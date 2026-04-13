import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option exponentiation.threshold 1024

@[simp]
abbrev UInt256.width := 256
@[simp]
abbrev UInt256.size := 2^UInt256.width

abbrev UInt256 := BitVec UInt256.width

@[simp]
def evm_mulmod (x y m: UInt256): UInt256 :=
  if ne_zero: m > 0
  then
    let a := x.toNat
    let b := y.toNat
    ⟨
      (a * b) % m.toNat,
      by
        have := Nat.mod_lt (a * b) ne_zero
        omega
    ⟩
  else 0

@[simp]
def bool_to_uint: Bool → UInt256
  | true => 1
  | false => 0

def remco_upper256 (x y : UInt256): UInt256 :=
  let mm := evm_mulmod x y (~~~0)
  let lower := x * y
  mm - lower - bool_to_uint (mm < lower)

def true_upper256 (x y : UInt256): UInt256 :=
  ⟨
    (x.toNat * y.toNat) >>> UInt256.width,
    by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' x.isLt y.isLt)
  ⟩

-- Helper matching the exact form produced by BitVec.toNat_sub after decomposition
private theorem remco_arith_helper (Q L M c p : Nat)
    (hp : p = Q * 2^256 + L)
    (hM : M = p % (2^256 - 1))
    (hc : c = if M < L then 1 else 0)
    (hQ : Q ≤ 2^256 - 2)
    (hL : L < 2^256) :
    L + (2^256 - c + (2^256 - L + M) % 2^256) % 2^256 * 2^256 = p := by
  have M_eq : M = (Q + L) % (2^256 - 1) := by
    rw [hM, hp]
    have h1 : 2^256 % (2^256 - 1) = 1 := by omega
    have h2 : Q * 2^256 % (2^256 - 1) = Q % (2^256 - 1) := by
      rw [Nat.mul_mod, h1, Nat.mul_one, Nat.mod_mod]
    rw [Nat.add_mod _ _ (2^256 - 1), h2, Nat.add_mod_mod, Nat.mod_add_mod]
  by_cases h : Q + L < 2^256 - 1
  · -- M = Q + L, c = 0
    have M_val : M = Q + L := by rw [M_eq, Nat.mod_eq_of_lt h]
    have c_val : c = 0 := by rw [hc, M_val]; exact if_neg (by omega)
    rw [M_val, c_val, hp]
    -- L + (2^256 + (2^256 - L + Q + L) % 2^256) % 2^256 * 2^256 = Q*2^256 + L
    -- (2^256 - L + Q + L) = (2^256 + Q)
    -- Since Q < 2^256: (2^256 + Q) % 2^256 = Q
    -- So: L + (2^256 + Q) % 2^256 * 2^256 = Q*2^256 + L
    have h_q : Q < 2^256 := by omega
    have h_inner : (2^256 + Q) % 2^256 = Q := by omega
    rw [show (2^256 - L + (Q + L)) = 2^256 + Q by omega, h_inner]
    omega
  · -- M = Q + L - (2^256 - 1), c = 1
    have h_range : Q + L - (2^256 - 1) < 2^256 - 1 := by omega
    have M_val : M = Q + L - (2^256 - 1) := by
      rw [M_eq]
      have : Q + L = (Q + L - (2^256 - 1)) + (2^256 - 1) := by omega
      conv_lhs => rw [this, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt h_range
    have c_val : c = 1 := by rw [hc, M_val]; exact if_pos (by omega)
    rw [M_val, c_val, hp]
    -- L + (2^256 - 1 + (2^256 - L + Q + L - (2^256 - 1)) % 2^256) % 2^256 * 2^256 = Q*2^256 + L
    -- 2^256 - L + Q + L - (2^256 - 1) = Q + 1
    -- Since Q+1 < 2^256: (Q+1) % 2^256 = Q+1
    -- 2^256 - 1 + (Q+1) = 2^256 + Q
    -- (2^256 + Q) % 2^256 = Q
    -- So: L + Q * 2^256 = Q*2^256 + L
    have h_q : Q + 1 < 2^256 := by omega
    have h_inner : (Q + 1) % 2^256 = Q + 1 := by omega
    have h_outer : (2^256 + Q) % 2^256 = Q := by omega
    rw [show (2^256 - L + (Q + L - (2^256 - 1))) = Q + 1 by omega, h_inner,
        show 2^256 - 1 + (Q + 1) = 2^256 + Q by omega, h_outer]
    omega

private theorem bool_to_uint_toNat_eq (mm lower : UInt256) :
    (bool_to_uint (mm < lower)).toNat = if mm < lower then 1 else 0 := by
  by_cases h : mm < lower
  · simp only [bool_to_uint, h]; rfl
  · simp only [bool_to_uint, h]; rfl

private theorem width_eq : (2^UInt256.width : Nat) = 2^256 := rfl

theorem remco_equiv_naive (x y : UInt256) : remco_upper256 x y = true_upper256 x y := by
  -- Bounds
  have x_le : x.toNat ≤ 2^256 - 1 := by have := x.isLt; simp [UInt256.width] at *; omega
  have y_le : y.toNat ≤ 2^256 - 1 := by have := y.isLt; simp [UInt256.width] at *; omega
  have Q_le : x.toNat * y.toNat / 2^256 ≤ 2^256 - 2 := by
    have h_le := Nat.mul_le_mul x_le y_le
    have h_sq : ((2^256 - 1) * (2^256 - 1)) / 2^256 ≤ 2^256 - 2 := by
      have : (2^256 - 1) * (2^256 - 1) = 2^256 * (2^256 - 2) + 1 := by ring
      rw [this, Nat.mul_add_div (by omega)]; simp
    exact Nat.le_trans (Nat.div_le_div_right h_le) h_sq
  have L_lt : x.toNat * y.toNat % 2^256 < 2^256 := Nat.mod_lt _ (by omega)
  -- Key BitVec facts
  have mm_nat : (evm_mulmod x y (~~~0)).toNat = x.toNat * y.toNat % (2^256 - 1) := by simp [evm_mulmod]
  have lower_nat : (x * y).toNat = x.toNat * y.toNat % 2^256 := BitVec.toNat_mul x y
  -- true_upper256
  have true_toNat : (true_upper256 x y).toNat = x.toNat * y.toNat / 2^256 := by
    unfold true_upper256; simp [Nat.shiftRight_eq_div_pow]
  have true_decomp :
      x.toNat * y.toNat % 2^256 + (true_upper256 x y).toNat * 2^256 = x.toNat * y.toNat := by
    rw [true_toNat]; have := Nat.mod_add_div (x.toNat * y.toNat) (2^256); omega
  -- remco_upper256 decomposition
  have remco_decomp :
      x.toNat * y.toNat % 2^256 + (remco_upper256 x y).toNat * 2^256 = x.toNat * y.toNat := by
    by_cases M_lt_L : x.toNat * y.toNat % (2^256 - 1) < x.toNat * y.toNat % 2^256
    · -- Case: M < L (c = 1)
      have h_lt : (evm_mulmod x y (~~~0)).toNat < (x * y).toNat := by
        rw [mm_nat, lower_nat]; exact M_lt_L
      have h_lt' : evm_mulmod x y (~~~0) < x * y := h_lt
      unfold remco_upper256
      rw [BitVec.toNat_sub, BitVec.toNat_sub, mm_nat, lower_nat]
      rw [bool_to_uint_toNat_eq, if_pos h_lt']
      conv_lhs => rw [width_eq, width_eq, width_eq]
      apply remco_arith_helper (x.toNat * y.toNat / 2^256)
        (x.toNat * y.toNat % 2^256) (x.toNat * y.toNat % (2^256 - 1)) 1
        (x.toNat * y.toNat) (by have := Nat.mod_add_div (x.toNat * y.toNat) (2^256); omega)
        (by rfl) (by exact (if_pos M_lt_L).symm) Q_le L_lt
    · -- Case: M ≥ L (c = 0)
      have h_nlt : ¬(evm_mulmod x y (~~~0)).toNat < (x * y).toNat := by rw [mm_nat, lower_nat]; omega
      have h_nlt' : ¬evm_mulmod x y (~~~0) < x * y := h_nlt
      unfold remco_upper256
      rw [BitVec.toNat_sub, BitVec.toNat_sub, mm_nat, lower_nat]
      rw [bool_to_uint_toNat_eq, if_neg h_nlt']
      conv_lhs => rw [width_eq, width_eq, width_eq]
      apply remco_arith_helper (x.toNat * y.toNat / 2^256)
        (x.toNat * y.toNat % 2^256) (x.toNat * y.toNat % (2^256 - 1)) 0
        (x.toNat * y.toNat) (by have := Nat.mod_add_div (x.toNat * y.toNat) (2^256); omega)
        (by rfl) (by exact (if_neg (by omega)).symm) Q_le L_lt
  -- Both decompose the same way
  have toNat_eq : (remco_upper256 x y).toNat = (true_upper256 x y).toNat := by
    have : (remco_upper256 x y).toNat * 2^256 = (true_upper256 x y).toNat * 2^256 := by omega
    exact Nat.eq_of_mul_eq_mul_right (by omega) this
  exact BitVec.eq_of_toNat_eq toNat_eq
