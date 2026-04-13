import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

set_option exponentiation.threshold 1024

@[simp] abbrev UInt256.width := 256
@[simp] abbrev UInt256.size := 2^UInt256.width
abbrev UInt256 := BitVec UInt256.width

@[simp]
def evm_mulmod (x y m : UInt256) : UInt256 :=
  if h : m > 0 then
    let a := x.toNat; let b := y.toNat
    ⟨(a * b) % m.toNat, by have := Nat.mod_lt (a * b) h; omega⟩
  else 0

@[simp] def bool_to_uint : Bool → UInt256 | true => 1 | false => 0

def remco_upper256 (x y : UInt256) : UInt256 :=
  let mm := evm_mulmod x y (~~~0)
  let lower := x * y
  mm - lower - bool_to_uint (mm < lower)

def true_upper256 (x y : UInt256) : UInt256 :=
  ⟨(x.toNat * y.toNat) >>> UInt256.width,
    by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' x.isLt y.isLt)⟩

-- 2^256 ≡ 1 (mod 2^256 - 1)
private theorem mul_add_mod_pred (Q L : Nat) :
    (Q * 2^256 + L) % (2^256 - 1) = (Q + L) % (2^256 - 1) := by
  have h1 : 2^256 % (2^256 - 1) = 1 := by omega
  have h2 : Q * 2^256 % (2^256 - 1) = Q % (2^256 - 1) := by
    rw [Nat.mul_mod, h1, Nat.mul_one, Nat.mod_mod]
  rw [Nat.add_mod, h2, Nat.add_mod_mod, Nat.mod_add_mod]

private theorem remco_arith_helper (Q L M c p : Nat)
    (hp : p = Q * 2^256 + L)
    (hM : M = p % (2^256 - 1))
    (hc : (if M < L then 1 else 0) = c)
    (hQ : Q ≤ 2^256 - 2) (hL : L < 2^256) :
    L + (2^256 - c + (2^256 - L + M) % 2^256) % 2^256 * 2^256 = p := by

  have M_eq : M = (Q + L) % (2^256 - 1) := by rw [hM, hp, mul_add_mod_pred]

  rw [Nat.add_mod_mod]
  by_cases h : Q + L < 2^256 - 1
  · grind
  · have M_val : M = Q + L - (2^256 - 1) := by grind
    grind

private theorem bool_to_uint_toNat_eq (mm lower : UInt256) :
    (bool_to_uint (mm < lower)).toNat = if mm < lower then 1 else 0 := by
  by_cases h : mm < lower
  · simp only [bool_to_uint, h]; rfl
  · simp only [bool_to_uint, h]; rfl

private theorem width_eq : (2^UInt256.width : Nat) = 2^256 := rfl

theorem remco_equiv_naive (x y : UInt256) : remco_upper256 x y = true_upper256 x y := by
  have x_le : x.toNat ≤ 2^256 - 1 := by have := x.isLt; simp [UInt256.width] at *; omega
  have y_le : y.toNat ≤ 2^256 - 1 := by have := y.isLt; simp [UInt256.width] at *; omega
  have Q_le : x.toNat * y.toNat / 2^256 ≤ 2^256 - 2 := by
    have h_le := Nat.mul_le_mul x_le y_le
    omega
  let L := x.toNat * y.toNat % 2^256
  have lower_nat : (x * y).toNat = L := BitVec.toNat_mul x y
  have true_decomp : L + (true_upper256 x y).toNat * 2^256 = x.toNat * y.toNat := by
    unfold true_upper256 
    simp [Nat.shiftRight_eq_div_pow]
    have := Nat.mod_add_div (x.toNat * y.toNat) (2^256)
    omega
  have remco_decomp : x.toNat * y.toNat % 2^256 + (remco_upper256 x y).toNat * 2^256 = x.toNat * y.toNat := by
    unfold remco_upper256
    rw [BitVec.toNat_sub, BitVec.toNat_sub, lower_nat, bool_to_uint_toNat_eq, Nat.add_mod_mod]
    by_cases M_lt_L : evm_mulmod x y (~~~0) < x * y
    · -- M < L: carry = 1
      rw [if_pos M_lt_L]
      conv_lhs => rw [width_eq, width_eq, width_eq]


      /-

⊢ BitVec.toNat x * BitVec.toNat y % 2 ^ 256 +
    (2 ^ 256 - 1 + (2 ^ 256 - L + BitVec.toNat (evm_mulmod x y (~~~0)))) % 2 ^ 256 * 2 ^ 256 =
  BitVec.toNat x * BitVec.toNat y
      -/

      sorry



    · -- M ≥ L: carry = 0
      sorry
      /- rw [if_neg M_lt_L] -/
      /- conv_lhs => rw [width_eq, width_eq, width_eq] -/
      /- exact remco_arith_helper _ _ _ 0 _ -/
      /-   (by have := Nat.mod_add_div (x.toNat * y.toNat) (2^256); omega) -/
      /-   (by rfl) (if_neg M_lt_L) Q_le L_lt -/
  have key : (remco_upper256 x y).toNat * 2^256 = (true_upper256 x y).toNat * 2^256 := by omega
  exact BitVec.eq_of_toNat_eq (Nat.eq_of_mul_eq_mul_right (by omega) key)
