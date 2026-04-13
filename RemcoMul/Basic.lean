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
private theorem mul_add_mod_pred (Q L : ℕ) :
    (Q * 2^256 + L) % (2^256 - 1) = (Q + L) % (2^256 - 1) := by
  have : 2^256 % (2^256 - 1) = 1 := by omega
  rw [Nat.add_mod, Nat.mul_mod, this, Nat.mul_one, Nat.mod_mod, Nat.add_mod_mod, Nat.mod_add_mod]

private theorem bool_to_uint_toNat_eq (mm lower : UInt256) :
    (bool_to_uint (mm < lower)).toNat = if mm < lower then 1 else 0 := by
  by_cases h : mm < lower <;> simp [bool_to_uint, h]

theorem remco_equiv_naive (x y : UInt256) : remco_upper256 x y = true_upper256 x y := by
  have x_le : x.toNat ≤ 2^256 - 1 := by have := x.isLt; simp [UInt256.width] at *; omega
  have y_le : y.toNat ≤ 2^256 - 1 := by have := y.isLt; simp [UInt256.width] at *; omega
  let L := x.toNat * y.toNat % 2^256
  have L_lt : L < 2^256 := Nat.mod_lt _ (by omega)
  have lower_nat : (x * y).toNat = L := BitVec.toNat_mul x y
  have p_decomp : x.toNat * y.toNat = x.toNat * y.toNat / 2^256 * 2^256 + L := by
    have := Nat.mod_add_div (x.toNat * y.toNat) (2^256); omega
  have Q_le : x.toNat * y.toNat / 2^256 ≤ 2^256 - 2 := by
    have := Nat.mul_le_mul x_le y_le; omega
  -- evm_mulmod x y (~~~0) = (Q + L) % (2^256 - 1)
  have mm_eq : (evm_mulmod x y (~~~0)).toNat = (x.toNat * y.toNat) % (2^256 - 1) := by simp [evm_mulmod]
  have mm_mod : (evm_mulmod x y (~~~0)).toNat = (x.toNat * y.toNat / 2^256 + L) % (2^256 - 1) := by
    conv_lhs => rw [mm_eq, p_decomp, mul_add_mod_pred]
  -- Both decompose the product: L + upper * 2^256 = x.toNat * y.toNat
  have true_decomp : L + (true_upper256 x y).toNat * 2^256 = x.toNat * y.toNat := by
    unfold true_upper256; simp [Nat.shiftRight_eq_div_pow]
    have := Nat.mod_add_div (x.toNat * y.toNat) (2^256); omega
  have remco_decomp : L + (remco_upper256 x y).toNat * 2^256 = x.toNat * y.toNat := by
    unfold remco_upper256
    have w : (2 ^ UInt256.width : ℕ) = 2^256 := rfl
    rw [BitVec.toNat_sub, BitVec.toNat_sub, lower_nat, bool_to_uint_toNat_eq,
        mm_mod, Nat.add_mod_mod, w, w, w]
    by_cases h : (evm_mulmod x y (~~~0)).toNat < L
    · -- carry = 1: M < L ↔ mm < lower
      have mm_lt : evm_mulmod x y (~~~0) < x * y :=
        BitVec.lt_def.mpr (by simpa [lower_nat] using h)
      simp only [if_pos mm_lt]
      have hQ : x.toNat * y.toNat / 2^256 + L ≥ 2^256 - 1 := by
        by_contra hq; push Not at hq; rw [mm_mod, Nat.mod_eq_of_lt hq] at h; omega
      have mm_val : (evm_mulmod x y (~~~0)).toNat =
          x.toNat * y.toNat / 2^256 + L - (2^256 - 1) := by
        rw [mm_mod, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      grind [Nat.mod_eq_of_lt, Nat.add_mod]
    · -- carry = 0: M ≥ L ↔ mm ≮ lower
      have mm_nlt : ¬(evm_mulmod x y (~~~0) < x * y) := by
        intro hlt; have := BitVec.lt_def.mp hlt; rw [lower_nat] at this; exact h this
      simp only [if_neg mm_nlt]
      have hQ : x.toNat * y.toNat / 2^256 + L < 2^256 - 1 := by
        by_contra hq; push Not at hq
        have mm_val : (evm_mulmod x y (~~~0)).toNat =
            x.toNat * y.toNat / 2^256 + L - (2^256 - 1) := by
          rw [mm_mod, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      have mm_val : (evm_mulmod x y (~~~0)).toNat =
          x.toNat * y.toNat / 2^256 + L := by rw [mm_mod, Nat.mod_eq_of_lt hQ]
      grind [Nat.mod_eq_of_lt, Nat.add_mod]
  -- Both sides equal x*y/2^256, hence equal
  have : (remco_upper256 x y).toNat < 2^256 := (remco_upper256 x y).isLt
  have : (true_upper256 x y).toNat < 2^256 := (true_upper256 x y).isLt
  exact BitVec.eq_of_toNat_eq (by omega)
