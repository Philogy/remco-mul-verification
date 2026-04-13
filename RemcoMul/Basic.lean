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
  let L := x.toNat * y.toNat % 2^256
  have L_lt : L < 2^256 := Nat.mod_lt _ (by omega)
  have lower_nat : (x * y).toNat = L := BitVec.toNat_mul x y
  have p_decomp : x.toNat * y.toNat = x.toNat * y.toNat / 2^256 * 2^256 + L := by
    grind [Nat.mod_add_div]
  have Q_le : x.toNat * y.toNat / 2^256 ≤ 2^256 - 2 := by
    have := Nat.mul_le_mul
      (show x.toNat ≤ 2^256-1 from by have := x.isLt; simp [UInt256.width] at *; omega)
      (show y.toNat ≤ 2^256-1 from by have := y.isLt; simp [UInt256.width] at *; omega)
    omega
  have mm_mod : (evm_mulmod x y (~~~0)).toNat = (x.toNat * y.toNat / 2^256 + L) % (2^256 - 1) := calc
    _ = (x.toNat * y.toNat) % (2^256 - 1) := by simp [evm_mulmod]
    _ = (x.toNat * y.toNat / 2^256 * 2^256 + L) % (2^256 - 1) := congrArg (· % (2^256 - 1)) p_decomp
    _ = (x.toNat * y.toNat / 2^256 + L) % (2^256 - 1) := mul_add_mod_pred _ _
  have remco_decomp : L + (remco_upper256 x y).toNat * 2^256 = x.toNat * y.toNat := by
    unfold remco_upper256
    simp only [BitVec.toNat_sub, lower_nat, bool_to_uint_toNat_eq]
    by_cases mm_lt : (evm_mulmod x y (~~~0)) < x * y
    · -- carry = 1: mm < lower, so Q+L ≥ 2^256-1 and mm.toNat = Q+L-(2^256-1)
      have hQ : x.toNat * y.toNat / 2^256 + L ≥ 2^256 - 1 := by
        have : (evm_mulmod x y (~~~0)).toNat < L :=
          lower_nat ▸ BitVec.lt_def.mp mm_lt
        omega
      have : (evm_mulmod x y (~~~0)).toNat = x.toNat * y.toNat / 2^256 + L - (2^256 - 1) := by omega
      grind
    · -- carry = 0: mm ≮ lower, so Q+L < 2^256-1 and mm.toNat = Q+L
      have hQ : x.toNat * y.toNat / 2^256 + L < 2^256 - 1 := by
        have : ¬(evm_mulmod x y (~~~0)).toNat < L :=
          lower_nat ▸ fun h => mm_lt (BitVec.lt_def.mpr h)
        omega
      grind
  have : L + (true_upper256 x y).toNat * 2^256 = x.toNat * y.toNat := by
    unfold true_upper256; simp [Nat.shiftRight_eq_div_pow]; grind [Nat.mod_add_div]
  exact BitVec.eq_of_toNat_eq (by omega)
