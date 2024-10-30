import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Aesop

@[simp]
abbrev UInt256.width := 256
@[simp]
abbrev UInt256.size := 2^UInt256.width

abbrev m0 :=
  115792089237316195423570985008687907853269984665640564039457584007913129639936
abbrev m1 :=
  115792089237316195423570985008687907853269984665640564039457584007913129639935



lemma m0_gt_zero : 0 < m0 := by decide

theorem Nat.xgcd_add_three_add_two (n : ℕ) : (n + 3).xgcd (n + 2) = (1, -1) := by
  simp only [xgcd, xgcdAux, succ_eq_add_one, mod_succ, Int.ofNat_ediv, cast_add, cast_ofNat,
    cast_one, mul_one, zero_sub, mul_zero, sub_zero, add_mod_left, one_mod, lt_add_iff_pos_left,
    add_pos_iff, ofNat_pos, or_true, add_div_left, mul_neg, sub_neg_eq_add, neg_add_rev,
    Int.reduceNeg, zero_add, mod_one, Nat.div_one, xgcd_zero_left, Prod.mk.injEq, add_right_eq_self,
    _root_.mul_eq_zero, neg_eq_zero]
  constructor
  · right
    norm_cast
    rw [Nat.div_eq_zero_iff] <;> omega
  · norm_cast
    rw [Nat.div_eq_zero_iff] <;> omega

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

lemma succ_coprime (n : ℕ): Nat.Coprime (n + 1) n := by simp

def bool_to_nat: Bool → ℕ
  | true => 1
  | false => 0

/-- WOw docs?-/
lemma Int.sub_mod_eq_no_mod_lt {x y m : ℕ}:
  x < m → y < m →
  ((x : ℤ) - (y : ℤ)) % ↑m = ↑(m * bool_to_nat (x < y) + x - y)
  := by
  intro x_lt y_lt
  if y_gt_x: x < y
  then
    simp [bool_to_nat, y_gt_x]
    rw [← Int.add_mul_emod_self (b := 1), Int.one_mul, Int.add_comm, ← Int.add_sub_assoc]
    rw [(by omega : ((m : ℤ) + ↑x - ↑y) = ↑(m + x - y)), ← Int.natCast_mod]
    have lt_m : (m + x - y) < m := by omega
    rw [Nat.mod_eq_of_lt lt_m]
  else
    simp [bool_to_nat, y_gt_x]
    rw [(by omega : ((x : ℤ) - ↑y) = ↑(x - y)), ← Int.natCast_mod]
    have lt_m : (x - y) < m := by omega
    rw [Nat.mod_eq_of_lt lt_m]




@[simp]
def remco_full_mul (x y : UInt256): ℕ :=
  let hidden_full := x.toNat * y.toNat
  let x0 := hidden_full % m0
  let x1 := hidden_full % m1
  bool_to_nat (x0 > x1) * m0 * m1 + x0 + x1 * m0 - x0 * m0


lemma Nat.add_sub_eq_sub_sub { a b c : ℕ }:  b < c → a + b - c = a - (c - b) := by omega


lemma Nat.div_both_eq (c : ℕ) { a b : ℕ }: a = b → a / c = b / c := by
  intro h
  rw [h]


lemma Nat.sub_le_left_still_le (c : ℕ) { a b: ℕ } : a ≤ b → a - c ≤ b := by
  intro h
  omega

theorem Nat.add_self_sub_mod { a b m : ℕ } : b ≤ a → (m + a - b) % m = (a - b) % m := by
  intro b_le_a
  rw [Nat.add_sub_assoc b_le_a m]
  rw [Nat.add_mod]
  simp


lemma Nat.lt_mul_sub_one_iff_lt (a b m : ℕ) : b < m → ((m * a < (m - 1) * b) ↔ (a < b)) := by
  intro m_gt_b
  constructor
  {
    intro top_cmp
    rw [Nat.sub_mul, one_mul] at top_cmp
    have weird_sub_lt_no_sub : m * b - b ≤ m * b := Nat.sub_le_left_still_le b (by simp)
    have ma_lt_mb : m * a < m * b := by omega
    exact Nat.lt_of_mul_lt_mul_left ma_lt_mb
  }
  {
    intro top_cmp
    rw [Nat.sub_mul, one_mul]
    have ma_lt_mb : m * a < m * b := (Nat.mul_lt_mul_left (by omega)).mpr top_cmp

    apply Nat.sub_lt_sub_right (c := m * a) (by omega) at ma_lt_mb
    rw [Nat.sub_self, ← Nat.mul_sub] at ma_lt_mb
    have b_minus_a_ne_zero : 0 <  (b - a) := by omega
    have b_minus_a_le_one : 1 ≤ (b - a) := by omega
    have prod_sub_b_ne_zero : m * (b - a) - b ≠ 0 := Nat.sub_ne_zero_of_lt (by {
      have b_lt_m_mul_one : m * 1 ≤ m * (b - a) := Nat.mul_le_mul_left m b_minus_a_le_one
      omega
    })
    apply Nat.ne_zero_iff_zero_lt.mp at prod_sub_b_ne_zero
    rw [Nat.mul_sub] at prod_sub_b_ne_zero
    omega
  }


theorem Nat.gcd_self_add_one (n : ℕ) : Nat.gcd (n + 1) n = 1 := by simp

theorem remco_equiv_naive(x y : UInt256) : remco_upper256 x y = true_upper256 x y := by
  let z := x.toNat * y.toNat
  let upper := z >>> UInt256.width
  let x0 := z % m0
  let x1 := z % m1

  have x0_lt_m0 : x0 < m0 := by
    simp [x0]
    exact Nat.mod_lt z (by decide)
  have x1_lt_m1 : x1 < m1 := by
    simp [x1]
    exact Nat.mod_lt z (by decide)

  have z_le : z ≤ (m1 * m1) := Nat.mul_le_mul (Nat.le_of_lt_succ x.isLt) (Nat.le_of_lt_succ y.isLt)
  have z_lt : z < (m0 * m1) := Nat.lt_of_le_of_lt z_le (by decide)
  have z_eq_no_mod : z = z % (m0 * m1) := Eq.symm <| Nat.mod_eq_of_lt z_lt
  simp [m0, m1] at z_eq_no_mod

  have comp_z_chinese :=
    Nat.chineseRemainder_modEq_unique (succ_coprime m1) (a := x0) (b := x1) (z := z)
    ( by simp [Nat.ModEq, x0, m0])
    ( by simp [Nat.ModEq, x1, m0, m1])


  simp only [Nat.chineseRemainder, Nat.chineseRemainder', Nat.ModEq] at comp_z_chinese
  have m0_xgcd : Nat.xgcd (m1 + 1) m1 = (1, -1) := by
    let m1_sub_2 := m1 - 2
    rw [(by decide : m1 = m1_sub_2 + 2), Nat.add_assoc, (by simp : 2 + 1 = 3)]
    exact Nat.xgcd_add_three_add_two m1_sub_2
  simp only [m0_xgcd, Nat.lcm, Nat.gcd_self_add_one m1] at comp_z_chinese
  simp at comp_z_chinese

  apply Eq.trans z_eq_no_mod at comp_z_chinese

  rw [← Int.sub_eq_add_neg] at comp_z_chinese
  rw [
    (by simp :
((115792089237316195423570985008687907853269984665640564039457584007913129639936 * (x1: ℤ) -
          115792089237316195423570985008687907853269984665640564039457584007913129639935 * ↑x0) %
        13407807929942597099574024998205846127479365820592393377723561443721764030073431184712636981971479856705023170278632780869088242247907112362425735876444160).toNat %
    ((m1 + 1) * m1)
    = (((↑(m0 * x1) - ↑(m1 * x0)) : ℤ) % ↑(m0 * m1)).toNat % (m0 * m1)

    )
  ] at comp_z_chinese

  have left_lt_m01 : m0 * x1 < m0 * m1 := (Nat.mul_lt_mul_left (by decide)).mpr x1_lt_m1
  have right_lt_m01 : m1 * x0 < m0 * m1 := (Nat.mul_lt_mul_left (by decide)).mpr x0_lt_m0

  rw [
    Int.sub_mod_eq_no_mod_lt
      left_lt_m01
      right_lt_m01
  ] at comp_z_chinese

  rw [(by omega : ∀ x: ℕ, (x : ℤ).toNat = x)] at comp_z_chinese

  have z_comp_lt_m01 : m0 * m1 * bool_to_nat ((m1 * x0 > m0 * x1)) + m0 * x1 - m1 * x0 < m0 * m1 := by
    if sides_lt:  m0 * x1 < m1 * x0
    then
      simp [sides_lt, bool_to_nat]
      rw [Nat.add_sub_eq_sub_sub sides_lt]
      have d_gt_zero : m1 * x0 - m0 * x1 > 0 := by omega
      have d_le_m01 : m1 * x0 - m0 * x1 ≤  m0 * m1 := by omega
      apply Nat.sub_lt_self d_gt_zero d_le_m01
    else
      simp [sides_lt, bool_to_nat]
      omega

  apply Nat.div_both_eq m0 at comp_z_chinese
  rw [(by decide : m0 = 2^UInt256.width)] at comp_z_chinese
  rw [← Nat.shiftRight_eq_div_pow] at comp_z_chinese
  rw [← (by decide : m0 = 2^UInt256.width)] at comp_z_chinese
  simp only [UInt256.width] at comp_z_chinese

  rw [Nat.mod_eq_of_lt z_comp_lt_m01, (by simp : m1 = m0 - 1)] at comp_z_chinese
  simp_rw [
    eq_iff_iff.mpr gt_iff_lt,
    eq_iff_iff.mpr (Nat.lt_mul_sub_one_iff_lt x1 x0 m0 x0_lt_m0)
  ] at comp_z_chinese

  have true_eq_upper : (true_upper256 x y) = ↑upper := by
    simp [upper, true_upper256]
    apply BitVec.toNat_eq.mpr
    rw [(by simp : z = x.toNat * y.toNat)]
    simp
    rw [Nat.shiftRight_eq_div_pow]
    simp
    have mul_lt_256 := (true_upper256 x y).isLt
    simp [true_upper256, Nat.shiftRight_eq_div_pow] at mul_lt_256
    rw [Nat.mod_eq_of_lt mul_lt_256]
  rw [true_eq_upper]
  simp [upper]
  rw [comp_z_chinese]
  simp [BitVec.ofNat, Fin.ofNat']
  simp [remco_upper256]
  simp [Fin.sub_def, Fin.mul_def]


  simp_rw [
    (by decide : 115792089237316195423570985008687907853269984665640564039457584007913129639936 = m0),
    (by decide : 115792089237316195423570985008687907853269984665640564039457584007913129639935 = m1),
  ]
  rw [
    ← (by simp [z] : z = x.toNat * y.toNat ),
    ← (by simp [x0, z] : x0 = z % m0 ),
    ← (by simp [x1, z] : x1 = z % m1 )
  ]

  if x1_lt_x0 : x1 < x0
  then
    simp [x1_lt_x0, bool_to_nat]
    simp_rw [
      (by decide : 115792089237316195423570985008687907853269984665640564039457584007913129639935 = m0 - 1)
    ]
    simp only [Nat.mul_sub, Nat.mul_sub_div]
    rw [← Nat.mul_sub, ← Nat.mul_add]

    have x0_ne_zero : x0 ≠ 0 := by omega
    have m1_mul_x0_ne_zero : (m0 - 1) * x0 ≠ 0 := Nat.mul_ne_zero (by decide) x0_ne_zero
    let m1_mul_x0_sub_one := (m0 - 1) * x0 - 1
    have m1_mul_x0_is_succ : (m0 - 1) * x0 = m1_mul_x0_sub_one + 1 := by omega
    rw [m1_mul_x0_is_succ]
    rw [Nat.mul_sub_div m1_mul_x0_sub_one m0 (m0 - 1 + x1) (by {
      simp only [m1_mul_x0_sub_one]
      have add_lt_add_one (a b : ℕ) : a < b ↔ a + 1 < b + 1 := by omega
      rw [eq_iff_iff.mpr <| add_lt_add_one ((m0 - 1) * x0 - 1) (m0 * (m0 - 1 + x1))]
      rw [Nat.sub_one_add_one m1_mul_x0_ne_zero]
      have m1x0_lt_max_prod : (m0 - 1) * x0 < (m0 - 1) * m0 := by
        apply (Nat.mul_lt_mul_left (a := (m0 - 1)) (by decide)).mpr
        exact x0_lt_m0
      have m1m0_lt_more : m0 * (m0 - 1) < m0 * ((m0 - 1) + x1) + 1 := by
        rw [Nat.mul_add, Nat.add_assoc, Nat.add_comm (m0 * x1) 1, ← Nat.add_assoc]
        exact Nat.lt_add_right (m0 * x1) (Nat.lt_add_one <| m0 * (m0 - 1))
      exact Nat.lt_trans m1x0_lt_max_prod m1m0_lt_more
    })]
    simp only [m1_mul_x0_sub_one]
    rw [Nat.sub_mul, Nat.one_mul]
    rw [Nat.sub_sub]
    rw [Nat.mul_sub_div x0 m0 x0 (by {
      exact (Nat.lt_mul_iff_one_lt_left (a := m0) (b := x0) (by omega)).mpr (by decide)
    })]
    have x0_div_m0_eq_zero : x0 / m0 = 0 := (Nat.div_eq_zero_iff m0_gt_zero).mpr x0_lt_m0
    rw [x0_div_m0_eq_zero]
    simp only [Nat.zero_add]
    rw [Nat.sub_one_add_one x0_ne_zero]
    rw [← Nat.sub_add_comm (by omega : x0 ≤ m0)]

    rw [(by omega : m0 + x1 - x0 = m0 - (x0 - x1) )]

    have d_le_m0 : (x0 - x1) ≤ m0 := by omega
    rw [← Nat.add_sub_assoc d_le_m0]

    rw [← Nat.sub_add_comm (by decide : 1 ≤ m0)]
    rw [Nat.sub_sub]

    have one_plus_d_le_m0 : (1 + (x0 - x1)) ≤ m0 := by
      rw [eq_iff_iff.mpr <| Nat.one_add_le_iff (m := x0 - x1) (n := m0)]
      have d_le_x0 : x0 - x1 ≤ x0 := by simp
      exact Nat.lt_of_le_of_lt d_le_x0 x0_lt_m0
    rw [Nat.add_self_sub_mod one_plus_d_le_m0]
    rw [( by omega : ∀ (a b c : ℕ), a - (b + c) = a - b - c )]
    rw [(by omega : (m0 - 1 - (x0 - x1)) =  (m0 - 1 + x1 - x0) )]
  else
    simp [x1_lt_x0, bool_to_nat]
    simp_rw [
      (by decide : 115792089237316195423570985008687907853269984665640564039457584007913129639935 = m0 - 1)
    ]
    simp only [Nat.sub_mul, Nat.one_mul]
    simp at x1_lt_x0
    rename x0 ≤ x1 => x0_le_x1
    match x0_val: x0 with
    | 0 => {
      simp
    }
    | x0_neg_one+1 => {
      simp at x0_val
      rw [← x0_val]
      rw [← x0_val] at x0_lt_m0
      rw [← x0_val] at x0_le_x1
      /- rw [Nat.exists_eq_succ_of_ne_zero] -/
      have x0_ne_zero : x0 ≠ 0 := by omega
      let weird_prod_sub_one := m0 * x0 - x0 - 1
      have weird_prod_eq_succ : m0 * x0 - x0 = weird_prod_sub_one + 1 := by
        simp [weird_prod_sub_one]
        have weird_prod_ne_zero : m0 * x0 - x0 ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr (by {
          rw [← eq_iff_iff.mpr (Nat.add_lt_add_iff_right (k := x0))]
          simp
          exact (Nat.lt_mul_iff_one_lt_left (a := m0) (b := x0) (by omega)).mpr (by decide)
        })
        rw [Nat.sub_one_add_one weird_prod_ne_zero]
      rw [weird_prod_eq_succ]
      rw [Nat.mul_sub_div weird_prod_sub_one m0 x1 (by {
        simp [weird_prod_sub_one]
        have m0_mul_x0_le_x1 : m0 * x0 ≤ m0 * x1 := Nat.mul_le_mul (by omega) (x0_le_x1)
        have d_lt_prod : m0 * x0 - x0 - 1 < m0 * x0 := by {
          rw [Nat.sub_sub]
          have m0_mul_x0_ne_zero : 0 < m0 * x0 := Nat.ne_zero_iff_zero_lt.mp <| Nat.mul_ne_zero (by decide) x0_ne_zero
          have x0_add_one_ne_zero : 0 < (x0 + 1) := by simp
          exact Nat.sub_lt m0_mul_x0_ne_zero (by simp)
        }
        omega
      })]
      simp only [weird_prod_sub_one]
      rw [Nat.sub_sub]
      rw [Nat.mul_sub_div x0 m0 x0 (by {
        exact (Nat.lt_mul_iff_one_lt_left (a := m0) (b := x0) (by omega)).mpr (by decide)
      })]
      have x0_div_m0_eq_zero : x0 / m0 = 0 := (Nat.div_eq_zero_iff m0_gt_zero).mpr x0_lt_m0
      rw [x0_div_m0_eq_zero, Nat.zero_add, Nat.sub_one_add_one x0_ne_zero]
      rw [← Nat.sub_add_comm (Nat.le_of_lt x0_lt_m0)]
      exact Nat.add_self_sub_mod x0_le_x1
    }

