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

#check Nat.mod_eq_of_lt

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


-- (m0 * x1 < (m0 - 1) * x0)

#check Nat.sub_lt_sub_right
#check Nat.mul_ne_zero_iff
#check Nat.sub_ne_zero_iff_lt
#check Nat.not_eq_zero_of_lt

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

  simp [Nat.chineseRemainder, Nat.chineseRemainder', Nat.lcm, Nat.ModEq, Nat.xgcd, Nat.xgcdAux] at comp_z_chinese
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


  /- have can_cmp_x0_x1_dir : (x0 < x1) = (m1 * x0 < m0 * x1) := eq_iff_iff.mpr (by {
    rw [(by simp : m1 = m0 - 1), mul_comm, Nat.mul_sub, mul_one]

    rw [mul_comm]

    constructor
    {
      intro h
      have muled_lt : m0 * x0 < m0 * x1 := (Nat.mul_lt_mul_left (by decide: 0 < m0)).mpr h
      exact Nat.sub_lt_left_still_lt x0 muled_lt
    }
    {
      intro h
      have ignore_small (a b m d : ℕ) : d < m → m * a - d < m * b → m * a < m * b := by
        intro d_lt_m
        intro inner_lt



        

    }
  }) -/

    


  rw [Nat.mod_eq_of_lt z_comp_lt_m01, (by simp : m1 = m0 - 1)] at comp_z_chinese
  simp_rw [
    eq_iff_iff.mpr gt_iff_lt,
    eq_iff_iff.mpr (Nat.lt_mul_sub_one_iff_lt x1 x0 m0 x0_lt_m0)
  ] at comp_z_chinese

  apply Nat.div_both_eq m0 at comp_z_chinese
  have true_eq_upper : (true_upper256 x y).toNat = upper := by simp [true_upper256]
  apply BitVec.toNat_eq.mpr
  rw [true_eq_upper]
  simp [upper]
  rw [(by decide : m0 = 2^UInt256.width)] at comp_z_chinese
  rw [← Nat.shiftRight_eq_div_pow] at comp_z_chinese
  rw [← (by decide : m0 = 2^UInt256.width)] at comp_z_chinese
  simp only [UInt256.width] at comp_z_chinese

  simp [remco_upper256]
  simp [Fin.lt_def, Fin.val_mul]

  have x0_eq_bitvec_mul : BitVec.toNat x * BitVec.toNat y % m0 = x0 := by simp
  have x1_eq_bitvec_mul : BitVec.toNat x * BitVec.toNat y % m1 = x1 := by simp
  have fin_mul_eq_x0 : x.toFin * y.toFin = ⟨x0, x0_lt_m0⟩:= by simp [x0, Fin.mul_def]
  simp_rw [x0_eq_bitvec_mul, x1_eq_bitvec_mul, fin_mul_eq_x0]
  rw [comp_z_chinese]

  simp [bool_to_nat]
  /- simp_rw [
    /- (by decide : 115792089237316195423570985008687907853269984665640564039457584007913129639936 = m0), -/
    (by decide : 115792089237316195423570985008687907853269984665640564039457584007913129639935 = m1)
  ] -/
  simp [Fin.sub_def]

  let c := match decide (x1 < x0) with | true => 1 | false => 0

  rw [
    ← (by simp : c = match decide (x1 < x0) with | true => 1 | false => 0 ),
    ← (by {
      simp [c]
      if x1_lt_x0: x1 < x0
      then simp [x1_lt_x0]
      else simp [x1_lt_x0]

    } : c = BitVec.toNat (match decide (x1 < x0) with | true => 1#256 | false => 0#256))
  ]

  rw [
    (by decide : 115792089237316195423570985008687907853269984665640564039457584007913129639936 = m0),
    (by decide : 115792089237316195423570985008687907853269984665640564039457584007913129639935 = m1),
  ]


  have bracket_out_m0 := Nat.mul_add m0 (m1 * c) x1
  rw [← Nat.mul_assoc] at bracket_out_m0
  rw [← bracket_out_m0]
  simp [c]

  if x1_lt_x0: x1 < x0
  then
    simp [x1_lt_x0]
    have x0_ne_zero : x0 ≠ 0 := by omega
    let x0_neg_one := x0 - 1
    have x0_eq_succ : x0 = x0_neg_one + 1 := by
      simp [x0_neg_one]
      rw [Nat.sub_one_add_one (a := x0) x0_ne_zero]
    let m1_mul_x0_neg_one := m1 * x0 - 1
    have m1_mul_x0_ne_zero : m1 * x0 ≠ 0 := Nat.mul_ne_zero (by decide) x0_ne_zero
    have m1_mul_x0_eq_succ : m1 * x0 = m1_mul_x0_neg_one + 1 := by
      simp [m1_mul_x0_neg_one]
      rw [Nat.sub_one_add_one (a := m1 * x0) m1_mul_x0_ne_zero]
    rw [m1_mul_x0_eq_succ]


    rw [Nat.mul_sub_div m1_mul_x0_neg_one m0 (m1 + x1) (by {
      simp [m1_mul_x0_neg_one]
      have add_lt_add_one (a b : ℕ) : a < b ↔ a + 1 < b + 1 := by omega
      rw [eq_iff_iff.mpr <| add_lt_add_one (m1 * x0 - 1) (m0 * (m1 + x1))]
      rw [Nat.sub_one_add_one m1_mul_x0_ne_zero]
      have m1x0_lt_max_prod : m1 * x0 < m1 * m0 := by
        apply (Nat.mul_lt_mul_left (a := m1) (by decide)).mpr
        exact x0_lt_m0
      have m1m0_lt_more : m0 * m1 < m0 * (m1 + x1) + 1 := by
        rw [Nat.mul_add, Nat.add_assoc, Nat.add_comm (m0 * x1) 1, ← Nat.add_assoc]
        exact Nat.lt_add_right (m0 * x1) (Nat.lt_add_one <| m0 * m1)
      omega
    })]
    simp [m1_mul_x0_neg_one]

    rw [
      (by decide : 115792089237316195423570985008687907853269984665640564039457584007913129639935 = m1),
      (by decide : m1 = m0 - 1)
    ]
    rw [Nat.mul_sub_right_distrib, one_mul]






  else
    sorry




  

  /- have x0_eq_succ : x0 = x0_neg_one + 1 := by
    simp [x0_neg_one]
    rw [Nat.sub_one_add_one (a := x0) x0_ne_zero]
  let m1_mul_x0_neg_one := m1 * x0 - 1
  have m1_mul_x0_ne_zero : m1 * x0 ≠ 0 := Nat.mul_ne_zero (by decide) x0_ne_zero
  have m1_mul_x0_eq_succ : m1 * x0 = m1_mul_x0_neg_one + 1 := by
    simp [m1_mul_x0_neg_one]
    rw [Nat.sub_one_add_one (a := m1 * x0) m1_mul_x0_ne_zero]
  rw [m1_mul_x0_eq_succ]

  rw [Nat.mul_sub_div m1_mul_x0_neg_one m0 (m1 + x1) (by {
    simp [m1_mul_x0_neg_one]
    have add_lt_add_one (a b : ℕ) : a < b ↔ a + 1 < b + 1 := by omega
    rw [eq_iff_iff.mpr <| add_lt_add_one (m1 * x0 - 1) (m0 * (m1 + x1))]
    rw [Nat.sub_one_add_one m1_mul_x0_ne_zero]
    have m1x0_lt_max_prod : m1 * x0 < m1 * m0 := by
      apply (Nat.mul_lt_mul_left (a := m1) (by decide)).mpr
      exact x0_lt_m0
    have m1m0_lt_more : m0 * m1 < m0 * (m1 + x1) + 1 := by
      rw [Nat.mul_add, Nat.add_assoc, Nat.add_comm (m0 * x1) 1, ← Nat.add_assoc]
      exact Nat.lt_add_right (m0 * x1) (Nat.lt_add_one <| m0 * m1)
    omega
  })]
  simp [m1_mul_x0_neg_one]
 -/
