import Mathlib

set_option autoImplicit false

namespace Q4263

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev v2 (q : ℚ) : ℤ := padicValRat 2 q

/-- `VAtLeast k q` is the zero-aware assertion `v₂(q) ≥ k`; zero is treated
as having infinite valuation. -/
def VAtLeast (k : ℤ) (q : ℚ) : Prop := q = 0 ∨ k ≤ v2 q

namespace VAtLeast

lemma zero (k : ℤ) : VAtLeast k 0 := Or.inl rfl

lemma mono {j k : ℤ} {q : ℚ} (hjk : j ≤ k) (hq : VAtLeast k q) :
    VAtLeast j q := by
  rcases hq with rfl | hq
  · exact zero _
  · exact Or.inr (hjk.trans hq)

lemma neg {k : ℤ} {q : ℚ} (hq : VAtLeast k q) : VAtLeast k (-q) := by
  rcases hq with rfl | hq
  · simp [VAtLeast]
  · right
    simpa using hq

lemma add {k : ℤ} {q r : ℚ}
    (hq : VAtLeast k q) (hr : VAtLeast k r) : VAtLeast k (q + r) := by
  by_cases hsum : q + r = 0
  · exact Or.inl hsum
  right
  rcases hq with hq0 | hq
  · subst q
    simpa using hr.resolve_left (by simpa using hsum)
  rcases hr with hr0 | hr
  · subst r
    simpa using hq
  exact (le_min hq hr).trans (padicValRat.min_le_padicValRat_add hsum)

lemma sub {k : ℤ} {q r : ℚ}
    (hq : VAtLeast k q) (hr : VAtLeast k r) : VAtLeast k (q - r) := by
  simpa [sub_eq_add_neg] using hq.add hr.neg

lemma mul {j k : ℤ} {q r : ℚ}
    (hq : VAtLeast j q) (hr : VAtLeast k r) : VAtLeast (j + k) (q * r) := by
  rcases hq with hqzero | hq
  · subst q
    simp [VAtLeast]
  rcases hr with hrzero | hr
  · subst r
    simp [VAtLeast]
  by_cases hq0 : q = 0
  · simp [hq0, VAtLeast]
  by_cases hr0 : r = 0
  · simp [hr0, VAtLeast]
  right
  change j ≤ padicValRat 2 q at hq
  change k ≤ padicValRat 2 r at hr
  change j + k ≤ padicValRat 2 (q * r)
  rw [padicValRat.mul hq0 hr0]
  omega

lemma div_unit {k : ℤ} {q u : ℚ} (hq : VAtLeast k q)
    (hu0 : u ≠ 0) (hu : v2 u = 0) : VAtLeast k (q / u) := by
  rcases hq with rfl | hq
  · simp [VAtLeast]
  by_cases hq0 : q = 0
  · simp [hq0, VAtLeast]
  right
  change k ≤ padicValRat 2 q at hq
  change k ≤ padicValRat 2 (q / u)
  rw [padicValRat.div hq0 hu0]
  change k ≤ padicValRat 2 q - v2 u
  rw [hu, sub_zero]
  exact hq

lemma pow {k : ℤ} {q : ℚ} (hq : VAtLeast k q) (n : ℕ) :
    VAtLeast ((n : ℤ) * k) (q ^ n) := by
  by_cases hq0 : q = 0
  · subst q
    cases n <;> simp [VAtLeast]
  rcases hq with hqzero | hq
  · exact (hq0 hqzero).elim
  right
  change (n : ℤ) * k ≤ padicValRat 2 (q ^ n)
  rw [padicValRat.pow hq0]
  exact mul_le_mul_of_nonneg_left hq (Int.natCast_nonneg n)

lemma pow_two {k : ℤ} {q : ℚ} (hq : VAtLeast k q) :
    VAtLeast (2 * k) (q ^ 2) := by
  simpa using hq.pow 2

lemma two_mul {k : ℤ} {q : ℚ} (hq : VAtLeast k q) :
    VAtLeast (k + 1) (2 * q) := by
  have htwo : VAtLeast 1 (2 : ℚ) := by
    right
    exact le_of_eq (padicValRat.self (p := 2) (by norm_num)).symm
  have h := htwo.mul hq
  simpa only [add_comm] using h

lemma sum {ι : Type*} {s : Finset ι} {f : ι → ℚ} {k : ℤ}
    (h : ∀ i ∈ s, VAtLeast k (f i)) :
    VAtLeast k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [VAtLeast]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply add
      · exact h a (by simp)
      · apply ih
        intro i hi
        exact h i (by simp [hi])

end VAtLeast

lemma v2_two : v2 (2 : ℚ) = 1 := by
  exact padicValRat.self (by norm_num)

lemma v2_two_pow (n : ℕ) : v2 ((2 : ℚ) ^ n) = (n : ℤ) := by
  change padicValRat 2 ((2 : ℚ) ^ n) = (n : ℤ)
  rw [padicValRat.pow (by norm_num), padicValRat.self (by norm_num)]
  simp

/-- Exact wrapper around Mathlib's distinct-valuation sum lemma. -/
lemma v2_add_eq_min_of_ne {a b : ℚ}
    (hab : a + b ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hv : v2 a ≠ v2 b) :
    v2 (a + b) = min (v2 a) (v2 b) := by
  exact padicValRat.add_eq_min hab ha hb hv

/-- Exact wrapper for the common strict-order orientation. -/
lemma v2_add_eq_left_of_lt {a b : ℚ}
    (hab : a + b ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hv : v2 a < v2 b) :
    v2 (a + b) = v2 a := by
  exact padicValRat.add_eq_of_lt hab ha hb hv

/-- Every integral-coefficient monomial of degree at least two has valuation at
least `v₂(z)+1` when `v₂(z)≥1`. -/
lemma higher_monomial {c z : ℚ} {n : ℕ}
    (hc : VAtLeast 0 c) (hz : 1 ≤ v2 z) (hn : 2 ≤ n) :
    VAtLeast (v2 z + 1) (c * z ^ n) := by
  have hzA : VAtLeast (v2 z) z := Or.inr le_rfl
  have h := hc.mul (hzA.pow n)
  exact VAtLeast.mono (by omega) h

/-- Finite version of “all terms of the tail have degree at least two and
2-integral coefficients”. -/
lemma higher_tail {ι : Type*} {s : Finset ι}
    {c : ι → ℚ} {degree : ι → ℕ} {z : ℚ}
    (hz : 1 ≤ v2 z)
    (hc : ∀ i ∈ s, VAtLeast 0 (c i))
    (hdegree : ∀ i ∈ s, 2 ≤ degree i) :
    VAtLeast (v2 z + 1)
      (∑ i ∈ s, c i * z ^ degree i) := by
  apply VAtLeast.sum
  intro i hi
  exact higher_monomial (hc i hi) hz (hdegree i hi)

/-- Reusable formal-doubling estimate from a finite explicit tail. -/
theorem formal_double_of_finite_tail
    {ι : Type*} {s : Finset ι} {c : ι → ℚ} {degree : ι → ℕ}
    {z z₂ : ℚ}
    (hz : 1 ≤ v2 z)
    (hc : ∀ i ∈ s, VAtLeast 0 (c i))
    (hdegree : ∀ i ∈ s, 2 ≤ degree i)
    (hexp : z₂ = 2 * z + ∑ i ∈ s, c i * z ^ degree i) :
    VAtLeast (v2 z + 1) z₂ := by
  rw [hexp]
  have hzA : VAtLeast (v2 z) z := Or.inr le_rfl
  exact hzA.two_mul.add (higher_tail hz hc hdegree)

/-- The compact form used after factoring the higher terms as `z² R`. -/
theorem formal_double_of_expansion {z z₂ R : ℚ}
    (hz : 1 ≤ v2 z)
    (hR : VAtLeast 0 R)
    (hexp : z₂ = 2 * z + z ^ 2 * R) :
    VAtLeast (v2 z + 1) z₂ := by
  let a : ℤ := v2 z
  have ha : 1 ≤ a := hz
  have hzA : VAtLeast a z := Or.inr le_rfl
  have hlinear : VAtLeast (a + 1) (2 * z) := hzA.two_mul
  have hquadratic0 : VAtLeast (2 * a + 0) (z ^ 2 * R) :=
    hzA.pow_two.mul hR
  have hquadratic : VAtLeast (a + 1) (z ^ 2 * R) := by
    apply hquadratic0.mono
    omega
  rw [hexp]
  exact hlinear.add hquadratic

/-- Ordinary `padicValRat` inequality, valid when the doubled parameter is
nonzero. -/
theorem formal_double_of_expansion_ne_zero {z z₂ R : ℚ}
    (hz : 1 ≤ v2 z)
    (hR : VAtLeast 0 R)
    (hexp : z₂ = 2 * z + z ^ 2 * R)
    (hz₂ : z₂ ≠ 0) :
    v2 z + 1 ≤ v2 z₂ := by
  rcases formal_double_of_expansion hz hR hexp with hzero | h
  · exact (hz₂ hzero).elim
  · exact h

/-- Numerator/denominator form.  This is what one applies after `ring` has
rewritten an explicit duplication numerator as
`(2*z + z^2*R) * D`, with `D` a 2-adic unit. -/
theorem formal_double_num_den {z z₂ N D R : ℚ}
    (hz : 1 ≤ v2 z)
    (hR : VAtLeast 0 R)
    (hD0 : D ≠ 0)
    (hDunit : v2 D = 0)
    (hN : N = (2 * z + z ^ 2 * R) * D)
    (hz₂ : z₂ = N / D) :
    VAtLeast (v2 z + 1) z₂ := by
  have hbase : VAtLeast (v2 z + 1) (2 * z + z ^ 2 * R) :=
    formal_double_of_expansion hz hR rfl
  have hD : VAtLeast 0 D := by
    right
    rw [hDunit]
  have hNval : VAtLeast (v2 z + 1) N := by
    rw [hN]
    simpa using hbase.mul hD
  rw [hz₂]
  exact hNval.div_unit hD0 hDunit

/-- Same numerator/denominator theorem with the tail left as an explicit finite
sum; useful for a large expression such as `E21DoubleYNum`. -/
theorem formal_double_num_den_of_tail
    {ι : Type*} {s : Finset ι} {c : ι → ℚ} {degree : ι → ℕ}
    {z z₂ N D : ℚ}
    (hz : 1 ≤ v2 z)
    (hc : ∀ i ∈ s, VAtLeast 0 (c i))
    (hdegree : ∀ i ∈ s, 2 ≤ degree i)
    (hD0 : D ≠ 0)
    (hDunit : v2 D = 0)
    (hN : N = (2 * z + ∑ i ∈ s, c i * z ^ degree i) * D)
    (hz₂ : z₂ = N / D) :
    VAtLeast (v2 z + 1) z₂ := by
  have hbase : VAtLeast (v2 z + 1)
      (2 * z + ∑ i ∈ s, c i * z ^ degree i) :=
    formal_double_of_finite_tail hz hc hdegree rfl
  have hD : VAtLeast 0 D := by
    right
    rw [hDunit]
  have hNval : VAtLeast (v2 z + 1) N := by
    rw [hN]
    simpa using hbase.mul hD
  rw [hz₂]
  exact hNval.div_unit hD0 hDunit

section ReductionKernel

variable {G A : Type*} [AddCommGroup G] [AddCommGroup A]

/-- If the reduced group has exponent four, then `4P` lies in the kernel of
reduction. -/
theorem four_smul_mem_reduction_ker
    (red : G →+ A)
    (hexp : ∀ Q : A, (4 : ℕ) • Q = 0)
    (P : G) : (4 : ℕ) • P ∈ red.ker := by
  change red ((4 : ℕ) • P) = 0
  rw [map_nsmul, hexp]

/-- Predicate form, for a separately defined formal kernel. -/
theorem four_smul_mem_formal_kernel
    (red : G →+ A)
    (FormalKernel : G → Prop)
    (hexp : ∀ Q : A, (4 : ℕ) • Q = 0)
    (hkernel : ∀ Q : G, FormalKernel Q ↔ red Q = 0)
    (P : G) : FormalKernel ((4 : ℕ) • P) := by
  rw [hkernel, map_nsmul, hexp]

end ReductionKernel

open WeierstrassCurve

/-- A concrete good-reduction-at-two model used to verify the finite exponent
step by direct enumeration of `x,y : ZMod 2`. -/
def E02 : WeierstrassCurve.Affine (ZMod 2) where
  a₁ := 1
  a₂ := 1
  a₃ := 1
  a₄ := -5
  a₆ := 2

instance : E02.IsElliptic where
  isUnit := by
    rw [isUnit_iff_ne_zero]
    native_decide

theorem E02_exponent_four (Q : E02.Point) : (4 : ℕ) • Q = 0 := by
  rcases Q with (_ | ⟨x, y, h⟩)
  · simp
  fin_cases x <;> fin_cases y <;> native_decide

end Q4263
