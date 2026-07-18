import Mathlib

set_option autoImplicit false

namespace N15FormalBackup

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev v2 (q : ℚ) : ℤ := padicValRat 2 q

/-- A finite-valued encoding of `v₂(q) ≥ k` in which `q = 0` is treated as
having infinite valuation. -/
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

lemma pow_two {k : ℤ} {q : ℚ} (hq : VAtLeast k q) :
    VAtLeast (2 * k) (q ^ 2) := by
  rcases hq with rfl | hq
  · simp [VAtLeast]
  by_cases hq0 : q = 0
  · simp [hq0, VAtLeast]
  right
  change k ≤ padicValRat 2 q at hq
  change 2 * k ≤ padicValRat 2 (q ^ 2)
  rw [padicValRat.pow hq0]
  omega

lemma two_mul {k : ℤ} {q : ℚ} (hq : VAtLeast k q) :
    VAtLeast (k + 1) (2 * q) := by
  have htwo : VAtLeast 1 (2 : ℚ) := by
    right
    exact le_of_eq (padicValRat.self (p := 2) (by norm_num)).symm
  have h := htwo.mul hq
  simpa only [add_comm] using h

end VAtLeast

/-- The exact valuation estimate one uses after writing the formal doubling
law in the form `[2](t) = 2t + t² R(t)`, with integral remainder.  The output
is zero-aware, so it remains true when `2P = O`. -/
theorem n15_v2_formal_double_of_expansion {t t₂ R : ℚ}
    (ht : 1 ≤ v2 t)
    (hR : VAtLeast 0 R)
    (hexp : t₂ = 2 * t + t ^ 2 * R) :
    VAtLeast (v2 t + 1) t₂ := by
  let a : ℤ := v2 t
  have ha : 1 ≤ a := ht
  have htA : VAtLeast a t := Or.inr le_rfl
  have hlinear : VAtLeast (a + 1) (2 * t) := htA.two_mul
  have hquadratic0 : VAtLeast (2 * a + 0) (t ^ 2 * R) :=
    htA.pow_two.mul hR
  have hquadratic : VAtLeast (a + 1) (t ^ 2 * R) := by
    apply hquadratic0.mono
    omega
  rw [hexp]
  exact hlinear.add hquadratic

section AbstractSeparatedness

variable {G : Type*} [AddCommGroup G]

/-- Membership in every image of multiplication by a power of two. -/
def InfinitelyTwoDivisible (x : G) : Prop :=
  ∀ n : ℕ, ∃ y : G, x = (2 ^ n : ℕ) • y

lemma iterate_level
    (L : ℕ → G → Prop)
    (hraise : ∀ n P, L n P → L (n + 1) ((2 : ℕ) • P))
    {P : G} (hP : L 1 P) :
    ∀ n : ℕ, L (n + 1) ((2 ^ n : ℕ) • P) := by
  intro n
  induction n with
  | zero => simpa using hP
  | succ n ih =>
      have h := hraise (n + 1) ((2 ^ n : ℕ) • P) ih
      simpa [pow_succ', smul_smul, Nat.mul_assoc] using h

/-- Abstract form of the formal-kernel separatedness argument.  `hfinite`
encodes that a fixed nonzero rational parameter has finite 2-adic valuation. -/
theorem n15_no_infinitely_two_divisible
    (L : ℕ → G → Prop)
    (hfour : ∀ Q : G, L 1 ((4 : ℕ) • Q))
    (hraise : ∀ n P, L n P → L (n + 1) ((2 : ℕ) • P))
    (hfinite : ∀ P : G, P ≠ 0 → ∃ B : ℕ, ¬ L (B + 1) P) :
    ∀ P : G, InfinitelyTwoDivisible P → P = 0 := by
  intro P hdiv
  by_contra hP0
  obtain ⟨B, hB⟩ := hfinite P hP0
  obtain ⟨Q, hQ⟩ := hdiv (B + 2)
  apply hB
  have hlev := iterate_level L hraise (n := B) (hfour Q)
  rw [hQ]
  simpa [smul_smul, pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlev

end AbstractSeparatedness

end N15FormalBackup
