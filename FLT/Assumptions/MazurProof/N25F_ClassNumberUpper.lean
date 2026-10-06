import FLT.Assumptions.MazurProof.N25F_ClassNumberFromRR
import FLT.Assumptions.MazurProof.N25F_CanonicalSections
import FLT.Assumptions.MazurProof.N25F_Gonality
import FLT.Assumptions.MazurProof.N25F_SharpRiemann

/-!
# The class number of the N25 curve is at most `71`

Write `h = #Pic⁰ = #Pic⁴` and `ℓ(c)` for the section rank of a class.  Effective
divisors of degree four fibre over `Pic⁴` with fibres of size `2^ℓ(c) - 1`, so

  `Σ_{c ∈ Pic⁴} (2^ℓ(c) - 1) = A₄ = 101`.

Every degree-four class has `ℓ ≥ 1` by the sharp Riemann inequality
`deg D ≤ ℓ(D) + 3`.  For the boundary divisor `H = 3X + YZ + 2Z` of degree six
and each of the `A₂ = 15` effective divisors `E` of degree two, the class
`[H - E]` has `ℓ ≥ 2` (`N25F_CanonicalSections`).  These fifteen classes are
distinct: by gonality `ℓ(E) = 1`, so the degree-two effective fibres are
singletons.  Hence `101 ≥ h + 2 · 15`, i.e. `h ≤ 71`.  No Riemann–Roch
identity is used.
-/

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_ClassNumberUpper

open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_ProjectiveDivisorSplit N25F_RiemannRochSpace N25F_FullPicardDegree
open N25F_SectionClassFiber N25F_SectionPrincipalTransport N25F_PicardZeroFinite
open RationalPointsN25QuotientMiddleRiemannRoch CurveZetaEulerRecurrence
open N25F_ClassNumberFromRR N25F_CanonicalSections N25F_Gonality N25F_SharpRiemann

/-- The degree-`n` Picard fibre of the actual N25 curve. -/
abbrev Pic25 (n : ℤ) :=
  fullClosedPointGrading25Two.PicDegree fullProjectivePrincipalSubgroup25Two
    fullProjectivePrincipalSubgroup25Two_le_degree_ker n

/-- The class of an effective divisor of degree `n`. -/
abbrev effClass25 (n : ℕ) : fullClosedPointGrading25Two.EffDivOfDegree n → Pic25 n :=
  fullClosedPointGrading25Two.effectiveClass fullProjectivePrincipalSubgroup25Two
    fullProjectivePrincipalSubgroup25Two_le_degree_ker n

/-- `Pic⁴ ≃ Pic⁰` by translation by the boundary class `X`. -/
def picFourEquivZero : Pic25 4 ≃ Pic25 0 :=
  fullClosedPointGrading25Two.picDegreeEquivZero fullProjectivePrincipalSubgroup25Two
    fullProjectivePrincipalSubgroup25Two_le_degree_ker boundaryXClass25Two
    boundaryXClass25Two_degree 4

noncomputable instance : Fintype (Pic25 4) := Fintype.ofEquiv _ picFourEquivZero.symm

noncomputable instance : Fintype (Pic25 ((4 : ℕ) : ℤ)) := inferInstanceAs (Fintype (Pic25 4))

/-- The effective counts `A₂ = 15` and `A₄ = 101`. -/
theorem effective_counts :
    Nat.card (fullClosedPointGrading25Two.EffDivOfDegree 2) = 15 ∧
      Nat.card (fullClosedPointGrading25Two.EffDivOfDegree 4) = 101 := by
  have hEuler := CurveZetaMarkedDivisors.ClosedPointGrading.effectiveCount_satisfiesEulerRecurrence
    fullClosedPointGrading25Two
  have hN1 := (ClosedPointBridge25TwoLE4.ghostCount_one fullClosedPointBridge25TwoLE4).trans
    extensionPointCount25Two_one
  have hN2 := (ClosedPointBridge25TwoLE4.ghostCount_two fullClosedPointBridge25TwoLE4).trans
    extensionPointCount25Two_two
  have hN3 := (ClosedPointBridge25TwoLE4.ghostCount_three fullClosedPointBridge25TwoLE4).trans
    extensionPointCount25Two_three
  have hN4 := (ClosedPointBridge25TwoLE4.ghostCount_four fullClosedPointBridge25TwoLE4).trans
    extensionPointCount25Two_four
  exact effective_counts_two_and_four_of_n25_binary_data _ _ hEuler hN1 hN2 hN3 hN4

/-- Every degree-four class has a nonzero section. -/
theorem one_le_rank_four (c : Pic25 4) : 1 ≤ fullClassSectionRank25Two c.1 := by
  obtain ⟨c, hc⟩ := c
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective fullProjectivePrincipalSubgroup25Two c
  have hD : fullClosedPointGrading25Two.divisorDegree D = 4 := hc
  have h := degree_le_finrank_add_three D
  change 1 ≤ fullClassSectionRank25Two
    (fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two D)
  rw [fullClassSectionRank25Two_classOf]
  omega

/-- The signed divisor of an effective divisor of degree two. -/
abbrev effToDiv (E : fullClosedPointGrading25Two.EffDivOfDegree 2) : ProjectiveDivisor25Two :=
  fullClosedPointGrading25Two.effectiveToDivisor E.1

theorem effToDiv_nonneg (E : fullClosedPointGrading25Two.EffDivOfDegree 2) (A) :
    0 ≤ effToDiv E A := by
  simp [effToDiv]

theorem effToDiv_degree (E : fullClosedPointGrading25Two.EffDivOfDegree 2) :
    fullClosedPointGrading25Two.divisorDegree (effToDiv E) = 2 := by
  rw [effToDiv, fullClosedPointGrading25Two.divisorDegree_effectiveToDivisor, E.2]
  rfl

/-- By gonality, distinct effective divisors of degree two are inequivalent. -/
theorem effClass_two_injective : Function.Injective (effClass25 2) := by
  classical
  intro E E' h
  have hcard := effectiveClass_fiber_card 2 (effClass25 2 E)
  have hrank : fullClassSectionRank25Two (effClass25 2 E).1 = 1 := by
    change fullClassSectionRank25Two
      (fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two (effToDiv E)) = 1
    rw [fullClassSectionRank25Two_classOf]
    exact finrank_fullRiemannRochSpace25Two_of_degree_le_two _ (effToDiv_nonneg E)
      (by rw [effToDiv_degree])
  rw [hrank, linearSystemCard_two] at hcard
  norm_num at hcard
  obtain ⟨x, hx⟩ := Nat.card_eq_one_iff_exists.mp hcard
  have h1 := hx ⟨E, rfl⟩
  have h2 := hx ⟨E', h.symm⟩
  exact congrArg Subtype.val (h1.trans h2.symm)

/-- The class `[H]` of the degree-six boundary divisor. -/
def canonicalClass25 :
    fullClosedPointGrading25Two.DivisorClass fullProjectivePrincipalSubgroup25Two :=
  fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two canonicalDivisor25Two

theorem canonicalClass25_degree :
    fullClosedPointGrading25Two.classDegree fullProjectivePrincipalSubgroup25Two
      fullProjectivePrincipalSubgroup25Two_le_degree_ker canonicalClass25 = 6 := by
  rw [canonicalClass25, fullClosedPointGrading25Two.classDegree_classOf,
    canonicalDivisor25Two_degree]

/-- The residual class `[H - E]` of a degree-two effective divisor. -/
def residualClass (E : fullClosedPointGrading25Two.EffDivOfDegree 2) : Pic25 4 :=
  (fullClosedPointGrading25Two.residualDegreeFourTwo fullProjectivePrincipalSubgroup25Two
    fullProjectivePrincipalSubgroup25Two_le_degree_ker canonicalClass25
    canonicalClass25_degree).symm (effClass25 2 E)

theorem residualClass_injective : Function.Injective residualClass :=
  (Equiv.injective _).comp effClass_two_injective

theorem two_le_rank_residualClass (E : fullClosedPointGrading25Two.EffDivOfDegree 2) :
    2 ≤ fullClassSectionRank25Two (residualClass E).1 := by
  have he : (residualClass E).1 =
      fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two
        (canonicalDivisor25Two - effToDiv E) := by
    rw [map_sub]
    rfl
  rw [he, fullClassSectionRank25Two_classOf]
  exact two_le_finrank_canonical_sub _ (effToDiv_nonneg E) (effToDiv_degree E)

/-- The fibre sum `Σ_{c ∈ Pic⁴} (2^ℓ(c) - 1) = 101`. -/
theorem sum_fiber_eq :
    ∑ c : Pic25 4, (2 ^ fullClassSectionRank25Two c.1 - 1) = 101 := by
  classical
  letI : Fintype (fullClosedPointGrading25Two.EffDivOfDegree 4) := Fintype.ofFinite _
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv (effClass25 4))
  rw [Fintype.card_sigma] at h
  rw [← effective_counts.2, Nat.card_eq_fintype_card, ← h]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Nat.card_eq_fintype_card, effectiveClass_fiber_card 4 c, linearSystemCard_two]

/-- **The class number is at most `71`.** -/
theorem card_picDegreeZero_le_seventy_one :
    Fintype.card (Pic25 0) ≤ 71 := by
  classical
  letI : Fintype (fullClosedPointGrading25Two.EffDivOfDegree 2) := Fintype.ofFinite _
  let S : Finset (Pic25 4) := Finset.univ.image residualClass
  have hS : S.card = 15 := by
    rw [Finset.card_image_of_injective _ residualClass_injective, Finset.card_univ,
      ← Nat.card_eq_fintype_card, effective_counts.1]
  have hterm : ∀ c : Pic25 4,
      1 + (if c ∈ S then 2 else 0) ≤ 2 ^ fullClassSectionRank25Two c.1 - 1 := by
    intro c
    split_ifs with hc
    · obtain ⟨E, -, rfl⟩ := Finset.mem_image.mp hc
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (two_le_rank_residualClass E)
      omega
    · have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (one_le_rank_four c)
      omega
  have hsum := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hterm c
  rw [sum_fiber_eq, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, Finset.sum_const, Finset.card_univ, hS] at hsum
  simp only [smul_eq_mul, mul_one] at hsum
  rw [← Fintype.card_congr picFourEquivZero]
  omega

end MazurProof.N25F_ClassNumberUpper
