import FLT.Assumptions.MazurProof.N25F_HighDegreeEffective
import FLT.Assumptions.MazurProof.N25F_ProjectiveDivisorDegree

/-!
# Finiteness of the degree-zero Picard group of the actual N25 curve over F2

The divisor group is the full closed-point divisor group
`fullClosedPointGrading25Two.Divisor` and the principal subgroup is the image
of the actual projective principal-divisor map
(`fullProjectivePrincipalSubgroup25Two`).  No truncation of closed points and
no Riemann--Roch premise is used.

Proof architecture.

* Put `n = 4B + 1`, where `B = wPolynomialBasisPoleBound25Two` is the existing
  divisor-independent pole bound.  By
  `exists_effective_representative_of_degree_gt_four_basis_bound`, every class
  of degree `n` is the class of an effective divisor of degree `n`, so the map
  `EffDivOfDegree n → Pic^n` is surjective.
* Effective divisors of a fixed degree form a finite type
  (`effDivOfDegreeFinite`), hence `Pic^n` is finite.
* The tagged boundary atom `X` is a closed point of degree one; its class is a
  degree-one class, and translation by `-n` times it identifies `Pic^n` with
  `Pic^0` (`picDegreeEquivZero`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_PicardZeroFinite

open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open N25F_ProjectiveDivisorDegree
open N25F_WBasisPoleBound N25F_FullPicardDegree N25F_HighDegreeEffective

/-- The fixed degree above the effectivity threshold used for the finiteness
argument: one more than four times the existing pole bound. -/
def picardFinitenessDegree25Two : ℕ := 4 * wPolynomialBasisPoleBound25Two + 1

/-- Every class of degree `4B + 1` in the actual full Picard group is the class
of an effective divisor of that degree. -/
theorem effectiveClass_surjective_picardFinitenessDegree :
    Function.Surjective
      (fullClosedPointGrading25Two.effectiveClass fullProjectivePrincipalSubgroup25Two
        fullProjectivePrincipalSubgroup25Two_le_degree_ker picardFinitenessDegree25Two) := by
  rintro ⟨c, hc⟩
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective fullProjectivePrincipalSubgroup25Two c
  have hdeg : fullClosedPointGrading25Two.divisorDegree D =
      (picardFinitenessDegree25Two : ℤ) := hc
  have hgt : 4 * (wPolynomialBasisPoleBound25Two : ℤ) <
      fullClosedPointGrading25Two.divisorDegree D := by
    rw [hdeg, picardFinitenessDegree25Two]
    push_cast
    omega
  obtain ⟨E, hE⟩ := exists_effective_representative_of_degree_gt_four_basis_bound D hgt
  refine ⟨⟨E.1, ?_⟩, ?_⟩
  · rw [E.2, hdeg]
    simp
  · apply Subtype.ext
    exact hE

/-- The degree-`4B+1` Picard fibre of the actual curve is finite. -/
theorem picDegree_picardFinitenessDegree_finite :
    Finite (fullClosedPointGrading25Two.PicDegree fullProjectivePrincipalSubgroup25Two
      fullProjectivePrincipalSubgroup25Two_le_degree_ker
      (picardFinitenessDegree25Two : ℤ)) :=
  Finite.of_surjective _ effectiveClass_surjective_picardFinitenessDegree

/-- The class of the degree-one boundary closed point `X`. -/
def boundaryXClass25Two :
    fullClosedPointGrading25Two.DivisorClass fullProjectivePrincipalSubgroup25Two :=
  fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two
    (Finsupp.single (fullBoundaryAtomOfTag FullBoundaryTag25Two.X) 1)

/-- The boundary class `X` has degree one. -/
theorem boundaryXClass25Two_degree :
    fullProjectiveClassDegree25Two boundaryXClass25Two = 1 := by
  change fullClosedPointGrading25Two.divisorDegree
    (Finsupp.single (fullBoundaryAtomOfTag FullBoundaryTag25Two.X) 1) = 1
  change (Finsupp.single (fullBoundaryAtomOfTag FullBoundaryTag25Two.X) (1 : ℤ)).sum
    (fun x m => m * (fullClosedPointGrading25Two.atomDegree x : ℤ)) = 1
  rw [Finsupp.sum_single_index (by simp), fullBoundaryAtomOfTag_degree]
  simp

/-- **The degree-zero Picard group of the actual N25 curve over `F₂` is finite.**
Here `Pic⁰` is the subtype of classes of degree zero in the quotient of the full
closed-point divisor group by divisors of actual nonzero functions. -/
theorem picDegreeZero_finite :
    Finite (fullClosedPointGrading25Two.PicDegree fullProjectivePrincipalSubgroup25Two
      fullProjectivePrincipalSubgroup25Two_le_degree_ker 0) := by
  haveI := picDegree_picardFinitenessDegree_finite
  exact Finite.of_equiv _
    (fullClosedPointGrading25Two.picDegreeEquivZero fullProjectivePrincipalSubgroup25Two
      fullProjectivePrincipalSubgroup25Two_le_degree_ker boundaryXClass25Two
      boundaryXClass25Two_degree (picardFinitenessDegree25Two : ℤ))

noncomputable instance : Fintype (fullClosedPointGrading25Two.PicDegree
    fullProjectivePrincipalSubgroup25Two fullProjectivePrincipalSubgroup25Two_le_degree_ker 0) :=
  haveI := picDegreeZero_finite
  Fintype.ofFinite _

end MazurProof.N25F_PicardZeroFinite
