import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoHyperplaneArtin

/-!
# Exact kernels for the binary hyperplane-section Artin models

The preceding Artin-model file reduces the two nonreduced local intersection
ideals to triangular normal forms.  This file proves that the associated
affine evaluations have exactly those kernels.  The proof constructs explicit
algebra equivalences

`F_2[y,z]/(y^2,z) ≃ F_2[t]/(t^2)`

and

`F_2[a,b]/(a+b+a*b,b^3) ≃ F_2[t]/(t^3)`.

For the tripled point, the key structural step is that `b^3=0` makes `1+b`
invertible.  The relation

`(1+b) * (a+b+b^2) = (a+b+a*b) + b^3`

then solves `a=b+b^2` in the quotient.  Thus neither kernel calculation uses
finite enumeration or a dimension-only argument.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoHyperplaneArtin

open Polynomial

/-! ## The doubled normal form -/

/-- The triangular ideal encoding the doubled local normal form. -/
def doubleNormalIdeal : Ideal BinaryAffinePlane :=
  Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 1}

/-- The doubled evaluation kills both generators of its triangular ideal. -/
theorem doubleNormalIdeal_le_ker :
    doubleNormalIdeal ≤ RingHom.ker doubleEvaluation.toRingHom := by
  refine Ideal.span_le.2 ?_
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · simpa using doubleRoot_sq
  · simp

/-- The map from the triangular quotient to the length-two Artin algebra. -/
def doubleQuotientToArtin :
    BinaryAffinePlane ⧸ doubleNormalIdeal →ₐ[ZMod 2] DoubleArtin :=
  Ideal.Quotient.liftₐ doubleNormalIdeal doubleEvaluation
    (fun _ hp => doubleNormalIdeal_le_ker hp)

/-- In the triangular quotient, the first coordinate is square zero. -/
theorem doubleQuotient_first_sq :
    (Ideal.Quotient.mkₐ (ZMod 2) doubleNormalIdeal (MvPolynomial.X 0)) ^ 2 = 0 := by
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_insert _ _))

/-- The second coordinate vanishes in the triangular quotient. -/
theorem doubleQuotient_second_eq_zero :
    Ideal.Quotient.mkₐ (ZMod 2) doubleNormalIdeal (MvPolynomial.X 1) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span
    (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))

/-- Send the Artin parameter back to the first coordinate of the triangular
quotient. -/
def doubleArtinToQuotient :
    DoubleArtin →ₐ[ZMod 2] BinaryAffinePlane ⧸ doubleNormalIdeal :=
  AdjoinRoot.liftAlgHom ((Polynomial.X : (ZMod 2)[X]) ^ 2)
    (Algebra.ofId (ZMod 2) (BinaryAffinePlane ⧸ doubleNormalIdeal))
    (Ideal.Quotient.mkₐ (ZMod 2) doubleNormalIdeal (MvPolynomial.X 0)) (by
      simpa using doubleQuotient_first_sq)

/-- The two maps are inverse on the doubled Artin target because they agree
on its single adjoined generator. -/
theorem doubleQuotientToArtin_comp_doubleArtinToQuotient :
    doubleQuotientToArtin.comp doubleArtinToQuotient =
      AlgHom.id (ZMod 2) DoubleArtin := by
  ext
  simp [doubleQuotientToArtin, doubleArtinToQuotient, doubleRoot]

/-- The two maps are inverse on the doubled triangular quotient: the first
variable is preserved and the second variable is zero. -/
theorem doubleArtinToQuotient_comp_doubleQuotientToArtin :
    doubleArtinToQuotient.comp doubleQuotientToArtin =
      AlgHom.id (ZMod 2) (BinaryAffinePlane ⧸ doubleNormalIdeal) := by
  apply Ideal.Quotient.algHom_ext
  ext i
  fin_cases i
  · simp [doubleQuotientToArtin, doubleArtinToQuotient, doubleRoot]
  · simpa [doubleQuotientToArtin] using doubleQuotient_second_eq_zero.symm

/-- The doubled triangular quotient is exactly the length-two Artin
algebra. -/
def doubleNormalQuotientAlgEquiv :
    (BinaryAffinePlane ⧸ doubleNormalIdeal) ≃ₐ[ZMod 2] DoubleArtin :=
  AlgEquiv.ofAlgHom doubleQuotientToArtin doubleArtinToQuotient
    doubleQuotientToArtin_comp_doubleArtinToQuotient
    doubleArtinToQuotient_comp_doubleQuotientToArtin

/-- The doubled evaluation has precisely the triangular normal-form ideal as
its kernel. -/
theorem doubleEvaluation_ker :
    RingHom.ker doubleEvaluation.toRingHom = doubleNormalIdeal := by
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply doubleNormalQuotientAlgEquiv.injective
    change doubleEvaluation p = 0
    exact hp
  · exact doubleNormalIdeal_le_ker

/-! ## The tripled normal form -/

/-- The triangular ideal encoding the tripled local normal form. -/
def tripleNormalIdeal : Ideal BinaryAffinePlane :=
  Ideal.span {yzChartQuadricPolynomial, MvPolynomial.X 1 ^ 3}

/-- The tripled evaluation kills both generators of its triangular ideal. -/
theorem tripleNormalIdeal_le_ker :
    tripleNormalIdeal ≤ RingHom.ker tripleEvaluation.toRingHom := by
  refine Ideal.span_le.2 ?_
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact tripleEvaluation_quadric
  · simpa using tripleRoot_cube

/-- The map from the triangular quotient to the length-three Artin algebra. -/
def tripleQuotientToArtin :
    BinaryAffinePlane ⧸ tripleNormalIdeal →ₐ[ZMod 2] TripleArtin :=
  Ideal.Quotient.liftₐ tripleNormalIdeal tripleEvaluation
    (fun _ hp => tripleNormalIdeal_le_ker hp)

/-- In the triangular quotient, the second coordinate has cube zero. -/
theorem tripleQuotient_second_cube :
    (Ideal.Quotient.mkₐ (ZMod 2) tripleNormalIdeal (MvPolynomial.X 1)) ^ 3 = 0 := by
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _))))

/-- Send the Artin parameter back to the second coordinate of the triangular
quotient. -/
def tripleArtinToQuotient :
    TripleArtin →ₐ[ZMod 2] BinaryAffinePlane ⧸ tripleNormalIdeal :=
  AdjoinRoot.liftAlgHom ((Polynomial.X : (ZMod 2)[X]) ^ 3)
    (Algebra.ofId (ZMod 2) (BinaryAffinePlane ⧸ tripleNormalIdeal))
    (Ideal.Quotient.mkₐ (ZMod 2) tripleNormalIdeal (MvPolynomial.X 1)) (by
      simpa using tripleQuotient_second_cube)

/-- The two maps are inverse on the tripled Artin target because they agree
on its single adjoined generator. -/
theorem tripleQuotientToArtin_comp_tripleArtinToQuotient :
    tripleQuotientToArtin.comp tripleArtinToQuotient =
      AlgHom.id (ZMod 2) TripleArtin := by
  ext
  simp [tripleQuotientToArtin, tripleArtinToQuotient, tripleRoot]

/-- The triangular relation solves the first quotient coordinate as
`a=b+b^2`; nilpotence makes `1+b` invertible. -/
theorem tripleQuotient_first_eq_second_add_sq :
    Ideal.Quotient.mkₐ (ZMod 2) tripleNormalIdeal (MvPolynomial.X 0) =
      Ideal.Quotient.mkₐ (ZMod 2) tripleNormalIdeal
        (MvPolynomial.X 1 + MvPolynomial.X 1 ^ 2) := by
  let A : BinaryAffinePlane ⧸ tripleNormalIdeal :=
    Ideal.Quotient.mkₐ (ZMod 2) tripleNormalIdeal (MvPolynomial.X 0)
  let B : BinaryAffinePlane ⧸ tripleNormalIdeal :=
    Ideal.Quotient.mkₐ (ZMod 2) tripleNormalIdeal (MvPolynomial.X 1)
  have hRelation : A + B + A * B = 0 := by
    change Ideal.Quotient.mkₐ (ZMod 2) tripleNormalIdeal
      yzChartQuadricPolynomial = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert _ _))
  have hCube : B ^ 3 = 0 := tripleQuotient_second_cube
  have htwo : (2 : BinaryAffinePlane ⧸ tripleNormalIdeal) = 0 := by
    have htwoCoeff : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
    change Ideal.Quotient.mk tripleNormalIdeal
      (MvPolynomial.C (2 : ZMod 2)) = 0
    rw [htwoCoeff, map_zero]
    exact map_zero (Ideal.Quotient.mk tripleNormalIdeal)
  have hProduct : (1 + B) * (A + B + B ^ 2) = 0 := by
    calc
      (1 + B) * (A + B + B ^ 2) =
          (A + B + A * B) + 2 * B ^ 2 + B ^ 3 := by ring
      _ = 0 := by rw [hRelation, hCube, htwo]; ring
  have hUnit : IsUnit (1 + B) :=
    (show IsNilpotent B from ⟨3, hCube⟩).isUnit_one_add
  have hSolved : A + B + B ^ 2 = 0 :=
    hUnit.mul_right_eq_zero.mp hProduct
  have hSum : A + (B + B ^ 2) = 0 := by
    simpa [add_assoc] using hSolved
  have hAddSelf : (B + B ^ 2) + (B + B ^ 2) = 0 := by
    calc
      (B + B ^ 2) + (B + B ^ 2) = 2 * (B + B ^ 2) := by ring
      _ = 0 := by rw [htwo, zero_mul]
  have hNeg : -(B + B ^ 2) = B + B ^ 2 :=
    neg_eq_iff_add_eq_zero.mpr hAddSelf
  change A = B + B ^ 2
  exact (eq_neg_of_add_eq_zero_left hSum).trans hNeg

/-- The two maps are inverse on the tripled triangular quotient. -/
theorem tripleArtinToQuotient_comp_tripleQuotientToArtin :
    tripleArtinToQuotient.comp tripleQuotientToArtin =
      AlgHom.id (ZMod 2) (BinaryAffinePlane ⧸ tripleNormalIdeal) := by
  apply Ideal.Quotient.algHom_ext
  ext i
  fin_cases i
  · simpa [tripleQuotientToArtin, tripleArtinToQuotient, tripleRoot] using
      tripleQuotient_first_eq_second_add_sq.symm
  · simp [tripleQuotientToArtin, tripleArtinToQuotient, tripleRoot]

/-- The tripled triangular quotient is exactly the length-three Artin
algebra. -/
def tripleNormalQuotientAlgEquiv :
    (BinaryAffinePlane ⧸ tripleNormalIdeal) ≃ₐ[ZMod 2] TripleArtin :=
  AlgEquiv.ofAlgHom tripleQuotientToArtin tripleArtinToQuotient
    tripleQuotientToArtin_comp_tripleArtinToQuotient
    tripleArtinToQuotient_comp_tripleQuotientToArtin

/-- The tripled evaluation has precisely the triangular normal-form ideal as
its kernel. -/
theorem tripleEvaluation_ker :
    RingHom.ker tripleEvaluation.toRingHom = tripleNormalIdeal := by
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply tripleNormalQuotientAlgEquiv.injective
    change tripleEvaluation p = 0
    exact hp
  · exact tripleNormalIdeal_le_ker

end MazurProof.RationalPointsN25QuotientTwoHyperplaneArtin
