import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAffineChart
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientSmoothF2
import FLT.Mathlib.RingTheory.RingHom.SmoothJacobian

/-!
# Smoothness of the first affine chart of the N25 binary quotient

This file turns the projective characteristic-two Jacobian certificate into
a Mathlib smoothness proof for the chart \`x=1\`.  The proof has three
structural layers:

* Euler homogeneity eliminates the two minors containing the removed
  projective coordinate;
* three naive complete-intersection presentations identify the remaining
  minors with selected presentation Jacobians;
* the resulting Bézout identity says those Jacobians span the unit ideal, so
  smoothness follows from target-localization locality.

All determinant computations are universal polynomial identities.  There is
no enumeration of field elements or quotient-ring representatives.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoAffineSmooth

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoChartIdeal
open HomogeneousLocalization

/-- On the chart `x=1`, homogeneity expresses the two Jacobian minors
involving the removed coordinate through the three affine minors, modulo the
cubic equation.  Substituting those identities into the existing projective
Bézout certificate gives the affine Jacobian certificate below. -/
theorem xChart_affine_jacobian_certificate
    {K : Type*} [CommRing K] [CharP K 2] (y z w : K) :
    let P : Coordinates4 K := ⟨1, y, z, w⟩
    let q := canonicalQuadric25CharTwo P
    let c := canonicalCubic25CharTwo P
    let M := canonicalJacobianMinors25CharTwo P
    let b := y*w + y + z + w + 1
    let A := y*z*w + z^2 + z*w + w^2 + y + w
    let B := y*z*w + z^2 + y*w + z*w + w^2 + z + w
    let D := y*z^2*w + z^3 + y^2*w + z^2*w + y*w^2 + z*w^2 +
      y^2 + y*z + y*w + w^2 + y + z + w
    A * q + (B + b * (y + z + w)) * c +
      (D + b*y) * M.yz + (y + 1 + b*y) * M.yw +
      (y + 1 + b*w + b*z) * M.zw = 1 := by
  let P : Coordinates4 K := ⟨1, y, z, w⟩
  let q := canonicalQuadric25CharTwo P
  let c := canonicalCubic25CharTwo P
  let M := canonicalJacobianMinors25CharTwo P
  have hxz : M.xz =
      (canonicalQuadricGradient25CharTwo P).z * c +
        y * M.yz + w * M.zw := by
    dsimp [M, P, c, canonicalJacobianMinors25CharTwo,
      canonicalQuadricGradient25CharTwo,
      canonicalCubicGradient25CharTwo,
      canonicalCubic25CharTwo]
    ring_nf
    simp [CharTwo.sub_eq_add, CharTwo.neg_eq, CharTwo.ofNat_eq_mod]
  have hxw : M.xw =
      (canonicalQuadricGradient25CharTwo P).w * c +
        y * M.yw + z * M.zw := by
    dsimp [M, P, c, canonicalJacobianMinors25CharTwo,
      canonicalQuadricGradient25CharTwo,
      canonicalCubicGradient25CharTwo,
      canonicalCubic25CharTwo]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  have hcert := xChart_jacobian_certificate y z w
  change
    (y*z*w + z^2 + z*w + w^2 + y + w) * q +
      (y*z*w + z^2 + y*w + z*w + w^2 + z + w) * c +
      (y*w + y + z + w + 1) * M.xz +
      (y*w + y + z + w + 1) * M.xw +
      (y*z^2*w + z^3 + y^2*w + z^2*w + y*w^2 + z*w^2 +
        y^2 + y*z + y*w + w^2 + y + z + w) * M.yz +
      (y + 1) * M.yw + (y + 1) * M.zw = 1 at hcert
  rw [hxz, hxw] at hcert
  change
    (y*z*w + z^2 + z*w + w^2 + y + w) * q +
      ((y*z*w + z^2 + y*w + z*w + w^2 + z + w) +
        (y*w + y + z + w + 1) * (y + z + w)) * c +
      ((y*z^2*w + z^3 + y^2*w + z^2*w + y*w^2 + z*w^2 +
        y^2 + y*z + y*w + w^2 + y + z + w) +
        (y*w + y + z + w + 1) * y) * M.yz +
      (y + 1 + (y*w + y + z + w + 1) * y) * M.yw +
      (y + 1 + (y*w + y + z + w + 1) * w +
        (y*w + y + z + w + 1) * z) * M.zw = 1
  dsimp [P, canonicalQuadricGradient25CharTwo] at hcert
  ring_nf at hcert ⊢
  simpa [CharTwo.ofNat_eq_mod] using hcert

/-! ## The three selected affine presentations -/

/-- The quotient by the dehomogenized quadric and cubic. -/
abbrev xChartAffineQuotient :=
  xChartAffineRing ⧸ xChartAffineEquationIdeal

/-- Omitting one of the three affine variables selects the other two
columns of the two-row Jacobian matrix. -/
noncomputable def xChartPreSubmersive (omitted : Fin 3) :
    Algebra.PreSubmersivePresentation k xChartAffineQuotient (Fin 3) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive
    (R := k) (v := xChartAffineRelation)
    omitted.succAbove omitted.succAbove_right_injective

/-- The selected Jacobian matrix consists of the corresponding partial
derivatives of the two displayed relations. -/
@[simp]
theorem xChartPreSubmersive_jacobiMatrix
    (omitted : Fin 3) (i j : Fin 2) :
    (xChartPreSubmersive omitted).jacobiMatrix i j =
      MvPolynomial.pderiv (omitted.succAbove i) (xChartAffineRelation j) := by
  exact Algebra.PreSubmersivePresentation.jacobiMatrix_naive
    omitted.succAbove omitted.succAbove_right_injective _ _ i j

/-- For the naive quotient presentation, the presentation algebra map is
the ordinary ideal-quotient map. -/
theorem xChartPreSubmersive_algebraMap (omitted : Fin 3) :
    algebraMap (xChartPreSubmersive omitted).Ring xChartAffineQuotient =
      Ideal.Quotient.mk xChartAffineEquationIdeal := by
  change algebraMap (xChartPreSubmersive omitted).Ring
      (xChartAffineRing ⧸ Ideal.span (Set.range xChartAffineRelation)) =
    Ideal.Quotient.mk (Ideal.span (Set.range xChartAffineRelation))
  apply MvPolynomial.ringHom_ext
  · intro r
    change Ideal.Quotient.mk _ (MvPolynomial.C r) =
      Ideal.Quotient.mk _ (MvPolynomial.C r)
    rfl
  · intro i
    change Ideal.Quotient.mk _ (MvPolynomial.X i) =
      Ideal.Quotient.mk _ (MvPolynomial.X i)
    rfl

/-- The universal affine point `(1,y,z,w)` over its polynomial ring. -/
def xChartUniversalPoint : Coordinates4 xChartAffineRing :=
  ⟨1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2⟩

/-- The three relevant minors as universal affine polynomials. -/
def xChartUniversalMinors : CanonicalJacobianMinors25 xChartAffineRing :=
  canonicalJacobianMinors25CharTwo xChartUniversalPoint

/-- The determinant selected after omitting `y` is the universal `(z,w)`
minor, before passing to the quotient. -/
theorem xChartSelectedMinor_zero :
    MvPolynomial.pderiv ((0 : Fin 3).succAbove 0) (xChartAffineRelation 0) *
        MvPolynomial.pderiv ((0 : Fin 3).succAbove 1) (xChartAffineRelation 1) -
      MvPolynomial.pderiv ((0 : Fin 3).succAbove 0) (xChartAffineRelation 1) *
        MvPolynomial.pderiv ((0 : Fin 3).succAbove 1) (xChartAffineRelation 0) =
      xChartUniversalMinors.zw := by
  simp [xChartUniversalMinors, xChartUniversalPoint,
    xChartAffineQuadric, xChartAffineCubic,
    canonicalJacobianMinors25CharTwo,
    canonicalQuadricGradient25CharTwo,
    canonicalCubicGradient25CharTwo]
  ring_nf
  simp [CharTwo.sub_eq_add, CharTwo.ofNat_eq_mod]

/-- The determinant selected after omitting `z` is the universal `(y,w)`
minor, before passing to the quotient. -/
theorem xChartSelectedMinor_one :
    MvPolynomial.pderiv ((1 : Fin 3).succAbove 0) (xChartAffineRelation 0) *
        MvPolynomial.pderiv ((1 : Fin 3).succAbove 1) (xChartAffineRelation 1) -
      MvPolynomial.pderiv ((1 : Fin 3).succAbove 0) (xChartAffineRelation 1) *
        MvPolynomial.pderiv ((1 : Fin 3).succAbove 1) (xChartAffineRelation 0) =
      xChartUniversalMinors.yw := by
  simp [xChartUniversalMinors, xChartUniversalPoint,
    xChartAffineQuadric, xChartAffineCubic,
    canonicalJacobianMinors25CharTwo,
    canonicalQuadricGradient25CharTwo,
    canonicalCubicGradient25CharTwo]
  ring_nf
  simp [CharTwo.sub_eq_add, CharTwo.ofNat_eq_mod]

/-- The determinant selected after omitting `w` is the universal `(y,z)`
minor, before passing to the quotient. -/
theorem xChartSelectedMinor_two :
    MvPolynomial.pderiv ((2 : Fin 3).succAbove 0) (xChartAffineRelation 0) *
        MvPolynomial.pderiv ((2 : Fin 3).succAbove 1) (xChartAffineRelation 1) -
      MvPolynomial.pderiv ((2 : Fin 3).succAbove 0) (xChartAffineRelation 1) *
        MvPolynomial.pderiv ((2 : Fin 3).succAbove 1) (xChartAffineRelation 0) =
      xChartUniversalMinors.yz := by
  have hzero : (2 : Fin 3).succAbove (0 : Fin 2) = 0 := by decide
  have hone : (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide
  rw [hzero, hone]
  simp [xChartUniversalMinors, xChartUniversalPoint,
    xChartAffineQuadric, xChartAffineCubic,
    canonicalJacobianMinors25CharTwo,
    canonicalQuadricGradient25CharTwo,
    canonicalCubicGradient25CharTwo]
  ring_nf
  simp [CharTwo.sub_eq_add, CharTwo.neg_eq, CharTwo.ofNat_eq_mod]

/-- Omitting `y` selects the `(z,w)` Jacobian minor. -/
theorem xChartPreSubmersive_jacobian_zero :
    (xChartPreSubmersive 0).jacobian =
      algebraMap xChartAffineRing xChartAffineQuotient
        xChartUniversalMinors.zw := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  rw [Matrix.det_fin_two]
  simp_rw [xChartPreSubmersive_jacobiMatrix]
  rw [xChartPreSubmersive_algebraMap]
  rw [xChartSelectedMinor_zero]
  change Ideal.Quotient.mk _ xChartUniversalMinors.zw =
    Ideal.Quotient.mk _ xChartUniversalMinors.zw
  rfl

/-- Omitting `z` selects the `(y,w)` Jacobian minor. -/
theorem xChartPreSubmersive_jacobian_one :
    (xChartPreSubmersive 1).jacobian =
      algebraMap xChartAffineRing xChartAffineQuotient
        xChartUniversalMinors.yw := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  rw [Matrix.det_fin_two]
  simp_rw [xChartPreSubmersive_jacobiMatrix]
  rw [xChartPreSubmersive_algebraMap]
  rw [xChartSelectedMinor_one]
  change Ideal.Quotient.mk _ xChartUniversalMinors.yw =
    Ideal.Quotient.mk _ xChartUniversalMinors.yw
  rfl

/-- Omitting `w` selects the `(y,z)` Jacobian minor. -/
theorem xChartPreSubmersive_jacobian_two :
    (xChartPreSubmersive 2).jacobian =
      algebraMap xChartAffineRing xChartAffineQuotient
        xChartUniversalMinors.yz := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  rw [Matrix.det_fin_two]
  simp_rw [xChartPreSubmersive_jacobiMatrix]
  rw [xChartPreSubmersive_algebraMap]
  rw [xChartSelectedMinor_two]
  change Ideal.Quotient.mk _ xChartUniversalMinors.yz =
    Ideal.Quotient.mk _ xChartUniversalMinors.yz
  rfl

/-! ## Descent of the certificate to the affine quotient -/

/-- The quadric relation vanishes in the affine coordinate quotient. -/
@[simp]
theorem xChartAffineQuotient_quadric :
    algebraMap xChartAffineRing xChartAffineQuotient xChartAffineQuadric = 0 := by
  change Ideal.Quotient.mk xChartAffineEquationIdeal xChartAffineQuadric = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨0, rfl⟩

/-- The cubic relation vanishes in the affine coordinate quotient. -/
@[simp]
theorem xChartAffineQuotient_cubic :
    algebraMap xChartAffineRing xChartAffineQuotient xChartAffineCubic = 0 := by
  change Ideal.Quotient.mk xChartAffineEquationIdeal xChartAffineCubic = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨1, rfl⟩

/-- Evaluating the universal quadric at the three quotient coordinate
classes gives zero because it is the first defining relation. -/
theorem xChartQuotient_quadric :
    canonicalQuadric25CharTwo
        (⟨1,
          algebraMap xChartAffineRing xChartAffineQuotient (MvPolynomial.X 0),
          algebraMap xChartAffineRing xChartAffineQuotient (MvPolynomial.X 1),
          algebraMap xChartAffineRing xChartAffineQuotient (MvPolynomial.X 2)⟩ :
          Coordinates4 xChartAffineQuotient) = 0 := by
  rw [← xChartAffineQuotient_quadric]
  simp [canonicalQuadric25CharTwo, xChartAffineQuadric]

/-- Evaluating the universal cubic at the three quotient coordinate
classes gives zero because it is the second defining relation. -/
theorem xChartQuotient_cubic :
    canonicalCubic25CharTwo
        (⟨1,
          algebraMap xChartAffineRing xChartAffineQuotient (MvPolynomial.X 0),
          algebraMap xChartAffineRing xChartAffineQuotient (MvPolynomial.X 1),
          algebraMap xChartAffineRing xChartAffineQuotient (MvPolynomial.X 2)⟩ :
          Coordinates4 xChartAffineQuotient) = 0 := by
  rw [← xChartAffineQuotient_cubic]
  simp [canonicalCubic25CharTwo, xChartAffineCubic]

/-- The universal `(y,z)` minor specializes to the third selected
presentation Jacobian. -/
theorem xChartQuotient_minor_yz :
    (canonicalJacobianMinors25CharTwo
        (⟨1,
          algebraMap xChartAffineRing xChartAffineQuotient (MvPolynomial.X 0),
          algebraMap xChartAffineRing xChartAffineQuotient (MvPolynomial.X 1),
          algebraMap xChartAffineRing xChartAffineQuotient (MvPolynomial.X 2)⟩ :
          Coordinates4 xChartAffineQuotient)).yz =
      (xChartPreSubmersive 2).jacobian := by
  rw [xChartPreSubmersive_jacobian_two]
  simp [xChartUniversalMinors, xChartUniversalPoint,
    canonicalJacobianMinors25CharTwo,
    canonicalQuadricGradient25CharTwo,
    canonicalCubicGradient25CharTwo]

/-- The universal `(y,w)` minor specializes to the second selected
presentation Jacobian. -/
theorem xChartQuotient_minor_yw :
    (canonicalJacobianMinors25CharTwo
        (⟨1,
          algebraMap xChartAffineRing xChartAffineQuotient (MvPolynomial.X 0),
          algebraMap xChartAffineRing xChartAffineQuotient (MvPolynomial.X 1),
          algebraMap xChartAffineRing xChartAffineQuotient (MvPolynomial.X 2)⟩ :
          Coordinates4 xChartAffineQuotient)).yw =
      (xChartPreSubmersive 1).jacobian := by
  rw [xChartPreSubmersive_jacobian_one]
  simp [xChartUniversalMinors, xChartUniversalPoint,
    canonicalJacobianMinors25CharTwo,
    canonicalQuadricGradient25CharTwo,
    canonicalCubicGradient25CharTwo]

/-- The universal `(z,w)` minor specializes to the first selected
presentation Jacobian. -/
theorem xChartQuotient_minor_zw :
    (canonicalJacobianMinors25CharTwo
        (⟨1,
          algebraMap xChartAffineRing xChartAffineQuotient (MvPolynomial.X 0),
          algebraMap xChartAffineRing xChartAffineQuotient (MvPolynomial.X 1),
          algebraMap xChartAffineRing xChartAffineQuotient (MvPolynomial.X 2)⟩ :
          Coordinates4 xChartAffineQuotient)).zw =
      (xChartPreSubmersive 0).jacobian := by
  rw [xChartPreSubmersive_jacobian_zero]
  simp [xChartUniversalMinors, xChartUniversalPoint,
    canonicalJacobianMinors25CharTwo,
    canonicalQuadricGradient25CharTwo,
    canonicalCubicGradient25CharTwo]

/-- The three selected Jacobians generate the unit ideal in the affine
coordinate quotient.  This is the ideal-theoretic form of the structural
affine Bézout certificate. -/
theorem xChartPreSubmersive_jacobian_span :
    Ideal.span (Set.range fun i ↦ (xChartPreSubmersive i).jacobian) = ⊤ := by
  let π : xChartAffineRing →+* xChartAffineQuotient :=
    algebraMap xChartAffineRing xChartAffineQuotient
  let y : xChartAffineRing := MvPolynomial.X 0
  let z : xChartAffineRing := MvPolynomial.X 1
  let w : xChartAffineRing := MvPolynomial.X 2
  let P : Coordinates4 xChartAffineRing := ⟨1, y, z, w⟩
  let M := canonicalJacobianMinors25CharTwo P
  have hcert := xChart_affine_jacobian_certificate y z w
  change
    let b := y*w + y + z + w + 1
    let A := y*z*w + z^2 + z*w + w^2 + y + w
    let B := y*z*w + z^2 + y*w + z*w + w^2 + z + w
    let D := y*z^2*w + z^3 + y^2*w + z^2*w + y*w^2 + z*w^2 +
      y^2 + y*z + y*w + w^2 + y + z + w
    A * canonicalQuadric25CharTwo P +
      (B + b * (y + z + w)) * canonicalCubic25CharTwo P +
      (D + b*y) * M.yz + (y + 1 + b*y) * M.yw +
      (y + 1 + b*w + b*z) * M.zw = 1 at hcert
  have hq : canonicalQuadric25CharTwo P = xChartAffineQuadric := by
    simp [P, y, z, w, canonicalQuadric25CharTwo, xChartAffineQuadric]
  have hc : canonicalCubic25CharTwo P = xChartAffineCubic := by
    simp [P, y, z, w, canonicalCubic25CharTwo, xChartAffineCubic]
  have hM : M = xChartUniversalMinors := by
    rfl
  have hmapped := congrArg π hcert
  simp only [map_add, map_mul, map_pow, map_one] at hmapped
  dsimp only [π] at hmapped
  rw [hq, hc, hM, xChartAffineQuotient_quadric,
    xChartAffineQuotient_cubic,
    ← xChartPreSubmersive_jacobian_two,
    ← xChartPreSubmersive_jacobian_one,
    ← xChartPreSubmersive_jacobian_zero] at hmapped
  simp only [mul_zero, zero_add] at hmapped
  let J := Ideal.span (Set.range fun i ↦ (xChartPreSubmersive i).jacobian)
  have hzero : (xChartPreSubmersive 0).jacobian ∈ J :=
    Ideal.subset_span ⟨0, rfl⟩
  have hone : (xChartPreSubmersive 1).jacobian ∈ J :=
    Ideal.subset_span ⟨1, rfl⟩
  have htwo : (xChartPreSubmersive 2).jacobian ∈ J :=
    Ideal.subset_span ⟨2, rfl⟩
  apply (Ideal.eq_top_iff_one J).mpr
  rw [← hmapped]
  exact J.add_mem
    (J.add_mem (J.mul_mem_left _ htwo) (J.mul_mem_left _ hone))
    (J.mul_mem_left _ hzero)

/-- The affine complete-intersection quotient on `x=1` is smooth over the
binary ground field. -/
theorem xChartAffineQuotient_smooth :
    RingHom.Smooth (algebraMap k xChartAffineQuotient) :=
  RingHom.Smooth.of_jacobian_span xChartPreSubmersive
    xChartPreSubmersive_jacobian_span

/-! ## Transport to the homogeneous projective chart -/

/-- The actual degree-zero coordinate ring of the standard open chart
`D₊(X₀)` in the projective canonical curve. -/
abbrev xChartCoordinateRing :=
  Away literalConePiece
    (canonicalConeGradedProjection (MvPolynomial.X 0))

/-- The coefficient algebra structure on the projective chart, transported
through the explicit coordinate-ring equivalence.  This records the same
binary constants used by the affine quotient. -/
noncomputable instance xChartCoordinateRingAlgebra :
    Algebra k xChartCoordinateRing :=
  (xChartCoordinateRingEquiv.toRingHom.comp
    (algebraMap k xChartAffineQuotient)).toAlgebra

/-- Smoothness is invariant under the proved coordinate-ring equivalence,
so the actual projective chart is smooth over the binary ground field. -/
theorem xChartCoordinateRing_smooth :
    RingHom.Smooth (algebraMap k xChartCoordinateRing) := by
  have hEquiv : RingHom.Smooth xChartCoordinateRingEquiv.toRingHom :=
    RingHom.Smooth.of_bijective xChartCoordinateRingEquiv.bijective
  have hComp := xChartAffineQuotient_smooth.comp hEquiv
  have hRingHom :
      xChartCoordinateRingEquiv.toRingHom.comp
          (algebraMap k xChartAffineQuotient) =
        algebraMap k xChartCoordinateRing :=
    RingHom.ext_zmod _ _
  rw [hRingHom] at hComp
  exact hComp

end MazurProof.RationalPointsN25QuotientTwoAffineSmooth
