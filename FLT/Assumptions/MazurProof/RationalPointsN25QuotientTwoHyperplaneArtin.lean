import FLT.Assumptions.MazurProof.RationalPointsN25QuotientF2
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Artin targets for the binary hyperplane-section local intersections

The `x=0` hyperplane section has proposed local lengths two, one, and three.
This file constructs the two nonreduced target algebras

`F_2[t]/(t^2)` and `F_2[t]/(t^3)`,

proves their vector-space dimensions, and gives explicit curve coordinates in
them.  These are the finite normal forms expected at `[0:0:0:1]` and
`[0:1:1:0]`.

This is not yet a proof that the localized intersection rings are isomorphic
to these targets.  That next theorem must construct the local evaluation maps
and prove their exact kernels; recording the target algebras first keeps that
remaining scheme-theoretic obligation visible.
-/

namespace MazurProof.RationalPointsN25QuotientTwoHyperplaneArtin

open Polynomial
open RationalPointsN25QuotientF2

/-! ## Exact hyperplane-restriction identities -/

/-- On `x=0` the characteristic-two cubic is the product of three rational
lines.  This factorization separates the three closed points before their
local multiplicities are computed. -/
theorem cubic_x_zero_factor
    {K : Type*} [CommRing K] [CharP K 2] (y z w : K) :
    canonicalCubic25Over (⟨0, y, z, w⟩ : Coordinates4 K) =
      z * w * (y + z + w) := by
  dsimp [canonicalCubic25Over]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination -(z * w ^ 2) * htwo

/-- On the cubic factor `z=0`, the quadric restricts to the doubled equation
`y^2=0`. -/
theorem quadric_xz_zero {K : Type*} [CommRing K] (y w : K) :
    canonicalQuadric25Over (⟨0, y, 0, w⟩ : Coordinates4 K) = y ^ 2 := by
  simp [canonicalQuadric25Over]

/-- On the cubic factor `w=0`, the quadric splits into the two reduced
linear factors `y` and `y+z`. -/
theorem quadric_xw_zero {K : Type*} [CommRing K] (y z : K) :
    canonicalQuadric25Over (⟨0, y, z, 0⟩ : Coordinates4 K) =
      y * (y + z) := by
  simp [canonicalQuadric25Over]
  ring

/-- On the third cubic factor `y+z+w=0`, the quadric becomes the doubled
equation `w^2=0`. -/
theorem quadric_x_zero_third_line
    {K : Type*} [CommRing K] [CharP K 2] (z w : K) :
    canonicalQuadric25Over (⟨0, z + w, z, w⟩ : Coordinates4 K) = w ^ 2 := by
  dsimp [canonicalQuadric25Over]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (z ^ 2 + 2 * z * w) * htwo

/-! ## Affine chart equations -/

/-- In the `w=1` chart of the hyperplane `x=0`, the quadric has equation
`y^2+y*z+z`. -/
theorem wChart_quadric
    {K : Type*} [CommRing K] (y z : K) :
    canonicalQuadric25Over (⟨0, y, z, 1⟩ : Coordinates4 K) =
      y ^ 2 + y * z + z := by
  dsimp [canonicalQuadric25Over]
  ring

/-- In characteristic two, the cubic equation in the same `w=1` chart is
`z*(y+z+1)`. -/
theorem wChart_cubic
    {K : Type*} [CommRing K] [CharP K 2] (y z : K) :
    canonicalCubic25Over (⟨0, y, z, 1⟩ : Coordinates4 K) =
      z * (y + z + 1) := by
  rw [cubic_x_zero_factor]
  ring

/-- Around `[0:1:1:0]`, put `a=z+1` and `b=w`.  In characteristic two the
quadric becomes the triangular relation `a+b+a*b`. -/
theorem yzChart_quadric
    {K : Type*} [CommRing K] [CharP K 2] (a b : K) :
    canonicalQuadric25Over (⟨0, 1, 1 + a, b⟩ : Coordinates4 K) =
      a + b + a * b := by
  dsimp [canonicalQuadric25Over]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination htwo

/-- In the same coordinates, the cubic is
`(1+a)*b*(a+b)`. -/
theorem yzChart_cubic
    {K : Type*} [CommRing K] [CharP K 2] (a b : K) :
    canonicalCubic25Over (⟨0, 1, 1 + a, b⟩ : Coordinates4 K) =
      (1 + a) * b * (a + b) := by
  rw [cubic_x_zero_factor]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (1 + a) * b * htwo

/-! ## Local ideal normal forms

The two lemmas below perform the scheme-theoretic algebra hidden by the
set-theoretic factorization of the hyperplane section.  They are stated in an
arbitrary coordinate ring so that they can later be applied directly after
localization.  The unit hypotheses record the principal open neighbourhoods
that isolate the relevant closed points.
-/

/-- On the principal open set where `y+z+1` is invertible, the equations in
the `w=1` chart generate `(y^2,z)`.  Thus the residual parameter is `y`, with
square zero; this is the algebraic source of multiplicity two at
`[0:0:0:1]`. -/
theorem wChart_intersectionIdeal_eq_normalForm
    {R : Type*} [CommRing R] (y z : R) (hu : IsUnit (y + z + 1)) :
    Ideal.span {y ^ 2 + y * z + z, z * (y + z + 1)} =
      Ideal.span {y ^ 2, z} := by
  let uInv : R := ↑hu.unit⁻¹
  have hInv : uInv * (y + z + 1) = 1 := hu.val_inv_mul
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with hr | hr
    · subst r
      exact Ideal.mem_span_pair.mpr ⟨1, y + 1, by ring⟩
    · subst r
      exact Ideal.mem_span_pair.mpr ⟨0, y + z + 1, by ring⟩
  · refine Ideal.span_le.2 ?_
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with hr | hr
    · subst r
      exact Ideal.mem_span_pair.mpr
        ⟨1, -(y + 1) * uInv, by
          calc
            1 * (y ^ 2 + y * z + z) + (-(y + 1) * uInv) *
                (z * (y + z + 1)) =
                y ^ 2 + z * (y + 1) * (1 - uInv * (y + z + 1)) := by ring
            _ = y ^ 2 := by rw [hInv]; ring⟩
    · subst r
      exact Ideal.mem_span_pair.mpr
        ⟨0, uInv, by
          calc
            0 * (y ^ 2 + y * z + z) + uInv * (z * (y + z + 1)) =
                z * (uInv * (y + z + 1)) := by ring
            _ = z := by rw [hInv, mul_one]⟩

/-- In characteristic two, after inverting `1+b`, the equations in the
`y=1` chart have triangular normal form `(a+b+a*b,b^3)`, where `a=z+1` and
`b=w`.  The first relation eliminates `a`; the second leaves the single
nilpotent parameter `b` of order three, explaining the multiplicity at
`[0:1:1:0]`. -/
theorem yzChart_intersectionIdeal_eq_normalForm
    {R : Type*} [CommRing R] [CharP R 2] (a b : R)
    (hu : IsUnit (1 + b)) :
    Ideal.span {a + b + a * b, (1 + a) * b * (a + b)} =
      Ideal.span {a + b + a * b, b ^ 3} := by
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have hthree : (3 : R) = 1 := by linear_combination htwo
  have hfour : (4 : R) = 0 := by linear_combination 2 * htwo
  have hsix : (6 : R) = 0 := by linear_combination 3 * htwo
  let uInv : R := ↑hu.unit⁻¹
  have hInv : uInv * (1 + b) = 1 := hu.val_inv_mul
  have hInvSq : uInv ^ 2 * (1 + b) ^ 2 = 1 := by
    rw [← mul_pow, hInv, one_pow]
  let h : R := a * b ^ 2 + a * b + b ^ 3 + b ^ 2 + b
  have hEliminate :
      h * (a + b + a * b) + (1 + b) ^ 2 * ((1 + a) * b * (a + b)) =
        b ^ 3 := by
    dsimp [h]
    ring_nf
    simp [htwo, hthree, hfour, hsix]
  have hSolve :
      b ^ 3 - h * (a + b + a * b) =
        (1 + b) ^ 2 * ((1 + a) * b * (a + b)) := by
    linear_combination -hEliminate
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact Ideal.mem_span_pair.mpr ⟨1, 0, by ring⟩
    · exact Ideal.mem_span_pair.mpr
        ⟨-(uInv ^ 2) * h, uInv ^ 2, by
          calc
            -(uInv ^ 2) * h * (a + b + a * b) + uInv ^ 2 * b ^ 3 =
                uInv ^ 2 * (b ^ 3 - h * (a + b + a * b)) := by ring
            _ = uInv ^ 2 * ((1 + b) ^ 2 * ((1 + a) * b * (a + b))) := by
              rw [hSolve]
            _ = (1 + a) * b * (a + b) := by
              rw [← mul_assoc, hInvSq, one_mul]⟩
  · refine Ideal.span_le.2 ?_
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact Ideal.mem_span_pair.mpr ⟨1, 0, by ring⟩
    · exact Ideal.mem_span_pair.mpr
        ⟨h, (1 + b) ^ 2, hEliminate⟩

/-! ## Finite Artin targets -/

/-- The length-two Artin algebra at `[0:0:0:1]`. -/
abbrev DoubleArtin :=
  AdjoinRoot ((X : (ZMod 2)[X]) ^ 2)

/-- The length-three Artin algebra at `[0:1:1:0]`. -/
abbrev TripleArtin :=
  AdjoinRoot ((X : (ZMod 2)[X]) ^ 3)

/-- The length-two quotient retains characteristic two because its defining
polynomial is nonconstant, so the base-field map remains injective. -/
noncomputable instance doubleArtinCharP : CharP DoubleArtin 2 :=
  charP_of_injective_algebraMap
    (AdjoinRoot.of.injective_of_degree_ne_zero (by simp)) 2

/-- The length-three quotient retains characteristic two because its defining
polynomial is nonconstant, so the base-field map remains injective. -/
noncomputable instance tripleArtinCharP : CharP TripleArtin 2 :=
  charP_of_injective_algebraMap
    (AdjoinRoot.of.injective_of_degree_ne_zero (by simp)) 2

/-- The nilpotent parameter in the length-two target. -/
noncomputable def doubleRoot : DoubleArtin :=
  AdjoinRoot.root ((X : (ZMod 2)[X]) ^ 2)

/-- The nilpotent parameter in the length-three target. -/
noncomputable def tripleRoot : TripleArtin :=
  AdjoinRoot.root ((X : (ZMod 2)[X]) ^ 3)

/-- The defining relation in the length-two Artin target. -/
theorem doubleRoot_sq : doubleRoot ^ 2 = 0 := by
  change (AdjoinRoot.mk ((X : (ZMod 2)[X]) ^ 2)) (X ^ 2) = 0
  exact AdjoinRoot.mk_eq_zero.mpr dvd_rfl

/-- The defining relation in the length-three Artin target. -/
theorem tripleRoot_cube : tripleRoot ^ 3 = 0 := by
  change (AdjoinRoot.mk ((X : (ZMod 2)[X]) ^ 3)) (X ^ 3) = 0
  exact AdjoinRoot.mk_eq_zero.mpr dvd_rfl

/-- The parameter in the doubled target is nilpotent. -/
theorem doubleRoot_nilpotent : IsNilpotent doubleRoot :=
  ⟨2, doubleRoot_sq⟩

/-- The parameter in the tripled target is nilpotent. -/
theorem tripleRoot_nilpotent : IsNilpotent tripleRoot :=
  ⟨3, tripleRoot_cube⟩

/-- The principal-open denominator at the doubled point maps to a unit in
the target algebra.  This is the condition needed to extend evaluation over
that localization. -/
theorem isUnit_one_add_doubleRoot : IsUnit (1 + doubleRoot) :=
  doubleRoot_nilpotent.isUnit_one_add

/-- The principal-open denominator at the tripled point maps to a unit in
the target algebra.  Hence evaluation at `b=t` extends over `D(1+b)`. -/
theorem isUnit_one_add_tripleRoot : IsUnit (1 + tripleRoot) :=
  tripleRoot_nilpotent.isUnit_one_add

/-- The first local target has vector-space length two over `F_2`. -/
theorem doubleArtin_finrank : Module.finrank (ZMod 2) DoubleArtin = 2 := by
  have hf : (X : (ZMod 2)[X]) ^ 2 ≠ 0 := by simp
  rw [(AdjoinRoot.powerBasis hf).finrank,
    AdjoinRoot.powerBasis_dim hf]
  norm_num

/-- The third local target has vector-space length three over `F_2`. -/
theorem tripleArtin_finrank : Module.finrank (ZMod 2) TripleArtin = 3 := by
  have hf : (X : (ZMod 2)[X]) ^ 3 ≠ 0 := by simp
  rw [(AdjoinRoot.powerBasis hf).finrank,
    AdjoinRoot.powerBasis_dim hf]
  norm_num

/-! ## Affine coordinate-ring evaluations

The variable with index zero is `y` in the `w=1` chart and `a=z+1` in the
`y=1` chart.  The variable with index one is respectively `z` and `b=w`.
-/

/-- The binary affine plane used for both local coordinate calculations. -/
abbrev BinaryAffinePlane := MvPolynomial (Fin 2) (ZMod 2)

/-- The quadric relation in the `w=1` chart. -/
noncomputable def wChartQuadricPolynomial : BinaryAffinePlane :=
  MvPolynomial.X 0 ^ 2 + MvPolynomial.X 0 * MvPolynomial.X 1 +
    MvPolynomial.X 1

/-- The cubic relation in the `w=1` chart. -/
noncomputable def wChartCubicPolynomial : BinaryAffinePlane :=
  MvPolynomial.X 1 * (MvPolynomial.X 0 + MvPolynomial.X 1 + 1)

/-- The quadric relation in the translated `y=1` chart. -/
noncomputable def yzChartQuadricPolynomial : BinaryAffinePlane :=
  MvPolynomial.X 0 + MvPolynomial.X 1 +
    MvPolynomial.X 0 * MvPolynomial.X 1

/-- The cubic relation in the translated `y=1` chart. -/
noncomputable def yzChartCubicPolynomial : BinaryAffinePlane :=
  (1 + MvPolynomial.X 0) * MvPolynomial.X 1 *
    (MvPolynomial.X 0 + MvPolynomial.X 1)

/-- The principal-open denominator isolating `[0:0:0:1]` in the `w=1`
chart. -/
noncomputable def wChartDenominator : BinaryAffinePlane :=
  MvPolynomial.X 0 + MvPolynomial.X 1 + 1

/-- The principal-open denominator used to solve the translated quadric near
`[0:1:1:0]`. -/
noncomputable def yzChartDenominator : BinaryAffinePlane :=
  1 + MvPolynomial.X 1

/-- Evaluate the `w=1` chart at the doubled infinitesimal point
`(y,z)=(t,0)`. -/
noncomputable def doubleEvaluation : BinaryAffinePlane →ₐ[ZMod 2] DoubleArtin :=
  MvPolynomial.aeval ![doubleRoot, 0]

/-- Evaluate the translated `y=1` chart at
`(a,b)=(t+t^2,t)` in the length-three target. -/
noncomputable def tripleEvaluation : BinaryAffinePlane →ₐ[ZMod 2] TripleArtin :=
  MvPolynomial.aeval ![tripleRoot + tripleRoot ^ 2, tripleRoot]

@[simp]
theorem doubleEvaluation_X_zero :
    doubleEvaluation (MvPolynomial.X 0) = doubleRoot := by
  simp [doubleEvaluation]

@[simp]
theorem doubleEvaluation_X_one :
    doubleEvaluation (MvPolynomial.X 1) = 0 := by
  simp [doubleEvaluation]

@[simp]
theorem tripleEvaluation_X_zero :
    tripleEvaluation (MvPolynomial.X 0) = tripleRoot + tripleRoot ^ 2 := by
  simp [tripleEvaluation]

@[simp]
theorem tripleEvaluation_X_one :
    tripleEvaluation (MvPolynomial.X 1) = tripleRoot := by
  simp [tripleEvaluation]

/-- Every element of the doubled Artin target is a polynomial in the image
of the first affine coordinate, so the evaluation map is surjective. -/
theorem doubleEvaluation_surjective : Function.Surjective doubleEvaluation := by
  intro x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨Polynomial.toMvPolynomial (R := ZMod 2) (0 : Fin 2) p, ?_⟩
  rw [doubleEvaluation, MvPolynomial.aeval_toMvPolynomial]
  exact AdjoinRoot.aeval_eq p

/-- Every element of the tripled Artin target is a polynomial in the image
of the second affine coordinate, so this evaluation is also surjective. -/
theorem tripleEvaluation_surjective : Function.Surjective tripleEvaluation := by
  intro x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨Polynomial.toMvPolynomial (R := ZMod 2) (1 : Fin 2) p, ?_⟩
  rw [tripleEvaluation, MvPolynomial.aeval_toMvPolynomial]
  exact AdjoinRoot.aeval_eq p

/-- The doubled evaluation sends its chart denominator to `1+t`, hence to a
unit. -/
theorem doubleEvaluation_denominator_isUnit :
    IsUnit (doubleEvaluation wChartDenominator) := by
  simpa [wChartDenominator, add_comm, add_left_comm, add_assoc] using
    isUnit_one_add_doubleRoot

/-- The tripled evaluation sends its chart denominator to `1+t`, hence to a
unit. -/
theorem tripleEvaluation_denominator_isUnit :
    IsUnit (tripleEvaluation yzChartDenominator) := by
  simpa [yzChartDenominator] using isUnit_one_add_tripleRoot

/-- Evaluation at the doubled infinitesimal point extended over the
principal open set `D(y+z+1)`. -/
noncomputable def doubleLocalizedEvaluation :
    Localization.Away wChartDenominator →+* DoubleArtin :=
  Localization.awayLift doubleEvaluation.toRingHom wChartDenominator
    doubleEvaluation_denominator_isUnit

/-- Evaluation at the tripled infinitesimal point extended over the
principal open set `D(1+b)`. -/
noncomputable def tripleLocalizedEvaluation :
    Localization.Away yzChartDenominator →+* TripleArtin :=
  Localization.awayLift tripleEvaluation.toRingHom yzChartDenominator
    tripleEvaluation_denominator_isUnit

/-- The doubled evaluation kills the restricted quadric. -/
theorem doubleEvaluation_quadric :
    doubleEvaluation wChartQuadricPolynomial = 0 := by
  simp [wChartQuadricPolynomial, doubleRoot_sq]

/-- The doubled evaluation kills the restricted cubic. -/
theorem doubleEvaluation_cubic :
    doubleEvaluation wChartCubicPolynomial = 0 := by
  simp [wChartCubicPolynomial]

/-- Consequently the complete-intersection ideal maps into the kernel of the
doubled evaluation.  Exactness will be proved after passing to `D(y+z+1)`. -/
theorem wChartIdeal_le_doubleEvaluation_ker :
    Ideal.span {wChartQuadricPolynomial, wChartCubicPolynomial} ≤
      RingHom.ker doubleEvaluation.toRingHom := by
  refine Ideal.span_le.2 ?_
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact doubleEvaluation_quadric
  · exact doubleEvaluation_cubic

/-- The tripled evaluation kills the translated quadric. -/
theorem tripleEvaluation_quadric :
    tripleEvaluation yzChartQuadricPolynomial = 0 := by
  simp only [yzChartQuadricPolynomial, map_add, map_mul,
    tripleEvaluation_X_zero, tripleEvaluation_X_one]
  have htwo : (2 : TripleArtin) = 0 := CharP.cast_eq_zero TripleArtin 2
  linear_combination tripleRoot_cube +
    (tripleRoot + tripleRoot ^ 2) * htwo

/-- The tripled evaluation kills the translated cubic. -/
theorem tripleEvaluation_cubic :
    tripleEvaluation yzChartCubicPolynomial = 0 := by
  simp only [yzChartCubicPolynomial, map_add, map_mul,
    tripleEvaluation_X_zero, tripleEvaluation_X_one, map_one]
  have htwo : (2 : TripleArtin) = 0 := CharP.cast_eq_zero TripleArtin 2
  have hTranslatedSum :
      tripleRoot + tripleRoot ^ 2 + tripleRoot = tripleRoot ^ 2 := by
    linear_combination tripleRoot * htwo
  rw [hTranslatedSum]
  calc
    (1 + (tripleRoot + tripleRoot ^ 2)) * tripleRoot * tripleRoot ^ 2 =
        (1 + (tripleRoot + tripleRoot ^ 2)) * tripleRoot ^ 3 := by ring
    _ = 0 := by rw [tripleRoot_cube, mul_zero]

/-- Consequently the complete-intersection ideal maps into the kernel of the
tripled evaluation.  The remaining local theorem is the reverse containment
after inverting `1+b`. -/
theorem yzChartIdeal_le_tripleEvaluation_ker :
    Ideal.span {yzChartQuadricPolynomial, yzChartCubicPolynomial} ≤
      RingHom.ker tripleEvaluation.toRingHom := by
  refine Ideal.span_le.2 ?_
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact tripleEvaluation_quadric
  · exact tripleEvaluation_cubic

/-! ## Explicit infinitesimal curve points -/

/-- The doubled point in the `w=1` chart: `y=t`, `z=0`. -/
noncomputable def doubleCoordinates : Coordinates4 DoubleArtin :=
  ⟨0, doubleRoot, 0, 1⟩

/-- The doubled target satisfies the restricted quadric. -/
theorem doubleCoordinates_quadric :
    canonicalQuadric25Over doubleCoordinates = 0 := by
  rw [doubleCoordinates, quadric_xz_zero]
  exact doubleRoot_sq

/-- The doubled target satisfies the restricted cubic because `z=0`. -/
theorem doubleCoordinates_cubic :
    canonicalCubic25Over doubleCoordinates = 0 := by
  rw [doubleCoordinates, cubic_x_zero_factor]
  simp

/-- The length-three point in the `y=1` chart.  Modulo `t^3`, the equation
`a + t + a*t = 0` is solved by `a=t+t^2`, hence
`z=1+t+t^2`, `w=t`. -/
noncomputable def tripleCoordinates : Coordinates4 TripleArtin :=
  ⟨0, 1, 1 + tripleRoot + tripleRoot ^ 2, tripleRoot⟩

/-- The length-three target satisfies the restricted quadric. -/
theorem tripleCoordinates_quadric :
    canonicalQuadric25Over tripleCoordinates = 0 := by
  dsimp [tripleCoordinates, canonicalQuadric25Over]
  have htwo : (2 : TripleArtin) = 0 := CharP.cast_eq_zero TripleArtin 2
  linear_combination tripleRoot_cube +
    (1 + tripleRoot + tripleRoot ^ 2) * htwo

/-- The length-three target satisfies the restricted cubic. -/
theorem tripleCoordinates_cubic :
    canonicalCubic25Over tripleCoordinates = 0 := by
  rw [tripleCoordinates, cubic_x_zero_factor]
  have htwo : (2 : TripleArtin) = 0 := CharP.cast_eq_zero TripleArtin 2
  linear_combination
    (5 + 3 * tripleRoot + tripleRoot ^ 2) * tripleRoot_cube +
      (tripleRoot + 2 * tripleRoot ^ 2) * htwo

end MazurProof.RationalPointsN25QuotientTwoHyperplaneArtin
