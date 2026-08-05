import FLT.Assumptions.MazurProof.RationalPointsN25CanonicalPoints

/-!
# The order-five action on the level-25 genus-four quotient

LMFDB curve `25.150.4.f.1` has canonical model

```
Q = -x*z - x*w + y^2 + y*z + z*w = 0,
C = x^2*w + x*y*z - x*y*w - x*z*w + y*z*w + z^2*w - z*w^2 = 0.
```

This file formalizes the explicit projective transformation

```
tau(x,y,z,w) = (z, w-y, -w, x-y).
```

It proves that `tau` has exact fifth iterate equal to the identity, preserves
the canonical complete intersection, and cyclically permutes the five listed
rational cusps.  It also records an equivariant linear change of coordinates
to the augmentation hyperplane in the regular five-cycle representation:

```
(x,y,z,w) |-> (x, z, -w, y-x, w-y-z).
```

The latter coordinates sum to zero and `tau` becomes cyclic rotation.  This
gives explicit quadratic, cubic, and quintic invariant polynomials suitable
for later cyclic-quintic descent arguments.
-/

namespace MazurProof.RationalPointsN25QuotientAction

open RationalPointsN25CanonicalPoints

/-! ## The four-dimensional order-five representation -/

/-- Homogeneous coordinates on the canonical `P^3` model. -/
@[ext]
structure Coordinates25 where
  x : ℚ
  y : ℚ
  z : ℚ
  w : ℚ
deriving DecidableEq

/-- Scalar multiplication of a homogeneous coordinate vector. -/
def scale25 (a : ℚ) (p : Coordinates25) : Coordinates25 :=
  ⟨a * p.x, a * p.y, a * p.z, a * p.w⟩

/-- The explicit order-five linear transformation on the canonical model. -/
def tau25 (p : Coordinates25) : Coordinates25 :=
  ⟨p.z, p.w - p.y, -p.w, p.x - p.y⟩

/-- The second iterate of `tau25`, in coordinates. -/
theorem tau25_sq (p : Coordinates25) :
    tau25 (tau25 p) =
      ⟨-p.w, p.x - p.w, p.y - p.x, p.y + p.z - p.w⟩ := by
  ext <;> simp [tau25]
  ring

/-- The third iterate of `tau25`, in coordinates. -/
theorem tau25_cube (p : Coordinates25) :
    tau25 (tau25 (tau25 p)) =
      ⟨p.y - p.x, p.y + p.z - p.x, p.w - p.y - p.z, -p.x⟩ := by
  ext <;> simp [tau25] <;> ring

/-- The fourth iterate of `tau25`, in coordinates. -/
theorem tau25_fourth (p : Coordinates25) :
    tau25 (tau25 (tau25 (tau25 p))) =
      ⟨p.w - p.y - p.z, -p.y - p.z, p.x, -p.z⟩ := by
  ext <;> simp [tau25] <;> ring

/-- Five applications of `tau25` are the identity. -/
theorem tau25_fifth (p : Coordinates25) :
    tau25 (tau25 (tau25 (tau25 (tau25 p)))) = p := by
  ext <;> simp [tau25] <;> ring

/-- `tau25` is injective. -/
theorem tau25_injective : Function.Injective tau25 := by
  intro p q hpq
  have h := congrArg (fun r => tau25 (tau25 (tau25 (tau25 r)))) hpq
  simpa only [tau25_fifth] using h

/-- `tau25` is surjective, with fourth iterate as inverse. -/
theorem tau25_surjective : Function.Surjective tau25 := by
  intro p
  refine ⟨tau25 (tau25 (tau25 (tau25 p))), ?_⟩
  exact tau25_fifth p

/-- `tau25` is a bijection of the ambient homogeneous coordinate space. -/
theorem tau25_bijective : Function.Bijective tau25 :=
  ⟨tau25_injective, tau25_surjective⟩

/-- The ambient order-five transformation as an explicit equivalence, with
fourth iterate as inverse. -/
def tauEquiv25 : Coordinates25 ≃ Coordinates25 where
  toFun := tau25
  invFun p := tau25 (tau25 (tau25 (tau25 p)))
  left_inv := tau25_fifth
  right_inv := tau25_fifth

/-- The action is homogeneous of degree one. -/
theorem tau25_scale (a : ℚ) (p : Coordinates25) :
    tau25 (scale25 a p) = scale25 a (tau25 p) := by
  ext <;> simp [tau25, scale25] <;> ring

/-! ## Projective equality and the canonical equations -/

/-- Existing projective equality, packaged for `Coordinates25`. -/
def ProjectivelyEqual25 (p q : Coordinates25) : Prop :=
  ProjectivelyEqual4 p.x p.y p.z p.w q.x q.y q.z q.w

/-- Projective equality is reflexive. -/
theorem projectivelyEqual25_refl (p : Coordinates25) :
    ProjectivelyEqual25 p p := by
  refine ⟨1, by norm_num, ?_, ?_, ?_, ?_⟩ <;> simp

/-- Projective equality is symmetric. -/
theorem projectivelyEqual25_symm {p q : Coordinates25}
    (h : ProjectivelyEqual25 p q) : ProjectivelyEqual25 q p := by
  rcases h with ⟨a, ha, hx, hy, hz, hw⟩
  refine ⟨a⁻¹, inv_ne_zero ha, ?_, ?_, ?_, ?_⟩
  · rw [hx]
    field_simp
  · rw [hy]
    field_simp
  · rw [hz]
    field_simp
  · rw [hw]
    field_simp

/-- Projective equality is transitive. -/
theorem projectivelyEqual25_trans {p q r : Coordinates25}
    (hpq : ProjectivelyEqual25 p q)
    (hqr : ProjectivelyEqual25 q r) : ProjectivelyEqual25 p r := by
  rcases hpq with ⟨a, ha, hx, hy, hz, hw⟩
  rcases hqr with ⟨b, hb, hX, hY, hZ, hW⟩
  refine ⟨a * b, mul_ne_zero ha hb, ?_, ?_, ?_, ?_⟩
  · rw [hx, hX]
    ring
  · rw [hy, hY]
    ring
  · rw [hz, hZ]
    ring
  · rw [hw, hW]
    ring

/-- The order-five transformation respects projective equality. -/
theorem tau25_projectivelyEqual {p q : Coordinates25}
    (h : ProjectivelyEqual25 p q) :
    ProjectivelyEqual25 (tau25 p) (tau25 q) := by
  rcases h with ⟨a, ha, hx, hy, hz, hw⟩
  refine ⟨a, ha, ?_, ?_, ?_, ?_⟩
  · simpa [tau25] using hz
  · simp only [tau25]
    rw [hw, hy]
    ring
  · simp only [tau25]
    rw [hw]
    ring
  · simp only [tau25]
    rw [hx, hy]
    ring

/-- A coordinate vector lies on the canonical complete intersection. -/
def OnCanonical25 (p : Coordinates25) : Prop :=
  canonicalQuadric25 p.x p.y p.z p.w = 0 ∧
    canonicalCubic25 p.x p.y p.z p.w = 0

/-- The canonical quadric is exactly invariant under `tau25`. -/
theorem canonicalQuadric25_tau25 (p : Coordinates25) :
    canonicalQuadric25 (tau25 p).x (tau25 p).y (tau25 p).z (tau25 p).w =
      canonicalQuadric25 p.x p.y p.z p.w := by
  simp only [tau25, canonicalQuadric25]
  ring

/-- The canonical cubic is invariant modulo the canonical quadric:
`C(tau p) = C(p) - z Q(p)`. -/
theorem canonicalCubic25_tau25 (p : Coordinates25) :
    canonicalCubic25 (tau25 p).x (tau25 p).y (tau25 p).z (tau25 p).w =
      canonicalCubic25 p.x p.y p.z p.w -
        p.z * canonicalQuadric25 p.x p.y p.z p.w := by
  simp only [tau25, canonicalCubic25, canonicalQuadric25]
  ring

/-- `tau25` sends canonical points to canonical points. -/
theorem tau25_onCanonical {p : Coordinates25} (hp : OnCanonical25 p) :
    OnCanonical25 (tau25 p) := by
  rcases hp with ⟨hQ, hC⟩
  constructor
  · rw [canonicalQuadric25_tau25, hQ]
  · rw [canonicalCubic25_tau25, hQ, hC]
    ring

/-- Since `tau25` is invertible, membership in the canonical model is
equivalent before and after applying it. -/
theorem onCanonical25_tau25_iff (p : Coordinates25) :
    OnCanonical25 (tau25 p) ↔ OnCanonical25 p := by
  constructor
  · intro hp
    have h2 := tau25_onCanonical hp
    have h3 := tau25_onCanonical h2
    have h4 := tau25_onCanonical h3
    have h5 := tau25_onCanonical h4
    simpa only [tau25_fifth] using h5
  · exact tau25_onCanonical

/-- The order-five automorphism restricted to the canonical complete
intersection. -/
def canonicalTauEquiv25 :
    {p : Coordinates25 // OnCanonical25 p} ≃
      {p : Coordinates25 // OnCanonical25 p} where
  toFun p := ⟨tau25 p.1, tau25_onCanonical p.2⟩
  invFun p :=
    ⟨tau25 (tau25 (tau25 (tau25 p.1))),
      tau25_onCanonical (tau25_onCanonical
        (tau25_onCanonical (tau25_onCanonical p.2)))⟩
  left_inv p := Subtype.ext (tau25_fifth p.1)
  right_inv p := Subtype.ext (tau25_fifth p.1)

/-! ## The five rational cusps form one cycle -/

/-- Cusp `[0:0:0:1]`. -/
def cusp25A : Coordinates25 := ⟨0, 0, 0, 1⟩

/-- Cusp `[0:-1:1:0]`. -/
def cusp25B : Coordinates25 := ⟨0, -1, 1, 0⟩

/-- Cusp `[1:1:0:1]`. -/
def cusp25C : Coordinates25 := ⟨1, 1, 0, 1⟩

/-- Cusp `[0:0:1:0]`. -/
def cusp25D : Coordinates25 := ⟨0, 0, 1, 0⟩

/-- Cusp `[1:0:0:0]`. -/
def cusp25E : Coordinates25 := ⟨1, 0, 0, 0⟩

/-- All five displayed representatives lie on the canonical model. -/
theorem canonical_cusps_on_model :
    OnCanonical25 cusp25A ∧ OnCanonical25 cusp25B ∧
      OnCanonical25 cusp25C ∧ OnCanonical25 cusp25D ∧
      OnCanonical25 cusp25E := by
  norm_num [OnCanonical25, cusp25A, cusp25B, cusp25C, cusp25D, cusp25E,
    canonicalQuadric25, canonicalCubic25]

/-- The first cusp maps to the second, with projective scalar `-1`. -/
theorem tau25_cuspA_to_cuspB :
    tau25 cusp25A = scale25 (-1) cusp25B := by
  ext <;> norm_num [tau25, scale25, cusp25A, cusp25B]

/-- The second cusp maps exactly to the third representative. -/
theorem tau25_cuspB_to_cuspC : tau25 cusp25B = cusp25C := by
  ext <;> norm_num [tau25, cusp25B, cusp25C]

/-- The third cusp maps to the fourth, with projective scalar `-1`. -/
theorem tau25_cuspC_to_cuspD :
    tau25 cusp25C = scale25 (-1) cusp25D := by
  ext <;> norm_num [tau25, scale25, cusp25C, cusp25D]

/-- The fourth cusp maps exactly to the fifth representative. -/
theorem tau25_cuspD_to_cuspE : tau25 cusp25D = cusp25E := by
  ext <;> norm_num [tau25, cusp25D, cusp25E]

/-- The fifth cusp maps exactly back to the first representative. -/
theorem tau25_cuspE_to_cuspA : tau25 cusp25E = cusp25A := by
  ext <;> norm_num [tau25, cusp25E, cusp25A]

/-- Scaling a nonzero homogeneous vector does not change its projective
class. -/
theorem scale25_projectivelyEqual (p : Coordinates25) {a : ℚ} (ha : a ≠ 0) :
    ProjectivelyEqual25 (scale25 a p) p := by
  exact ⟨a, ha, rfl, rfl, rfl, rfl⟩

/-- Projective form of the cusp cycle `A -> B`. -/
theorem tau25_cuspA_projective :
    ProjectivelyEqual25 (tau25 cusp25A) cusp25B := by
  rw [tau25_cuspA_to_cuspB]
  exact scale25_projectivelyEqual cusp25B (by norm_num)

/-- Projective form of the cusp cycle `B -> C`. -/
theorem tau25_cuspB_projective :
    ProjectivelyEqual25 (tau25 cusp25B) cusp25C := by
  rw [tau25_cuspB_to_cuspC]
  exact projectivelyEqual25_refl cusp25C

/-- Projective form of the cusp cycle `C -> D`. -/
theorem tau25_cuspC_projective :
    ProjectivelyEqual25 (tau25 cusp25C) cusp25D := by
  rw [tau25_cuspC_to_cuspD]
  exact scale25_projectivelyEqual cusp25D (by norm_num)

/-- Projective form of the cusp cycle `D -> E`. -/
theorem tau25_cuspD_projective :
    ProjectivelyEqual25 (tau25 cusp25D) cusp25E := by
  rw [tau25_cuspD_to_cuspE]
  exact projectivelyEqual25_refl cusp25E

/-- Projective form of the cusp cycle `E -> A`. -/
theorem tau25_cuspE_projective :
    ProjectivelyEqual25 (tau25 cusp25E) cusp25A := by
  rw [tau25_cuspE_to_cuspA]
  exact projectivelyEqual25_refl cusp25A

/-- The existing five-cusp predicate, packaged for coordinate vectors. -/
def IsCusp25 (p : Coordinates25) : Prop :=
  IsCanonicalCusp25 p.x p.y p.z p.w

/-- The displayed disjunction in `IsCanonicalCusp25` is exactly the five
named cusp representatives. -/
theorem isCusp25_iff (p : Coordinates25) :
    IsCusp25 p ↔
      ProjectivelyEqual25 p cusp25A ∨
      ProjectivelyEqual25 p cusp25B ∨
      ProjectivelyEqual25 p cusp25C ∨
      ProjectivelyEqual25 p cusp25D ∨
      ProjectivelyEqual25 p cusp25E := by
  rfl

/-- `tau25` cyclically permutes the full five-cusp locus. -/
theorem tau25_isCusp {p : Coordinates25} (hp : IsCusp25 p) :
    IsCusp25 (tau25 p) := by
  rw [isCusp25_iff] at hp ⊢
  rcases hp with hpA | hpB | hpC | hpD | hpE
  · exact Or.inr <| Or.inl <|
      projectivelyEqual25_trans (tau25_projectivelyEqual hpA) tau25_cuspA_projective
  · exact Or.inr <| Or.inr <| Or.inl <|
      projectivelyEqual25_trans (tau25_projectivelyEqual hpB) tau25_cuspB_projective
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      projectivelyEqual25_trans (tau25_projectivelyEqual hpC) tau25_cuspC_projective
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      projectivelyEqual25_trans (tau25_projectivelyEqual hpD) tau25_cuspD_projective
  · exact Or.inl <|
      projectivelyEqual25_trans (tau25_projectivelyEqual hpE) tau25_cuspE_projective

/-- Cusp membership is equivalent before and after applying `tau25`. -/
theorem isCusp25_tau25_iff (p : Coordinates25) :
    IsCusp25 (tau25 p) ↔ IsCusp25 p := by
  constructor
  · intro hp
    have h2 := tau25_isCusp hp
    have h3 := tau25_isCusp h2
    have h4 := tau25_isCusp h3
    have h5 := tau25_isCusp h4
    simpa only [tau25_fifth] using h5
  · exact tau25_isCusp

/-! ## Equivariant coordinates on the cyclic augmentation hyperplane -/

/-- Five coordinates carrying the regular cyclic rotation. -/
@[ext]
structure QuinticCoordinates25 where
  a0 : ℚ
  a1 : ℚ
  a2 : ℚ
  a3 : ℚ
  a4 : ℚ
deriving DecidableEq

/-- Cyclic left rotation of five coordinates. -/
def rotateQuintic25 (a : QuinticCoordinates25) : QuinticCoordinates25 :=
  ⟨a.a1, a.a2, a.a3, a.a4, a.a0⟩

/-- Five rotations are the identity. -/
theorem rotateQuintic25_fifth (a : QuinticCoordinates25) :
    rotateQuintic25 (rotateQuintic25 (rotateQuintic25
      (rotateQuintic25 (rotateQuintic25 a)))) = a := by
  ext <;> rfl

/-- Sum of the five cyclic coordinates. -/
def quinticSum25 (a : QuinticCoordinates25) : ℚ :=
  a.a0 + a.a1 + a.a2 + a.a3 + a.a4

/-- The augmentation hyperplane is stable under cyclic rotation. -/
theorem quinticSum25_rotate (a : QuinticCoordinates25) :
    quinticSum25 (rotateQuintic25 a) = quinticSum25 a := by
  simp only [quinticSum25, rotateQuintic25]
  ring

/-- Equivariant orbit coordinates: these are the `x`-coordinates of
`p, tau p, ..., tau^4 p`. -/
def orbitCoordinates25 (p : Coordinates25) : QuinticCoordinates25 :=
  ⟨p.x, p.z, -p.w, p.y - p.x, p.w - p.y - p.z⟩

/-- The orbit-coordinate image lies on the augmentation hyperplane. -/
theorem orbitCoordinates25_sum_zero (p : Coordinates25) :
    quinticSum25 (orbitCoordinates25 p) = 0 := by
  simp only [quinticSum25, orbitCoordinates25]
  ring

/-- In orbit coordinates, `tau25` is exactly cyclic rotation. -/
theorem orbitCoordinates25_tau25 (p : Coordinates25) :
    orbitCoordinates25 (tau25 p) =
      rotateQuintic25 (orbitCoordinates25 p) := by
  ext <;> simp [orbitCoordinates25, tau25, rotateQuintic25]

/-- Reconstruct the four original coordinates from the first four cyclic
coordinates. -/
def reconstructCoordinates25 (a : QuinticCoordinates25) : Coordinates25 :=
  ⟨a.a0, a.a3 + a.a0, a.a1, -a.a2⟩

/-- Reconstruction is a left inverse to the orbit-coordinate map. -/
theorem reconstruct_orbitCoordinates25 (p : Coordinates25) :
    reconstructCoordinates25 (orbitCoordinates25 p) = p := by
  ext <;> simp [reconstructCoordinates25, orbitCoordinates25]

/-- On the augmentation hyperplane, reconstruction is also a right inverse. -/
theorem orbitCoordinates_reconstruct25 {a : QuinticCoordinates25}
    (ha : quinticSum25 a = 0) :
    orbitCoordinates25 (reconstructCoordinates25 a) = a := by
  ext <;> simp [orbitCoordinates25, reconstructCoordinates25]
  simp only [quinticSum25] at ha
  linarith

/-- The orbit-coordinate map is injective. -/
theorem orbitCoordinates25_injective : Function.Injective orbitCoordinates25 := by
  intro p q hpq
  have h := congrArg reconstructCoordinates25 hpq
  simpa only [reconstruct_orbitCoordinates25] using h

/-- The four-dimensional representation is explicitly equivalent to the
sum-zero hyperplane of the five-cycle representation. -/
def orbitHyperplaneEquiv25 :
    Coordinates25 ≃ {a : QuinticCoordinates25 // quinticSum25 a = 0} where
  toFun p := ⟨orbitCoordinates25 p, orbitCoordinates25_sum_zero p⟩
  invFun a := reconstructCoordinates25 a.1
  left_inv := reconstruct_orbitCoordinates25
  right_inv a := by
    apply Subtype.ext
    exact orbitCoordinates_reconstruct25 a.2

/-! ## Explicit invariant polynomials -/

/-- The cyclic adjacent-pair quadratic on the five-cycle representation. -/
def cyclicAdjacent25 (a : QuinticCoordinates25) : ℚ :=
  a.a0 * a.a1 + a.a1 * a.a2 + a.a2 * a.a3 +
    a.a3 * a.a4 + a.a4 * a.a0

/-- The adjacent-pair quadratic is invariant under rotation. -/
theorem cyclicAdjacent25_rotate (a : QuinticCoordinates25) :
    cyclicAdjacent25 (rotateQuintic25 a) = cyclicAdjacent25 a := by
  simp only [cyclicAdjacent25, rotateQuintic25]
  ring

/-- The canonical quadric is the negative adjacent-pair invariant in orbit
coordinates. -/
theorem canonicalQuadric25_eq_neg_cyclicAdjacent (p : Coordinates25) :
    canonicalQuadric25 p.x p.y p.z p.w =
      -cyclicAdjacent25 (orbitCoordinates25 p) := by
  simp only [canonicalQuadric25, cyclicAdjacent25, orbitCoordinates25]
  ring

/-- A linear correction whose coboundary is `5*z`. -/
def cubicCorrection25 (p : Coordinates25) : ℚ :=
  2 * p.x - p.y - 3 * p.z + 2 * p.w

/-- The correction term changes by exactly `5*z` under `tau25`. -/
theorem cubicCorrection25_tau25 (p : Coordinates25) :
    cubicCorrection25 (tau25 p) = cubicCorrection25 p + 5 * p.z := by
  simp only [cubicCorrection25, tau25]
  ring

/-- An exactly invariant cubic representative of the class of the canonical
cubic modulo the canonical quadric. -/
def invariantCubic25 (p : Coordinates25) : ℚ :=
  5 * canonicalCubic25 p.x p.y p.z p.w +
    cubicCorrection25 p * canonicalQuadric25 p.x p.y p.z p.w

/-- The corrected cubic is exactly invariant, not merely invariant modulo the
quadric. -/
theorem invariantCubic25_tau25 (p : Coordinates25) :
    invariantCubic25 (tau25 p) = invariantCubic25 p := by
  rw [invariantCubic25, canonicalCubic25_tau25,
    canonicalQuadric25_tau25, cubicCorrection25_tau25]
  simp only [invariantCubic25]
  ring

/-- On the canonical quadric, vanishing of the corrected invariant cubic is
equivalent to vanishing of the original canonical cubic. -/
theorem invariantCubic25_eq_zero_iff_of_quadric {p : Coordinates25}
    (hQ : canonicalQuadric25 p.x p.y p.z p.w = 0) :
    invariantCubic25 p = 0 ↔ canonicalCubic25 p.x p.y p.z p.w = 0 := by
  simp [invariantCubic25, hQ]

/-- The cyclic product (norm) of the five orbit coordinates. -/
def cyclicNorm25 (a : QuinticCoordinates25) : ℚ :=
  a.a0 * a.a1 * a.a2 * a.a3 * a.a4

/-- The cyclic norm is invariant under rotation. -/
theorem cyclicNorm25_rotate (a : QuinticCoordinates25) :
    cyclicNorm25 (rotateQuintic25 a) = cyclicNorm25 a := by
  simp only [cyclicNorm25, rotateQuintic25]
  ring

/-- Explicit factorization of the orbit norm in the original coordinates. -/
theorem cyclicNorm25_orbitCoordinates (p : Coordinates25) :
    cyclicNorm25 (orbitCoordinates25 p) =
      p.x * p.z * (-p.w) * (p.y - p.x) * (p.w - p.y - p.z) := by
  rfl

/-- The orbit norm is invariant under `tau25`. -/
theorem cyclicNorm25_tau25 (p : Coordinates25) :
    cyclicNorm25 (orbitCoordinates25 (tau25 p)) =
      cyclicNorm25 (orbitCoordinates25 p) := by
  rw [orbitCoordinates25_tau25, cyclicNorm25_rotate]

/-- Three basic homogeneous invariants, of weights two, three, and five. -/
@[ext]
structure BasicInvariants25 where
  quadratic : ℚ
  cubic : ℚ
  quintic : ℚ
deriving DecidableEq

/-- The explicit basic-invariant map for the order-five action. -/
def basicInvariantMap25 (p : Coordinates25) : BasicInvariants25 :=
  ⟨canonicalQuadric25 p.x p.y p.z p.w,
    invariantCubic25 p,
    cyclicNorm25 (orbitCoordinates25 p)⟩

/-- The basic-invariant map is constant on `tau25`-orbits. -/
theorem basicInvariantMap25_tau25 (p : Coordinates25) :
    basicInvariantMap25 (tau25 p) = basicInvariantMap25 p := by
  ext
  · exact canonicalQuadric25_tau25 p
  · exact invariantCubic25_tau25 p
  · exact cyclicNorm25_tau25 p

/-- The canonical quadric has homogeneous weight two. -/
theorem canonicalQuadric25_scale (a : ℚ) (p : Coordinates25) :
    canonicalQuadric25 (scale25 a p).x (scale25 a p).y
      (scale25 a p).z (scale25 a p).w =
      a ^ 2 * canonicalQuadric25 p.x p.y p.z p.w := by
  simp only [scale25, canonicalQuadric25]
  ring

/-- The corrected invariant cubic has homogeneous weight three. -/
theorem invariantCubic25_scale (a : ℚ) (p : Coordinates25) :
    invariantCubic25 (scale25 a p) = a ^ 3 * invariantCubic25 p := by
  simp only [invariantCubic25, cubicCorrection25, scale25,
    canonicalQuadric25, canonicalCubic25]
  ring

/-- Orbit coordinates are homogeneous of degree one. -/
theorem orbitCoordinates25_scale (a : ℚ) (p : Coordinates25) :
    orbitCoordinates25 (scale25 a p) =
      ⟨a * (orbitCoordinates25 p).a0,
       a * (orbitCoordinates25 p).a1,
       a * (orbitCoordinates25 p).a2,
       a * (orbitCoordinates25 p).a3,
       a * (orbitCoordinates25 p).a4⟩ := by
  ext <;> simp [orbitCoordinates25, scale25] <;> ring

/-- The cyclic norm has homogeneous weight five. -/
theorem cyclicNorm25_scale (a : ℚ) (p : Coordinates25) :
    cyclicNorm25 (orbitCoordinates25 (scale25 a p)) =
      a ^ 5 * cyclicNorm25 (orbitCoordinates25 p) := by
  simp only [cyclicNorm25, orbitCoordinates25, scale25]
  ring

/-- On the canonical complete intersection, the invariant map has only its
quintic coordinate left. -/
theorem basicInvariantMap25_of_onCanonical {p : Coordinates25}
    (hp : OnCanonical25 p) :
    basicInvariantMap25 p =
      ⟨0, 0, cyclicNorm25 (orbitCoordinates25 p)⟩ := by
  rcases hp with ⟨hQ, hC⟩
  ext <;> simp [basicInvariantMap25, invariantCubic25, hQ, hC]

end MazurProof.RationalPointsN25QuotientAction
