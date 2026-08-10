import FLT.Assumptions.MazurProof.RationalPointsN25QuotientKummerThreeF81

/-!
# Projective bookkeeping for the characteristic-three Kummer model

The Kummer certificate counts 87 affine pairs `(r,t)`.  This file proves the
two projective corrections structurally:

* the cleared equation has two solutions with `r=0`, whereas the dense Segre
  chart has only `(r,s)=(0,0)`, so the dense chart contains 86 points;
* the two boundary rulings and their corner each contain one curve point.

Consequently the normalized `P¹ × P¹` Segre model has 89 points over `F81`.
All comparisons away from `r=0` are explicit equivalences induced by
`t=r²s`; no two-dimensional finite search is used.
-/

namespace MazurProof.RationalPointsN25QuotientKummerThreeProjective

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientWeilThree
open MazurProof.RationalPointsN25QuotientKummerThree
open MazurProof.RationalPointsN25QuotientKummerThreeF81
open scoped BigOperators

noncomputable section

/-! ## Canonical normalized points over a field -/

/-- First-nonzero homogeneous coordinates using the zero and one of an
actual field. -/
def normalizedCoordinatesThree {K : Type*} [Field K] :
    NormalizedProjective4 K → Coordinates4 K
  | .xChart y z w => ⟨1, y, z, w⟩
  | .yChart z w => ⟨0, 1, z, w⟩
  | .zChart w => ⟨0, 0, 1, w⟩
  | .wChart => ⟨0, 0, 0, 1⟩

/-- The canonical quadric-cubic equations on a first-nonzero projective
representative over an actual characteristic-three field. -/
def IsCanonicalNormalizedThree {K : Type*} [Field K]
    (P : NormalizedProjective4 K) : Prop :=
  canonicalQuadric25Three (normalizedCoordinatesThree P) = 0 ∧
    canonicalCubic25Three (normalizedCoordinatesThree P) = 0

/-- The executable `F81` chart coordinates are the same coordinates supplied
by its transported field structure. -/
theorem ternaryCoordinates_f81_eq (P : NormalizedProjective4 F81) :
    ternaryCoordinates f81Operations P = normalizedCoordinatesThree P := by
  cases P <;> simp [ternaryCoordinates, normalizedCoordinatesThree,
    f81Operations_zero_eq, f81Operations_one_eq]

/-- The executable `F81` quadric evaluator is the actual field polynomial. -/
theorem canonicalQuadric25Ternary_f81_eq (P : Coordinates4 F81) :
    canonicalQuadric25Ternary f81Operations P =
      canonicalQuadric25Three P := by
  unfold canonicalQuadric25Ternary canonicalQuadric25Three
  rw [f81Operations_add_eq, f81Operations_add_eq,
    f81Operations_neg_eq, f81Operations_mul_eq,
    f81Operations_neg_eq, f81Operations_mul_eq,
    f81Operations_add_eq, f81Operations_mul_eq,
    f81Operations_add_eq, f81Operations_mul_eq,
    f81Operations_mul_eq]
  ring

/-- The executable `F81` cubic evaluator is the actual field polynomial. -/
theorem canonicalCubic25Ternary_f81_eq (P : Coordinates4 F81) :
    canonicalCubic25Ternary f81Operations P =
      canonicalCubic25Three P := by
  unfold canonicalCubic25Ternary canonicalCubic25Three
  repeat' rw [f81Operations_add_eq]
  repeat' rw [f81Operations_neg_eq]
  repeat' rw [f81Operations_mul_eq]
  ring

/-- The old executable normalized-point predicate has exactly the semantic
meaning asserted by the field-valued canonical equations. -/
theorem isCanonicalNormalized25Ternary_f81_iff
    (P : NormalizedProjective4 F81) :
    IsCanonicalNormalized25Ternary f81Operations P ↔
      IsCanonicalNormalizedThree P := by
  unfold IsCanonicalNormalized25Ternary IsCanonicalNormalizedThree
  rw [ternaryCoordinates_f81_eq]
  dsimp only
  rw [canonicalQuadric25Ternary_f81_eq,
    canonicalCubic25Ternary_f81_eq, f81Operations_zero_eq]

/-! ## Projectivizing the eigenbasis -/

/-- The zero vector in four homogeneous field coordinates. -/
def zeroCoordinatesThree {K : Type*} [Zero K] : Coordinates4 K :=
  ⟨0, 0, 0, 0⟩

/-- Scalar multiplication of four homogeneous coordinates. -/
def scaleCoordinatesThree {K : Type*} [Mul K]
    (a : K) (P : Coordinates4 K) : Coordinates4 K :=
  ⟨a * P.x, a * P.y, a * P.z, a * P.w⟩

/-- Normalize a homogeneous vector by its first nonzero coordinate.  The
zero vector is sent to `wChart`; all uses below separately prove nonvanishing. -/
def normalizeCoordinatesThree {K : Type*} [Field K] [DecidableEq K]
    (P : Coordinates4 K) : NormalizedProjective4 K :=
  if _hx : P.x ≠ 0 then
    .xChart (P.y / P.x) (P.z / P.x) (P.w / P.x)
  else if _hy : P.y ≠ 0 then
    .yChart (P.z / P.y) (P.w / P.y)
  else if _hz : P.z ≠ 0 then
    .zChart (P.w / P.z)
  else .wChart

/-- A first-nonzero normalized projective representative is never the zero
homogeneous vector. -/
theorem normalizedCoordinatesThree_ne_zero
    {K : Type*} [Field K] (P : NormalizedProjective4 K) :
    normalizedCoordinatesThree P ≠ zeroCoordinatesThree := by
  cases P <;> simp [normalizedCoordinatesThree, zeroCoordinatesThree,
    Coordinates4.mk.injEq]

/-- Normalizing a nonzero scalar multiple of an already normalized vector
returns the original projective chart. -/
theorem normalize_scale_normalized
    {K : Type*} [Field K] [DecidableEq K]
    (P : NormalizedProjective4 K) {a : K} (ha : a ≠ 0) :
    normalizeCoordinatesThree
      (scaleCoordinatesThree a (normalizedCoordinatesThree P)) = P := by
  cases P with
  | xChart y z w =>
      simp [normalizeCoordinatesThree, scaleCoordinatesThree,
        normalizedCoordinatesThree, ha]
  | yChart z w =>
      simp [normalizeCoordinatesThree, scaleCoordinatesThree,
        normalizedCoordinatesThree, ha]
  | zChart w =>
      simp [normalizeCoordinatesThree, scaleCoordinatesThree,
        normalizedCoordinatesThree, ha]
  | wChart =>
      simp [normalizeCoordinatesThree, scaleCoordinatesThree,
        normalizedCoordinatesThree]

/-- Normalization rescales every nonzero homogeneous vector by a nonzero
field element. -/
theorem normalizeCoordinatesThree_spec
    {K : Type*} [Field K] [DecidableEq K] {P : Coordinates4 K}
    (hP : P ≠ zeroCoordinatesThree) :
    ∃ a : K, a ≠ 0 ∧
      normalizedCoordinatesThree (normalizeCoordinatesThree P) =
        scaleCoordinatesThree a P := by
  by_cases hx : P.x ≠ 0
  · refine ⟨P.x⁻¹, inv_ne_zero hx, ?_⟩
    simp [normalizeCoordinatesThree, hx, normalizedCoordinatesThree,
      scaleCoordinatesThree, div_eq_mul_inv, mul_comm]
  · by_cases hy : P.y ≠ 0
    · have hx0 : P.x = 0 := not_ne_iff.mp hx
      refine ⟨P.y⁻¹, inv_ne_zero hy, ?_⟩
      simp [normalizeCoordinatesThree, hy, normalizedCoordinatesThree,
        scaleCoordinatesThree, hx0, div_eq_mul_inv, mul_comm]
    · by_cases hz : P.z ≠ 0
      · have hx0 : P.x = 0 := not_ne_iff.mp hx
        have hy0 : P.y = 0 := not_ne_iff.mp hy
        refine ⟨P.z⁻¹, inv_ne_zero hz, ?_⟩
        simp [normalizeCoordinatesThree, hz, normalizedCoordinatesThree,
          scaleCoordinatesThree, hx0, hy0, div_eq_mul_inv, mul_comm]
      · have hw : P.w ≠ 0 := by
          have hx0 : P.x = 0 := not_ne_iff.mp hx
          have hy0 : P.y = 0 := not_ne_iff.mp hy
          have hz0 : P.z = 0 := not_ne_iff.mp hz
          intro hw
          apply hP
          rcases P with ⟨x, y, z, w⟩
          simp only at hx0 hy0 hz0 hw
          subst x
          subst y
          subst z
          subst w
          rfl
        have hx0 : P.x = 0 := not_ne_iff.mp hx
        have hy0 : P.y = 0 := not_ne_iff.mp hy
        have hz0 : P.z = 0 := not_ne_iff.mp hz
        refine ⟨P.w⁻¹, inv_ne_zero hw, ?_⟩
        simp [normalizeCoordinatesThree, normalizedCoordinatesThree,
          scaleCoordinatesThree, hx0, hy0, hz0, hw]

/-- The inverse eigenbasis commutes with homogeneous scalar multiplication. -/
theorem canonicalCoordinatesFromEigen_scale
    {K : Type*} [Field K] (e a : K) (U : Coordinates4 K) :
    canonicalCoordinatesFromEigen25Three e
        (scaleCoordinatesThree a U).x (scaleCoordinatesThree a U).y
        (scaleCoordinatesThree a U).z (scaleCoordinatesThree a U).w =
      scaleCoordinatesThree a
        (canonicalCoordinatesFromEigen25Three e U.x U.y U.z U.w) := by
  rcases U with ⟨u1, u2, u3, u4⟩
  simp only [scaleCoordinatesThree, canonicalCoordinatesFromEigen25Three,
    Coordinates4.mk.injEq]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The forward eigenbasis commutes with homogeneous scalar multiplication. -/
theorem canonicalEigenCoordinates_scale
    {K : Type*} [Field K] (e a : K) (P : Coordinates4 K) :
    canonicalEigenCoordinates25Three e (scaleCoordinatesThree a P) =
      scaleCoordinatesThree a (canonicalEigenCoordinates25Three e P) := by
  rcases P with ⟨x, y, z, w⟩
  simp only [scaleCoordinatesThree, canonicalEigenCoordinates25Three,
    Coordinates4.mk.injEq]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The inverse eigenbasis sends a nonzero vector to a nonzero vector. -/
theorem canonicalCoordinatesFromEigen_ne_zero
    {K : Type*} [Field K] [CharP K 3] {e : K}
    (he : IsCyclotomicFive25Three e) {U : Coordinates4 K}
    (hU : U ≠ zeroCoordinatesThree) :
    canonicalCoordinatesFromEigen25Three e U.x U.y U.z U.w ≠
      zeroCoordinatesThree := by
  intro h
  have h' := congrArg (canonicalEigenCoordinates25Three e) h
  have hleft := canonicalEigenCoordinates_fromEigen
    (e := e) (u₁ := U.x) (u₂ := U.y) (u₃ := U.z) (u₄ := U.w) he
  apply hU
  rw [hleft] at h'
  rcases U with ⟨u1, u2, u3, u4⟩
  simpa [zeroCoordinatesThree, canonicalEigenCoordinates25Three] using h'

/-- The forward eigenbasis sends a nonzero vector to a nonzero vector. -/
theorem canonicalEigenCoordinates_ne_zero
    {K : Type*} [Field K] [CharP K 3] {e : K}
    (he : IsCyclotomicFive25Three e) {P : Coordinates4 K}
    (hP : P ≠ zeroCoordinatesThree) :
    canonicalEigenCoordinates25Three e P ≠ zeroCoordinatesThree := by
  intro h
  have h' := congrArg (fun U : Coordinates4 K =>
    canonicalCoordinatesFromEigen25Three e U.x U.y U.z U.w) h
  have hleft := canonicalCoordinatesFromEigen_eigen (e := e) (P := P) he
  apply hP
  rw [hleft] at h'
  simpa [zeroCoordinatesThree, canonicalCoordinatesFromEigen25Three] using h'

/-- Apply the inverse eigenbasis and normalize the resulting canonical
homogeneous vector. -/
def eigenToCanonicalProjective
    {K : Type*} [Field K] [DecidableEq K] (e : K)
    (P : NormalizedProjective4 K) : NormalizedProjective4 K :=
  normalizeCoordinatesThree
    (canonicalCoordinatesFromEigen25Three e
      (normalizedCoordinatesThree P).x (normalizedCoordinatesThree P).y
      (normalizedCoordinatesThree P).z (normalizedCoordinatesThree P).w)

/-- Apply the forward eigenbasis and normalize the resulting eigenvector. -/
def canonicalToEigenProjective
    {K : Type*} [Field K] [DecidableEq K] (e : K)
    (P : NormalizedProjective4 K) : NormalizedProjective4 K :=
  normalizeCoordinatesThree
    (canonicalEigenCoordinates25Three e (normalizedCoordinatesThree P))

/-- The mutually inverse eigenbasis matrices induce a genuine equivalence on
first-nonzero normalized projective coordinates. -/
def eigenCanonicalProjectiveEquiv
    {K : Type*} [Field K] [CharP K 3] [DecidableEq K]
    (e : K) (he : IsCyclotomicFive25Three e) :
    NormalizedProjective4 K ≃ NormalizedProjective4 K where
  toFun := eigenToCanonicalProjective e
  invFun := canonicalToEigenProjective e
  left_inv P := by
    unfold eigenToCanonicalProjective canonicalToEigenProjective
    let U := normalizedCoordinatesThree P
    have hU : U ≠ zeroCoordinatesThree :=
      normalizedCoordinatesThree_ne_zero P
    have hV : canonicalCoordinatesFromEigen25Three e U.x U.y U.z U.w ≠
        zeroCoordinatesThree := canonicalCoordinatesFromEigen_ne_zero he hU
    rcases normalizeCoordinatesThree_spec hV with ⟨a, ha, hspec⟩
    rw [hspec, canonicalEigenCoordinates_scale,
      canonicalEigenCoordinates_fromEigen he]
    exact normalize_scale_normalized P ha
  right_inv P := by
    unfold eigenToCanonicalProjective canonicalToEigenProjective
    let V := normalizedCoordinatesThree P
    have hV : V ≠ zeroCoordinatesThree :=
      normalizedCoordinatesThree_ne_zero P
    have hU : canonicalEigenCoordinates25Three e V ≠ zeroCoordinatesThree :=
      canonicalEigenCoordinates_ne_zero he hV
    rcases normalizeCoordinatesThree_spec hU with ⟨a, ha, hspec⟩
    rw [hspec, canonicalCoordinatesFromEigen_scale,
      canonicalCoordinatesFromEigen_eigen he]
    exact normalize_scale_normalized P ha

/-! ## Dense and Kummer solution types -/

section Generic

variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

/-- Affine solutions `(r,s)` on the dense Segre chart. -/
abbrev DenseSolutions (e : K) :=
  {p : K × K // canonicalDenseSegreCubic25Three e p.1 p.2 = 0}

/-- Solutions `(r,t)` of the denominator-cleared Kummer equation. -/
abbrev KummerSolutions (e : K) :=
  {p : K × K // canonicalKummerPolynomial25Three e p.1 p.2 = 0}

/-- Dense-chart solutions on the special fibre `r=0`. -/
abbrev DenseZeroSolutions (e : K) :=
  {p : K × K //
    canonicalDenseSegreCubic25Three e p.1 p.2 = 0 ∧ p.1 = 0}

/-- Dense-chart solutions away from `r=0`. -/
abbrev DenseNonzeroSolutions (e : K) :=
  {p : K × K //
    canonicalDenseSegreCubic25Three e p.1 p.2 = 0 ∧ p.1 ≠ 0}

/-- Kummer solutions on the special fibre `r=0`. -/
abbrev KummerZeroSolutions (e : K) :=
  {p : K × K //
    canonicalKummerPolynomial25Three e p.1 p.2 = 0 ∧ p.1 = 0}

/-- Kummer solutions away from `r=0`. -/
abbrev KummerNonzeroSolutions (e : K) :=
  {p : K × K //
    canonicalKummerPolynomial25Three e p.1 p.2 = 0 ∧ p.1 ≠ 0}

/-- Split the dense solution set according to whether `r` vanishes. -/
def densePartitionEquiv (e : K) :
    DenseSolutions e ≃ DenseZeroSolutions e ⊕ DenseNonzeroSolutions e where
  toFun p := if h : p.1.1 = 0 then
      Sum.inl ⟨p.1, p.2, h⟩
    else Sum.inr ⟨p.1, p.2, h⟩
  invFun p := p.elim (fun q => ⟨q.1, q.2.1⟩) (fun q => ⟨q.1, q.2.1⟩)
  left_inv p := by
    dsimp
    split <;> rfl
  right_inv p := by
    rcases p with p | p
    · simp [p.2.2]
    · simp [p.2.2]

/-- Split the Kummer solution set according to whether `r` vanishes. -/
def kummerPartitionEquiv (e : K) :
    KummerSolutions e ≃ KummerZeroSolutions e ⊕ KummerNonzeroSolutions e where
  toFun p := if h : p.1.1 = 0 then
      Sum.inl ⟨p.1, p.2, h⟩
    else Sum.inr ⟨p.1, p.2, h⟩
  invFun p := p.elim (fun q => ⟨q.1, q.2.1⟩) (fun q => ⟨q.1, q.2.1⟩)
  left_inv p := by
    dsimp
    split <;> rfl
  right_inv p := by
    rcases p with p | p
    · simp [p.2.2]
    · simp [p.2.2]

/-- The dense zero fibre consists only of `(r,s)=(0,0)`. -/
def denseZeroEquivUnit {e : K} (he : IsCyclotomicFive25Three e) :
    DenseZeroSolutions e ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(0, 0), (denseSegre_at_zero he).2 rfl, rfl⟩
  left_inv p := by
    rcases p with ⟨⟨r, s⟩, hcurve, hr⟩
    change r = 0 at hr
    subst r
    change canonicalDenseSegreCubic25Three e 0 s = 0 at hcurve
    have hs := (denseSegre_at_zero he).1 hcurve
    change s = 0 at hs
    subst s
    rfl
  right_inv p := by cases p; rfl

/-- The cleared Kummer zero fibre consists of `t=0` and the one extraneous
parameter introduced by clearing `r⁴`. -/
def kummerZeroEquivBool {e : K} (he : IsCyclotomicFive25Three e) :
    KummerZeroSolutions e ≃ Bool where
  toFun p := if p.1.2 = 0 then false else true
  invFun b := if b then
      ⟨(0, extraneousKummerParameter25Three e),
        (kummer_zero_fibre_iff he).2 (Or.inr rfl), rfl⟩
    else ⟨(0, 0), (kummer_zero_fibre_iff he).2 (Or.inl rfl), rfl⟩
  left_inv p := by
    rcases p with ⟨⟨r, t⟩, hcurve, hr⟩
    change r = 0 at hr
    subst r
    change canonicalKummerPolynomial25Three e 0 t = 0 at hcurve
    rcases (kummer_zero_fibre_iff he).1 hcurve with ht | ht
    · change t = 0 at ht
      subst t
      simp
    · change t = extraneousKummerParameter25Three e at ht
      subst t
      simp [extraneousKummerParameter25Three_ne_zero he]
  right_inv b := by
    cases b <;> simp [extraneousKummerParameter25Three_ne_zero he]

/-- Away from `r=0`, the substitution `t=r²s` is an equivalence between
dense Segre solutions and Kummer solutions. -/
def denseNonzeroEquivKummerNonzero (e : K) :
    DenseNonzeroSolutions e ≃ KummerNonzeroSolutions e where
  toFun p := ⟨(p.1.1, p.1.1 ^ 2 * p.1.2), by
    constructor
    · have h := denseSegre_to_kummer_identity e p.1.1 p.1.2
      rw [p.2.1, mul_zero] at h
      exact h.symm
    · exact p.2.2⟩
  invFun p := ⟨(p.1.1, p.1.2 / p.1.1 ^ 2), by
    constructor
    · exact (denseSegre_eq_zero_iff_kummer e p.2.2).2 p.2.1
    · exact p.2.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact mul_div_cancel_left₀ p.1.2 (pow_ne_zero 2 p.2.2)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact mul_div_cancel₀ p.1.2 (pow_ne_zero 2 p.2.2)

/-- Re-index Kummer pairs by the quotient parameter `t`, exposing the root
fibre used by the one-dimensional certificate. -/
def kummerSolutionsEquivSigma (e : K) :
    KummerSolutions e ≃
      (Σ t : K, {r : K // canonicalKummerPolynomial25Three e r t = 0}) where
  toFun p := ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
  invFun p := ⟨(p.2.1, p.1), p.2.2⟩
  left_inv p := rfl
  right_inv p := by rcases p with ⟨t, r, h⟩; rfl

/-! ## Normalized charts on the Segre quadric -/

/-- First-nonzero charts on the two factors of the Segre quadric.  The four
constructors represent the dense chart, the two boundary rulings, and their
intersection. -/
inductive NormalizedSegrePoint (K : Type*) where
  | dense (r s : K)
  | leftBoundary (s : K)
  | rightBoundary (r : K)
  | corner
deriving DecidableEq, Fintype

/-- Map the four normalized Segre charts through the inverse eigenbasis to
canonical homogeneous coordinates. -/
def normalizedSegreCoordinates (e : K) :
    NormalizedSegrePoint K → Coordinates4 K
  | .dense r s => canonicalSegreCoordinates25Three e 1 r 1 s
  | .leftBoundary s => canonicalSegreCoordinates25Three e 0 1 1 s
  | .rightBoundary r => canonicalSegreCoordinates25Three e 1 r 0 1
  | .corner => canonicalSegreCoordinates25Three e 0 1 0 1

/-- The four-term cubic predicate on a normalized Segre chart. -/
def IsNormalizedSegreCurve (e : K) : NormalizedSegrePoint K → Prop
  | .dense r s => canonicalDenseSegreCubic25Three e r s = 0
  | .leftBoundary s => canonicalSegreCubic25Three e 0 1 1 s = 0
  | .rightBoundary r => canonicalSegreCubic25Three e 1 r 0 1 = 0
  | .corner => canonicalSegreCubic25Three e 0 1 0 1 = 0

/-- Normalized projective Segre parameters satisfying the curve equation. -/
abbrev SegreSolutions (e : K) :=
  {p : NormalizedSegrePoint K // IsNormalizedSegreCurve e p}

/-- Curve points on the left boundary ruling. -/
abbrev LeftBoundarySolutions (e : K) :=
  {s : K // canonicalSegreCubic25Three e 0 1 1 s = 0}

/-- Curve points on the right boundary ruling. -/
abbrev RightBoundarySolutions (e : K) :=
  {r : K // canonicalSegreCubic25Three e 1 r 0 1 = 0}

/-- The normalized Segre solution set is the disjoint union of its dense
chart, two boundary rulings, and their corner. -/
def segreSolutionsEquivCharts (e : K) : SegreSolutions e ≃
    DenseSolutions e ⊕
      LeftBoundarySolutions e ⊕ RightBoundarySolutions e ⊕ Unit where
  toFun p := by
    rcases p with ⟨p, hp⟩
    cases p with
    | dense r s => exact Sum.inl ⟨(r, s), hp⟩
    | leftBoundary s => exact Sum.inr (Sum.inl ⟨s, hp⟩)
    | rightBoundary r => exact Sum.inr (Sum.inr (Sum.inl ⟨r, hp⟩))
    | corner => exact Sum.inr (Sum.inr (Sum.inr ()))
  invFun p := by
    rcases p with p | p
    · exact ⟨.dense p.1.1 p.1.2, p.2⟩
    · rcases p with p | p
      · exact ⟨.leftBoundary p.1, p.2⟩
      · rcases p with p | p
        · exact ⟨.rightBoundary p.1, p.2⟩
        · exact ⟨.corner, segre_boundary_corner e⟩
  left_inv p := by
    rcases p with ⟨p, hp⟩
    cases p <;> rfl
  right_inv p := by
    rcases p with p | p
    · rfl
    · rcases p with p | p
      · rfl
      · rcases p with p | p
        · rfl
        · cases p
          rfl

/-- The left boundary ruling contributes one solution. -/
def leftBoundaryEquivUnit {e : K} (he : IsCyclotomicFive25Three e) :
    LeftBoundarySolutions e ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨0, (segre_boundary_a_zero he).2 rfl⟩
  left_inv p := by
    rcases p with ⟨s, hs⟩
    have h := (segre_boundary_a_zero he).1 hs
    subst s
    rfl
  right_inv p := by cases p; rfl

/-- The right boundary ruling contributes one solution. -/
def rightBoundaryEquivUnit {e : K} (he : IsCyclotomicFive25Three e) :
    RightBoundarySolutions e ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨0, (segre_boundary_c_zero he).2 rfl⟩
  left_inv p := by
    rcases p with ⟨r, hr⟩
    have h := (segre_boundary_c_zero he).1 hr
    subst r
    rfl
  right_inv p := by cases p; rfl

end Generic

/-! ## The `F81` projective count -/

/-- The actual Kummer solution type has cardinality 87, by summing the
proved fifth-power root cardinalities over all quotient parameters. -/
theorem f81_kummer_solutions_card :
    Nat.card (KummerSolutions f81FifthRoot25) = 87 := by
  calc
    Nat.card (KummerSolutions f81FifthRoot25) =
        Nat.card (Σ t : F81,
          {r : F81 // canonicalKummerPolynomial25Three f81FifthRoot25 r t = 0}) :=
      Nat.card_congr (kummerSolutionsEquivSigma f81FifthRoot25)
    _ = ∑ t : F81,
        Nat.card {r : F81 //
          canonicalKummerPolynomial25Three f81FifthRoot25 r t = 0} :=
      Nat.card_sigma
    _ = 87 := f81_kummer_actual_fiber_sum

/-- Removing the single extraneous zero-fibre Kummer solution leaves 86
points on the dense Segre chart. -/
theorem f81_dense_solutions_card :
    Nat.card (DenseSolutions f81FifthRoot25) = 86 := by
  have hdense : Nat.card (DenseSolutions f81FifthRoot25) =
      1 + Nat.card (DenseNonzeroSolutions f81FifthRoot25) := by
    calc
      Nat.card (DenseSolutions f81FifthRoot25) =
          Nat.card (DenseZeroSolutions f81FifthRoot25 ⊕
            DenseNonzeroSolutions f81FifthRoot25) :=
        Nat.card_congr (densePartitionEquiv f81FifthRoot25)
      _ = Nat.card (DenseZeroSolutions f81FifthRoot25) +
          Nat.card (DenseNonzeroSolutions f81FifthRoot25) := Nat.card_sum
      _ = 1 + Nat.card (DenseNonzeroSolutions f81FifthRoot25) := by
        rw [Nat.card_congr (denseZeroEquivUnit f81FifthRoot25_isCyclotomic)]
        simp
  have hkummer : Nat.card (KummerSolutions f81FifthRoot25) =
      2 + Nat.card (KummerNonzeroSolutions f81FifthRoot25) := by
    calc
      Nat.card (KummerSolutions f81FifthRoot25) =
          Nat.card (KummerZeroSolutions f81FifthRoot25 ⊕
            KummerNonzeroSolutions f81FifthRoot25) :=
        Nat.card_congr (kummerPartitionEquiv f81FifthRoot25)
      _ = Nat.card (KummerZeroSolutions f81FifthRoot25) +
          Nat.card (KummerNonzeroSolutions f81FifthRoot25) := Nat.card_sum
      _ = 2 + Nat.card (KummerNonzeroSolutions f81FifthRoot25) := by
        rw [Nat.card_congr (kummerZeroEquivBool f81FifthRoot25_isCyclotomic)]
        simp
  have hnz : Nat.card (DenseNonzeroSolutions f81FifthRoot25) =
      Nat.card (KummerNonzeroSolutions f81FifthRoot25) :=
    Nat.card_congr (denseNonzeroEquivKummerNonzero f81FifthRoot25)
  rw [hdense, hnz]
  rw [f81_kummer_solutions_card] at hkummer
  omega

/-- The normalized projective Segre model has 86 dense points and three
boundary points, hence 89 points in total. -/
theorem f81_segre_solutions_card :
    Nat.card (SegreSolutions f81FifthRoot25) = 89 := by
  calc
    Nat.card (SegreSolutions f81FifthRoot25) =
        Nat.card (DenseSolutions f81FifthRoot25 ⊕
          LeftBoundarySolutions f81FifthRoot25 ⊕
          RightBoundarySolutions f81FifthRoot25 ⊕ Unit) :=
      Nat.card_congr (segreSolutionsEquivCharts f81FifthRoot25)
    _ = Nat.card (DenseSolutions f81FifthRoot25) +
        Nat.card (LeftBoundarySolutions f81FifthRoot25) +
        Nat.card (RightBoundarySolutions f81FifthRoot25) +
        Nat.card Unit := by
      simp only [Nat.card_sum, Nat.add_assoc]
    _ = 86 + 1 + 1 + 1 := by
      rw [f81_dense_solutions_card,
        Nat.card_congr (leftBoundaryEquivUnit f81FifthRoot25_isCyclotomic),
        Nat.card_congr (rightBoundaryEquivUnit f81FifthRoot25_isCyclotomic)]
      simp
    _ = 89 := by norm_num

/-! ## Restricting the projective eigenbasis to the curve

The preceding count lives naturally on the four normalized charts of
`P¹ × P¹`.  This final structural layer identifies those charts with the
normalized determinant quadric in eigen-coordinates, restricts the
projective eigenbasis equivalence to the cubic equation, and thereby
transports the count to the stored canonical quadric-cubic model.
-/

section CanonicalRestriction

variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

/-- The four Segre charts as normalized eigen-coordinates.  They are the
rank-one matrices `(ac,ad;bc,bd)` after normalizing the first nonzero entry
of the two projective factors. -/
def normalizedSegreEigenPoint :
    NormalizedSegrePoint K → NormalizedProjective4 K
  | .dense r s => .xChart s r (r * s)
  | .leftBoundary s => .zChart s
  | .rightBoundary r => .yChart 0 r
  | .corner => .wChart

/-- The determinant equation `u₂u₃=u₁u₄` on a first-nonzero normalized
eigenvector.  This is the diagonalized canonical quadric. -/
def IsNormalizedEigenQuadric (P : NormalizedProjective4 K) : Prop :=
  let U := normalizedCoordinatesThree P
  U.y * U.z - U.x * U.w = 0

/-- The normalized Segre charts parametrize the normalized determinant
quadric bijectively.  The inverse reads off the dense chart, then the two
boundary rulings, with the determinant equation removing the redundant
coordinate in each case. -/
def normalizedSegreEquivEigenQuadric :
    NormalizedSegrePoint K ≃
      {P : NormalizedProjective4 K // IsNormalizedEigenQuadric P} where
  toFun p := by
    refine ⟨normalizedSegreEigenPoint p, ?_⟩
    cases p <;>
      simp [normalizedSegreEigenPoint, IsNormalizedEigenQuadric,
        normalizedCoordinatesThree]
    all_goals ring
  invFun P := by
    rcases P with ⟨P, hP⟩
    cases P with
    | xChart y z w => exact .dense z y
    | yChart z w => exact .rightBoundary w
    | zChart w => exact .leftBoundary w
    | wChart => exact .corner
  left_inv p := by
    cases p <;> rfl
  right_inv P := by
    rcases P with ⟨P, hP⟩
    apply Subtype.ext
    cases P with
    | xChart y z w =>
        change y * z - 1 * w = 0 at hP
        simp only [normalizedSegreEigenPoint]
        congr
        linear_combination hP
    | yChart z w =>
        change 1 * z - 0 * w = 0 at hP
        have hz : z = 0 := by simpa using hP
        subst z
        rfl
    | zChart w => rfl
    | wChart => rfl

omit [CharP K 3] [DecidableEq K] in
/-- Scaling a homogeneous vector multiplies the canonical quadric by the
square of the scalar.  This is the projective invariance needed after
first-nonzero normalization. -/
theorem canonicalQuadric25Three_scale (a : K) (P : Coordinates4 K) :
    canonicalQuadric25Three (scaleCoordinatesThree a P) =
      a ^ 2 * canonicalQuadric25Three P := by
  rcases P with ⟨x, y, z, w⟩
  simp only [scaleCoordinatesThree, canonicalQuadric25Three]
  ring

omit [CharP K 3] [DecidableEq K] in
/-- Scaling a homogeneous vector multiplies the canonical cubic by the
cube of the scalar.  Hence its zero locus is unchanged by projective
normalization through a nonzero scalar. -/
theorem canonicalCubic25Three_scale (a : K) (P : Coordinates4 K) :
    canonicalCubic25Three (scaleCoordinatesThree a P) =
      a ^ 3 * canonicalCubic25Three P := by
  rcases P with ⟨x, y, z, w⟩
  simp only [scaleCoordinatesThree, canonicalCubic25Three]
  ring

/-- The curve in normalized eigen-coordinates: the determinant quadric
together with the canonical cubic pulled back through the inverse
eigenbasis. -/
def IsNormalizedEigenCurve (e : K)
    (P : NormalizedProjective4 K) : Prop :=
  let U := normalizedCoordinatesThree P
  U.y * U.z - U.x * U.w = 0 ∧
    canonicalCubic25Three
      (canonicalCoordinatesFromEigen25Three e U.x U.y U.z U.w) = 0

/-- Projectivizing the inverse eigenbasis transports the determinant-cubic
curve exactly to the normalized canonical quadric-cubic intersection.
The only scalars introduced are the nonzero normalization scalar, the
nonzero quadric multiplier, and their homogeneous powers. -/
theorem isNormalizedEigenCurve_iff_canonical
    (e : K) (he : IsCyclotomicFive25Three e)
    (P : NormalizedProjective4 K) :
    IsNormalizedEigenCurve e P ↔
      IsCanonicalNormalizedThree (eigenToCanonicalProjective e P) := by
  let U := normalizedCoordinatesThree P
  let V := canonicalCoordinatesFromEigen25Three e U.x U.y U.z U.w
  have hU : U ≠ zeroCoordinatesThree :=
    normalizedCoordinatesThree_ne_zero P
  have hV : V ≠ zeroCoordinatesThree :=
    canonicalCoordinatesFromEigen_ne_zero he hU
  rcases normalizeCoordinatesThree_spec hV with ⟨a, ha, hspec⟩
  have hcoords :
      normalizedCoordinatesThree (eigenToCanonicalProjective e P) =
        scaleCoordinatesThree a V := by
    exact hspec
  have hquad :
      canonicalQuadric25Three
          (normalizedCoordinatesThree (eigenToCanonicalProjective e P)) = 0 ↔
        U.y * U.z - U.x * U.w = 0 := by
    rw [hcoords, canonicalQuadric25Three_scale,
      canonicalQuadric25_fromEigen he]
    simp [ha, canonicalSegreQuadricScalar25Three_ne_zero he]
  have hcubic :
      canonicalCubic25Three
          (normalizedCoordinatesThree (eigenToCanonicalProjective e P)) = 0 ↔
        canonicalCubic25Three V = 0 := by
    rw [hcoords, canonicalCubic25Three_scale]
    simp [ha]
  unfold IsNormalizedEigenCurve IsCanonicalNormalizedThree
  change (U.y * U.z - U.x * U.w = 0 ∧ canonicalCubic25Three V = 0) ↔ _
  rw [hquad, hcubic]

omit [DecidableEq K] in
/-- On every rank-one eigenvector, vanishing of the pulled-back canonical
cubic is equivalent to vanishing of the four-term Segre cubic.  The
comparison scalar `e³+1` is nonzero on the fifth-cyclotomic locus. -/
theorem canonicalCubic25_fromEigen_eq_zero_iff_segre
    {e a b c d : K} (he : IsCyclotomicFive25Three e) :
    canonicalCubic25Three
        (canonicalCoordinatesFromEigen25Three e
          (a * c) (a * d) (b * c) (b * d)) = 0 ↔
      canonicalSegreCubic25Three e a b c d = 0 := by
  have h := canonicalCubic25_segre
    (e := e) (a := a) (b := b) (c := c) (d := d) he
  change canonicalCubic25Three
      (canonicalCoordinatesFromEigen25Three e
        (a * c) (a * d) (b * c) (b * d)) =
    (e ^ 3 + 1) * canonicalSegreCubic25Three e a b c d at h
  rw [h]
  simp [cyclotomicFive25Three_cubicScalar_ne_zero he]

omit [DecidableEq K] in
/-- The normalized four-chart Segre curve is exactly the determinant-cubic
curve in normalized eigen-coordinates.  Each chart is a rank-one matrix;
the determinant vanishes identically and the preceding scalar comparison
handles the cubic. -/
theorem isNormalizedSegreCurve_iff_eigenCurve
    {e : K} (he : IsCyclotomicFive25Three e)
    (p : NormalizedSegrePoint K) :
    IsNormalizedSegreCurve e p ↔
      IsNormalizedEigenCurve e (normalizedSegreEigenPoint p) := by
  cases p with
  | dense r s =>
      have hc := canonicalCubic25_fromEigen_eq_zero_iff_segre
        (e := e) (a := 1) (b := r) (c := 1) (d := s) he
      change canonicalSegreCubic25Three e 1 r 1 s = 0 ↔
        s * r - 1 * (r * s) = 0 ∧
          canonicalCubic25Three
            (canonicalCoordinatesFromEigen25Three e 1 s r (r * s)) = 0
      constructor
      · intro h
        exact ⟨by ring, by simpa using hc.mpr h⟩
      · intro h
        exact hc.mp (by simpa using h.2)
  | leftBoundary s =>
      have hc := canonicalCubic25_fromEigen_eq_zero_iff_segre
        (e := e) (a := 0) (b := 1) (c := 1) (d := s) he
      change canonicalSegreCubic25Three e 0 1 1 s = 0 ↔
        0 * 1 - 0 * s = 0 ∧
          canonicalCubic25Three
            (canonicalCoordinatesFromEigen25Three e 0 0 1 s) = 0
      constructor
      · intro h
        exact ⟨by ring, by simpa using hc.mpr h⟩
      · intro h
        exact hc.mp (by simpa using h.2)
  | rightBoundary r =>
      have hc := canonicalCubic25_fromEigen_eq_zero_iff_segre
        (e := e) (a := 1) (b := r) (c := 0) (d := 1) he
      change canonicalSegreCubic25Three e 1 r 0 1 = 0 ↔
        1 * 0 - 0 * r = 0 ∧
          canonicalCubic25Three
            (canonicalCoordinatesFromEigen25Three e 0 1 0 r) = 0
      constructor
      · intro h
        exact ⟨by ring, by simpa using hc.mpr h⟩
      · intro h
        exact hc.mp (by simpa using h.2)
  | corner =>
      have hc := canonicalCubic25_fromEigen_eq_zero_iff_segre
        (e := e) (a := 0) (b := 1) (c := 0) (d := 1) he
      change canonicalSegreCubic25Three e 0 1 0 1 = 0 ↔
        0 * 0 - 0 * 1 = 0 ∧
          canonicalCubic25Three
            (canonicalCoordinatesFromEigen25Three e 0 0 0 1) = 0
      constructor
      · intro h
        exact ⟨by ring, by simpa using hc.mpr h⟩
      · intro h
        exact hc.mp (by simpa using h.2)

/-- The pulled-back canonical cubic on normalized eigen-coordinates.  It is
kept separate here because the determinant equation is already stored in
the subtype produced by the Segre-quadric equivalence. -/
def IsNormalizedEigenCubic (e : K)
    (P : NormalizedProjective4 K) : Prop :=
  let U := normalizedCoordinatesThree P
  canonicalCubic25Three
    (canonicalCoordinatesFromEigen25Three e U.x U.y U.z U.w) = 0

/-- Inside the determinant quadric, the four-term Segre cubic cuts out the
same locus as the pulled-back canonical cubic. -/
def segreSolutionsEquivEigenQuadricCubic
    {e : K} (he : IsCyclotomicFive25Three e) :
    SegreSolutions e ≃
      {Q : {P : NormalizedProjective4 K // IsNormalizedEigenQuadric P} //
        IsNormalizedEigenCubic e Q.1} :=
  normalizedSegreEquivEigenQuadric.subtypeEquiv (fun p => by
    change IsNormalizedSegreCurve e p ↔
      IsNormalizedEigenCubic e (normalizedSegreEigenPoint p)
    have h := isNormalizedSegreCurve_iff_eigenCurve he p
    constructor
    · intro hp
      exact (h.mp hp).2
    · intro hc
      exact h.mpr ⟨(normalizedSegreEquivEigenQuadric p).2, hc⟩)

/-- Flatten the nested “point on the quadric, then on the cubic” subtype to
the conjunction defining the normalized eigen-coordinate curve. -/
def eigenQuadricCubicEquivEigenCurve (e : K) :
    {Q : {P : NormalizedProjective4 K // IsNormalizedEigenQuadric P} //
        IsNormalizedEigenCubic e Q.1} ≃
      {P : NormalizedProjective4 K // IsNormalizedEigenCurve e P} where
  toFun Q := ⟨Q.1.1, Q.1.2, Q.2⟩
  invFun P := ⟨⟨P.1, P.2.1⟩, P.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The normalized Segre curve and the normalized eigen-coordinate curve are
equivalent as finite types, not merely related by a surjection. -/
def segreSolutionsEquivEigenCurve
    {e : K} (he : IsCyclotomicFive25Three e) :
    SegreSolutions e ≃
      {P : NormalizedProjective4 K // IsNormalizedEigenCurve e P} :=
  (segreSolutionsEquivEigenQuadricCubic he).trans
    (eigenQuadricCubicEquivEigenCurve e)

/-- Restrict the projective eigenbasis equivalence to the curve equations.
Homogeneity ensures that first-nonzero renormalization preserves both loci. -/
def eigenCurveEquivCanonicalCurve
    (e : K) (he : IsCyclotomicFive25Three e) :
    {P : NormalizedProjective4 K // IsNormalizedEigenCurve e P} ≃
      {P : NormalizedProjective4 K // IsCanonicalNormalizedThree P} :=
  (eigenCanonicalProjectiveEquiv e he).subtypeEquiv
    (isNormalizedEigenCurve_iff_canonical e he)

/-- Composite structural equivalence from the normalized `P¹ × P¹` Segre
model to the canonical normalized quadric-cubic model. -/
def segreSolutionsEquivCanonicalCurve
    (e : K) (he : IsCyclotomicFive25Three e) :
    SegreSolutions e ≃
      {P : NormalizedProjective4 K // IsCanonicalNormalizedThree P} :=
  (segreSolutionsEquivEigenCurve he).trans
    (eigenCurveEquivCanonicalCurve e he)

end CanonicalRestriction

/-- The canonical normalized genus-four model has exactly 89 points over
`F81`, transported from the structural Kummer-Segre count. -/
theorem f81_canonical_normalized_three_card :
    Nat.card {P : NormalizedProjective4 F81 // IsCanonicalNormalizedThree P} =
      89 := by
  calc
    Nat.card {P : NormalizedProjective4 F81 // IsCanonicalNormalizedThree P} =
        Nat.card (SegreSolutions f81FifthRoot25) :=
      Nat.card_congr
        (segreSolutionsEquivCanonicalCurve
          f81FifthRoot25 f81FifthRoot25_isCyclotomic).symm
    _ = 89 := f81_segre_solutions_card

/-- The executable ternary-table predicate and the actual field-valued
canonical predicate define equivalent point types over `F81`. -/
def f81ExecutableCanonicalEquivActual :
    {P : NormalizedProjective4 F81 //
      IsCanonicalNormalized25Ternary f81Operations P} ≃
    {P : NormalizedProjective4 F81 // IsCanonicalNormalizedThree P} :=
  Equiv.subtypeEquivRight isCanonicalNormalized25Ternary_f81_iff

/-- The legacy executable normalized-point predicate therefore also has
exactly 89 solutions; this statement contains no ambient point enumeration. -/
theorem f81_canonical_normalized_ternary_card :
    Nat.card {P : NormalizedProjective4 F81 //
      IsCanonicalNormalized25Ternary f81Operations P} = 89 := by
  calc
    Nat.card {P : NormalizedProjective4 F81 //
        IsCanonicalNormalized25Ternary f81Operations P} =
        Nat.card {P : NormalizedProjective4 F81 //
          IsCanonicalNormalizedThree P} :=
      Nat.card_congr f81ExecutableCanonicalEquivActual
    _ = 89 := f81_canonical_normalized_three_card

end


end MazurProof.RationalPointsN25QuotientKummerThreeProjective
