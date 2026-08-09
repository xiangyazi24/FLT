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

end


end MazurProof.RationalPointsN25QuotientKummerThreeProjective
