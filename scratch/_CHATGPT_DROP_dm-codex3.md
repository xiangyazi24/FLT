# Q2369 Lean drop: certificate boundary for the N=12 curve `E24` / shifted curve `E1`

Target curve over `ℚ`:

```text
E24 : V^2 = U^3 - U^2 - 4U + 4
```

Shifted model:

```text
X = U - 1,  Y = V
E1 : Y^2 = X^3 + 2X^2 - 3X = X * (X - 1) * (X + 3).
```

The desired affine rational points are:

```text
E24 : (-2,0), (1,0), (2,0), (0,±2), (4,±6)
E1  : (-3,0), (0,0), (1,0), (-1,±2), (3,±6)
```

This note gives formalization-grade theorem boundaries and a certificate DAG.  It deliberately separates:

* elementary wrappers and finite congruence checks;
* the genuinely hard descent/rank theorem;
* the optional direct full-2-cover classification route that avoids a large elliptic-curve group API but replaces it with explicit genus-one cover certificates.

## 1. Basic definitions and exact point-list wrappers

These definitions are intentionally local and lightweight.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Original affine N=12 curve. -/
def E24Curve (U V : ℚ) : Prop :=
  V ^ 2 = U ^ 3 - U ^ 2 - 4 * U + 4

/-- Shifted curve `X = U - 1`. -/
def E1Curve (X Y : ℚ) : Prop :=
  Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X

/-- Exact affine point list on `E1`. -/
def E1AffinePointList (X Y : ℚ) : Prop :=
  (X = (-3 : ℚ) ∧ Y = 0) ∨
  (X = 0 ∧ Y = 0) ∨
  (X = 1 ∧ Y = 0) ∨
  (X = -1 ∧ Y = 2) ∨
  (X = -1 ∧ Y = -2) ∨
  (X = 3 ∧ Y = 6) ∨
  (X = 3 ∧ Y = -6)

/-- Exact affine point list on `E24`. -/
def E24AffinePointList (U V : ℚ) : Prop :=
  (U = (-2 : ℚ) ∧ V = 0) ∨
  (U = 1 ∧ V = 0) ∨
  (U = 2 ∧ V = 0) ∨
  (U = 0 ∧ V = 2) ∨
  (U = 0 ∧ V = -2) ∨
  (U = 4 ∧ V = 6) ∨
  (U = 4 ∧ V = -6)

/-- Shift an `E24` point to `E1`. -/
theorem E1Curve_of_E24Curve
    {U V : ℚ} (h : E24Curve U V) :
    E1Curve (U - 1) V := by
  dsimp [E24Curve, E1Curve] at h ⊢
  rw [h]
  ring

/-- Unshift an `E1` point to `E24`. -/
theorem E24Curve_of_E1Curve
    {X Y : ℚ} (h : E1Curve X Y) :
    E24Curve (X + 1) Y := by
  dsimp [E24Curve, E1Curve] at h ⊢
  rw [h]
  ring

/-- Convert the shifted exact list back to the original exact list. -/
theorem E24AffinePointList_of_E1AffinePointList_shift
    {U V : ℚ}
    (h : E1AffinePointList (U - 1) V) :
    E24AffinePointList U V := by
  rcases h with h | h | h | h | h | h | h
  · left; constructor <;> linarith
  · right; left; constructor <;> linarith
  · right; right; left; constructor <;> linarith
  · right; right; right; left; constructor <;> linarith
  · right; right; right; right; left; constructor <;> linarith
  · right; right; right; right; right; left; constructor <;> linarith
  · right; right; right; right; right; right; constructor <;> linarith

/-- Final wrapper: exact shifted affine classification implies exact original affine classification. -/
theorem E24AffineRationalPoints_of_E1AffineRationalPoints
    (hE1 : ∀ X Y : ℚ, E1Curve X Y → E1AffinePointList X Y) :
    ∀ U V : ℚ, E24Curve U V → E24AffinePointList U V := by
  intro U V h
  exact E24AffinePointList_of_E1AffinePointList_shift
    (hE1 (U - 1) V (E1Curve_of_E24Curve h))

end MazurProof.RationalPointsN12
```

## 2. Minimal rank-zero/torsion boundary without committing to a full EC API

A future elliptic-curve file may provide an actual group structure.  The N=12 obstruction file does not need to know it.  The following interface is enough: a black-box predicate `IsTorsion` on the small local point type, a rank-zero certificate saying every point is torsion, and a torsion enumeration certificate saying the torsion points are exactly the visible list.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Local point type for `E1`, including the point at infinity. -/
inductive E1Point where
  | infinity : E1Point
  | affine (X Y : ℚ) (h : E1Curve X Y) : E1Point

/-- The visible finite point list, including infinity. -/
def E1VisibleTorsionPoint : E1Point → Prop
  | .infinity => True
  | .affine X Y _ => E1AffinePointList X Y

/-- Rank-zero certificate relative to a future torsion predicate. -/
def E1RankZeroCertificate (IsTorsion : E1Point → Prop) : Prop :=
  ∀ P : E1Point, IsTorsion P

/-- Torsion enumeration certificate relative to the same future torsion predicate. -/
def E1TorsionEnumerationCertificate (IsTorsion : E1Point → Prop) : Prop :=
  ∀ P : E1Point, IsTorsion P → E1VisibleTorsionPoint P

/-- Rank-zero + torsion enumeration implies the exact affine point list. -/
theorem E1AffineRationalPoints_of_rankZero_and_torsionEnumeration
    (IsTorsion : E1Point → Prop)
    (hrank : E1RankZeroCertificate IsTorsion)
    (htors : E1TorsionEnumerationCertificate IsTorsion) :
    ∀ X Y : ℚ, E1Curve X Y → E1AffinePointList X Y := by
  intro X Y hXY
  exact htors (.affine X Y hXY) (hrank (.affine X Y hXY))

/-- Combined wrapper all the way back to `E24`. -/
theorem E24AffineRationalPoints_of_rankZero_and_torsionEnumeration
    (IsTorsion : E1Point → Prop)
    (hrank : E1RankZeroCertificate IsTorsion)
    (htors : E1TorsionEnumerationCertificate IsTorsion) :
    ∀ U V : ℚ, E24Curve U V → E24AffinePointList U V := by
  exact E24AffineRationalPoints_of_E1AffineRationalPoints
    (E1AffineRationalPoints_of_rankZero_and_torsionEnumeration IsTorsion hrank htors)

end MazurProof.RationalPointsN12
```

This is the cleanest public interface if the future proof uses a group law.  The group-law file proves `hrank` from a 2-isogeny descent and proves `htors` from a Nagell--Lutz / reduction / explicit addition table argument.  The obstruction file imports only the final public theorem.

## 3. Special 2-isogeny descent certificate for this curve

For the curve

```text
E : y^2 = x^3 + a x^2 + b x,  a = 2, b = -3,
```

the quotient by `(0,0)` is

```text
E' : y^2 = x^3 - 4x^2 + 16x.
```

The standard 2-isogeny cover equations are:

For `E`:

```text
N^2 = d M^4 + 2 M^2 T^2 + e T^4,      d * e = -3.
```

For `E'`:

```text
N^2 = d M^4 - 4 M^2 T^2 + e T^4,      d * e = 16.
```

Use `d,e` instead of division by `d` in Lean.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Primitive binary normalization for cover coordinates. -/
def PrimitiveBinary (M T : ℤ) : Prop :=
  T ≠ 0 ∧ Int.gcd M T = 1

/-- Allowed `d,e` pairs for the 2-isogeny cover of `E1`, where `d*e = -3`. -/
def E1PhiPair (d e : ℤ) : Prop :=
  (d = 1 ∧ e = -3) ∨
  (d = -1 ∧ e = 3) ∨
  (d = 3 ∧ e = -1) ∨
  (d = -3 ∧ e = 1)

/-- 2-isogeny cover equation for `E1`. -/
def E1PhiCoverEq (d e M N T : ℤ) : Prop :=
  d * e = -3 ∧
  N ^ 2 = d * M ^ 4 + 2 * M ^ 2 * T ^ 2 + e * T ^ 4

/-- Primitive soluble `E1` 2-isogeny cover. -/
def E1PhiCoverPrimitiveSoluble (d e : ℤ) : Prop :=
  ∃ M N T : ℤ,
    PrimitiveBinary M T ∧ E1PhiCoverEq d e M N T

/-- Allowed `d,e` pairs for the dual cover of `E'`, where `d*e = 16`. -/
def E1DualPair (d e : ℤ) : Prop :=
  (d = 1 ∧ e = 16) ∨
  (d = -1 ∧ e = -16) ∨
  (d = 2 ∧ e = 8) ∨
  (d = -2 ∧ e = -8)

/-- Dual 2-isogeny cover equation for `E'`. -/
def E1DualCoverEq (d e M N T : ℤ) : Prop :=
  d * e = 16 ∧
  N ^ 2 = d * M ^ 4 - 4 * M ^ 2 * T ^ 2 + e * T ^ 4

/-- Primitive soluble dual cover. -/
def E1DualCoverPrimitiveSoluble (d e : ℤ) : Prop :=
  ∃ M N T : ℤ,
    PrimitiveBinary M T ∧ E1DualCoverEq d e M N T

/-- Finite 2-isogeny certificate: all `E1` phi-cover classes are among the four visible classes. -/
def E1PhiSelmerCertificate : Prop :=
  ∀ d e : ℤ,
    E1PhiCoverPrimitiveSoluble d e → E1PhiPair d e

/-- Finite dual certificate: only the identity dual cover is soluble. -/
def E1DualSelmerTrivialCertificate : Prop :=
  ∀ d e : ℤ,
    E1DualPair d e → E1DualCoverPrimitiveSoluble d e → d = 1 ∧ e = 16

/-- Hard group/descent boundary: the two finite cover certificates imply rank zero. -/
def E1RankZeroFromTwoIsogenyDescentTheorem
    (IsTorsion : E1Point → Prop) : Prop :=
  E1PhiSelmerCertificate →
  E1DualSelmerTrivialCertificate →
  E1RankZeroCertificate IsTorsion

end MazurProof.RationalPointsN12
```

The theorem `E1RankZeroFromTwoIsogenyDescentTheorem` is the honest rank/descent boundary if you use a minimal elliptic-curve group API.  It packages the rank formula for a degree-2 isogeny.  The N=12 file should not import the proof of this theorem.

## 4. Pure finite arithmetic for the dual covers

The dual cover certificate is the easiest part to make fully Lean-checkable.  The non-identity dual classes are killed as follows.

### Negative dual classes

For `d = -1, e = -16`:

```text
N^2 = -M^4 - 4M^2T^2 - 16T^4 < 0
```

because `T ≠ 0`.

For `d = -2, e = -8`:

```text
N^2 = -2M^4 - 4M^2T^2 - 8T^4 < 0.
```

These are pure `nlinarith` goals using `sq_nonneg M`, `sq_pos_of_ne_zero hT`, etc.

### The `d = 2, e = 8` dual class

The equation is

```text
N^2 = 2M^4 - 4M^2T^2 + 8T^4,
```

with `T ≠ 0` and `gcd M T = 1`.

Use the following finite residue facts:

```lean
import Mathlib

example (n : ZMod 8) : n ^ 2 ≠ (2 : ZMod 8) ∧ n ^ 2 ≠ (6 : ZMod 8) := by
  fin_cases n <;> decide

example (n : ZMod 16) : n ^ 2 ≠ (8 : ZMod 16) := by
  fin_cases n <;> decide
```

Then split on the parity of `M`.

* If `M` is odd, then `M^4 ≡ 1 (mod 8)`.  If `T` is even, the right side is `2 mod 8`; if `T` is odd, it is `6 mod 8`.  Both are impossible squares.
* If `M` is even, primitivity forces `T` odd.  Then the right side is `8 mod 16`, impossible for a square.

A good theorem interface for this finite check is:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Pure finite arithmetic: the dual cover class `d = -1` has no primitive solution. -/
def E1DualCover_neg_one_no_solution : Prop :=
  ¬ E1DualCoverPrimitiveSoluble (-1) (-16)

/-- Pure finite arithmetic: the dual cover class `d = -2` has no primitive solution. -/
def E1DualCover_neg_two_no_solution : Prop :=
  ¬ E1DualCoverPrimitiveSoluble (-2) (-8)

/-- Pure finite arithmetic: the dual cover class `d = 2` has no primitive solution. -/
def E1DualCover_two_no_solution : Prop :=
  ¬ E1DualCoverPrimitiveSoluble 2 8

/-- The three finite checks imply the dual Selmer certificate. -/
theorem E1DualSelmerTrivialCertificate_of_finite_checks
    (hneg1 : E1DualCover_neg_one_no_solution)
    (hneg2 : E1DualCover_neg_two_no_solution)
    (hpos2 : E1DualCover_two_no_solution) :
    E1DualSelmerTrivialCertificate := by
  intro d e hpair hsol
  rcases hpair with h | h | h | h
  · exact ⟨h.1, h.2⟩
  · subst d; subst e
    exact False.elim (hneg1 hsol)
  · subst d; subst e
    exact False.elim (hpos2 hsol)
  · subst d; subst e
    exact False.elim (hneg2 hsol)

end MazurProof.RationalPointsN12
```

The three `def`s above are not hard descent facts; they are finite arithmetic lemmas and should eventually become theorems with explicit `nlinarith`/`ZMod` proofs.

## 5. Torsion enumeration boundary

Nagell--Lutz alone is not rank zero, but after rank zero it is enough to enumerate torsion.  Keep the statement local.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Future finite torsion theorem for the shifted curve. -/
def E1TorsionEnumerationTheorem : Prop :=
  ∃ IsTorsion : E1Point → Prop,
    E1TorsionEnumerationCertificate IsTorsion ∧
    -- The same predicate will be used by the rank-zero theorem.
    True

/-- Public theorem shape once the descent proof and torsion proof are connected. -/
def E1AffineRationalPointsFromTwoIsogenyAndTorsionTheorem : Prop :=
  ∃ IsTorsion : E1Point → Prop,
    E1RankZeroFromTwoIsogenyDescentTheorem IsTorsion ∧
    E1TorsionEnumerationCertificate IsTorsion →
    ∀ X Y : ℚ, E1Curve X Y → E1AffinePointList X Y

end MazurProof.RationalPointsN12
```

In a future file with a genuine group structure, replace the schematic `IsTorsion` by the actual group-theoretic torsion predicate and prove:

```lean
namespace MazurProof.RationalPointsN12

/-- Hard theorem, proved in a future file importing the descent internals. -/
theorem E1_rankZero_from_two_isogeny_descent
    (IsTorsion : E1Point → Prop) :
    E1RankZeroFromTwoIsogenyDescentTheorem IsTorsion := by
  -- Uses 2-isogeny descent, Selmer bounds, and the rank formula.
  -- Not in the obstruction file.
  sorry

/-- Hard finite theorem, proved by Nagell--Lutz / reductions / explicit group-law table. -/
theorem E1_torsion_enumeration
    (IsTorsion : E1Point → Prop) :
    E1TorsionEnumerationCertificate IsTorsion := by
  -- Finite torsion enumeration.
  -- Not in the obstruction file.
  sorry

end MazurProof.RationalPointsN12
```

These are theorem names to be proved elsewhere, not axioms to add to the current file.

## 6. Direct full-2-cover route avoiding a full EC group API

Yes: one can avoid a full elliptic-curve group API by proving a direct rational point classification using full 2-covering equations for the split cubic

```text
Y^2 = X(X - 1)(X + 3).
```

This replaces group/rank infrastructure with explicit genus-one cover certificates.  It is still a hard descent proof, but the theorem DAG can be purely about rational and integer equations.

For a non-2-torsion point, `X`, `X - 1`, and `X + 3` are nonzero.  Since their pairwise differences are `1`, `3`, and `4`, every prime outside `{2,3}` occurs to even valuation in each factor.  Thus their squareclasses have representatives in

```lean
def S23Rep (d : ℤ) : Prop :=
  d = -6 ∨ d = -3 ∨ d = -2 ∨ d = -1 ∨
  d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6
```

The full 2-cover equations are:

```text
X       = d0 * A^2 / T^2
X - 1   = d1 * B^2 / T^2
X + 3   = d3 * C^2 / T^2
```

so the primitive integer equations are:

```text
d0*A^2 - d1*B^2 = T^2
d3*C^2 - d0*A^2 = 3*T^2
```

and the product squareclass condition is that `d0*d1*d3` is a rational square.

The only non-torsion `X` values in the final list are `X = -1` and `X = 3`, with squareclass triples:

```text
X = -1 : (d0,d1,d3) = (-1,-2, 2)
X =  3 : (d0,d1,d3) = ( 3, 2, 6)
```

A direct-cover certificate interface is:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- S-unit squareclass representatives supported at `{2,3}`. -/
def S23Rep (d : ℤ) : Prop :=
  d = -6 ∨ d = -3 ∨ d = -2 ∨ d = -1 ∨
  d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6

/-- Product-one condition in `ℚ*/ℚ*²`, expressed by an integer square. -/
def SquareclassProductOne (d0 d1 d3 : ℤ) : Prop :=
  ∃ q : ℤ, d0 * d1 * d3 = q ^ 2

/-- Primitive full 2-cover solution. -/
def E1FullTwoCoverSolution
    (d0 d1 d3 A B C T : ℤ) : Prop :=
  S23Rep d0 ∧ S23Rep d1 ∧ S23Rep d3 ∧
  SquareclassProductOne d0 d1 d3 ∧
  T ≠ 0 ∧
  Int.gcd A T = 1 ∧ Int.gcd B T = 1 ∧ Int.gcd C T = 1 ∧
  d0 * A ^ 2 - d1 * B ^ 2 = T ^ 2 ∧
  d3 * C ^ 2 - d0 * A ^ 2 = 3 * T ^ 2

/-- Exact direct full-2-cover certificate. -/
def E1FullTwoCoverClassificationCertificate : Prop :=
  ∀ d0 d1 d3 A B C T : ℤ,
    E1FullTwoCoverSolution d0 d1 d3 A B C T →
      ((d0 = -1 ∧ d1 = -2 ∧ d3 = 2 ∧
          A ^ 2 = T ^ 2 ∧ B ^ 2 = T ^ 2 ∧ C ^ 2 = T ^ 2) ∨
       (d0 = 3 ∧ d1 = 2 ∧ d3 = 6 ∧
          A ^ 2 = T ^ 2 ∧ B ^ 2 = T ^ 2 ∧ C ^ 2 = T ^ 2))

/-- Elementary normalization theorem from a non-torsion affine point to a full 2-cover. -/
def E1PointToFullTwoCoverNormalizationTheorem : Prop :=
  ∀ X Y : ℚ,
    E1Curve X Y →
    Y ≠ 0 →
    ∃ d0 d1 d3 A B C T : ℤ,
      E1FullTwoCoverSolution d0 d1 d3 A B C T ∧
      X = (d0 : ℚ) * (A : ℚ) ^ 2 / (T : ℚ) ^ 2

/-- Direct-cover classification implies the exact affine point list. -/
def E1AffineRationalPointsFromFullTwoCoverTheorem : Prop :=
  E1PointToFullTwoCoverNormalizationTheorem →
  E1FullTwoCoverClassificationCertificate →
  ∀ X Y : ℚ, E1Curve X Y → E1AffinePointList X Y

end MazurProof.RationalPointsN12
```

The theorem `E1PointToFullTwoCoverNormalizationTheorem` is mostly elementary valuation/squareclass normalization.  The theorem `E1FullTwoCoverClassificationCertificate` is the hard direct descent certificate.  It can be proved by finitely many congruence checks and descent steps on the two simultaneous quadratic equations, without ever defining an elliptic-curve group law.

### Root-point wrapper for the direct route

The direct-cover route handles `Y ≠ 0`.  The root case is elementary:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- If `Y = 0`, then `X` is one of the three roots. -/
theorem E1AffinePointList_of_Y_eq_zero
    {X Y : ℚ}
    (h : E1Curve X Y)
    (hY : Y = 0) :
    E1AffinePointList X Y := by
  dsimp [E1Curve] at h
  subst Y
  have hprod : X * (X - 1) * (X + 3) = 0 := by
    nlinarith [h]
  have hx : X = 0 ∨ X - 1 = 0 ∨ X + 3 = 0 := by
    -- `mul_eq_zero.mp` twice; exact nesting may need local adjustment.
    rcases mul_eq_zero.mp hprod with h0 | h1
    · exact Or.inl h0
    · rcases mul_eq_zero.mp h1 with h1 | h3
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h3)
  rcases hx with h0 | h1 | h3
  · right; left; exact ⟨h0, rfl⟩
  · right; right; left; constructor <;> linarith
  · left; constructor <;> linarith

end MazurProof.RationalPointsN12
```

For `Y ≠ 0`, the full-cover certificate gives `X = -1` or `X = 3`; then the curve equation gives `Y^2 = 4` or `Y^2 = 36`, hence `Y = ±2` or `Y = ±6`.  Those are pure rational arithmetic lemmas.

## 7. Which facts are finite arithmetic and which are genuinely hard?

### Pure finite arithmetic / elementary Lean

These should be proved directly in Lean:

* shift wrappers between `E24` and `E1`;
* root case `Y = 0`;
* exact evaluation that the seven listed affine points lie on the curve;
* dual-cover negative-class contradictions by positivity;
* dual-cover `d = 2` contradiction by mod `8`/`16` squares;
* squareclass support outside `{2,3}` for the full split cubic;
* conversion from full-cover classified solutions to `X = -1` or `X = 3`;
* final `Y^2 = 4 → Y = ±2` and `Y^2 = 36 → Y = ±6`.

### Genuinely hard descent/rank facts

Choose one of these two hard boundaries, not both.

**Group/rank route:**

```lean
E1RankZeroFromTwoIsogenyDescentTheorem
E1TorsionEnumerationCertificate
```

This uses the 2-isogeny rank formula and torsion enumeration.

**Direct cover route:**

```lean
E1FullTwoCoverClassificationCertificate
```

This avoids a full elliptic-curve group API, but it requires solving the finite family of full 2-cover equations.  That is still a descent theorem, just expressed as elementary Diophantine certificates.

## 8. False stronger statements to avoid

* Nagell--Lutz / torsion enumeration alone does not prove rank zero.
* The four soluble `E1` phi-cover classes do not classify all rational points unless paired with the dual descent/rank theorem or a direct cover classification theorem.
* Do not claim that the local odd-prime sign splitting gives a single global sign modulo `B^2`; different odd prime powers can choose different signs, and `p = 2` behaves separately.
* Do not make the N=12 obstruction file depend on Selmer groups, isogeny maps, or cover-solution internals.  Put those in private proof files and export only the final point-classification theorem.

## 9. Recommended file split

```text
FLT/Assumptions/MazurProof/RationalPointsN12/CurveDefs.lean
```

Definitions and wrappers:

```lean
E24Curve
E1Curve
E1AffinePointList
E24AffinePointList
E24AffineRationalPoints_of_E1AffineRationalPoints
```

```text
FLT/Assumptions/MazurProof/RationalPointsN12/TwoIsogenyCovers.lean
```

Cover equations and finite congruence checks:

```lean
E1PhiCoverEq
E1DualCoverEq
E1DualSelmerTrivialCertificate_of_finite_checks
```

```text
FLT/Assumptions/MazurProof/RationalPointsN12/TwoIsogenyDescent.lean
```

Hard rank theorem:

```lean
E1RankZeroFromTwoIsogenyDescentTheorem
```

```text
FLT/Assumptions/MazurProof/RationalPointsN12/Torsion.lean
```

Finite torsion enumeration:

```lean
E1TorsionEnumerationCertificate
```

```text
FLT/Assumptions/MazurProof/RationalPointsN12/PointClassification.lean
```

Public theorem:

```lean
E1AffineRationalPoints
E24AffineRationalPoints
```

The existing N=12 obstruction file should import only `PointClassification.lean` or a still smaller public boundary file exporting `E24AffineRationalPoints`.