# Q2417 (dm-codex1): non-circular E24 classification from an E1 full-2-cover certificate

Goal in the local file:

```lean
def E24 (U V : ℚ) : Prop :=
  V^2 = U^3 - U^2 - 4*U + 4

def E24XCoordinateClassification : Prop :=
  ∀ {U V : ℚ}, E24 U V → U = -2 ∨ U = 1 ∨ U = 2 ∨ U = 0 ∨ U = 4
```

Shortest honest route:

```text
independent arithmetic inputs
  (FourRatSquaresAPConst + degenerate-cover obstruction + finite S23 local obstructions)
        |
        v
E1 full-2-cover certificate for Y≠0
        |
        v
E1 X-coordinate classification: X ∈ {-3,0,1,-1,3}
        |
        v  shift U = X+1
E24 U-coordinate classification: U ∈ {-2,1,2,0,4}
```

Do **not** use the current local `doubleLeg_of_ratQuarticEisenstein` if its `RatQuarticEisensteinXClassification` is produced from `E24XCoordinateClassification`.  That is circular.

---

## 1. Exact shift/birational relation between E24 and E1

There is no nontrivial birational map needed here.  It is the translation

```text
X = U - 1,
Y = V,
```

with inverse

```text
U = X + 1,
V = Y.
```

Indeed

```text
X(X-1)(X+3) at X=U-1
  = (U-1)(U-2)(U+2)
  = U^3 - U^2 - 4U + 4.
```

So define:

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Shifted E24 curve. -/
def E1 (X Y : ℚ) : Prop :=
  Y^2 = X * (X - 1) * (X + 3)

/-- Existing curve. -/
def E24 (U V : ℚ) : Prop :=
  V^2 = U^3 - U^2 - 4*U + 4

/-- E24 shifts to E1 by `X=U-1`, `Y=V`. -/
theorem E24_to_E1_shift {U V : ℚ} (h : E24 U V) :
    E1 (U - 1) V := by
  unfold E24 E1 at h ⊢
  nlinarith [h]

/-- Inverse shift: E1 shifts to E24 by `U=X+1`, `V=Y`. -/
theorem E1_to_E24_shift {X Y : ℚ} (h : E1 X Y) :
    E24 (X + 1) Y := by
  unfold E24 E1 at h ⊢
  nlinarith [h]

end MazurProof.RationalPointsN12
```

If `nlinarith` does not expand the cubic in your local Mathlib, replace each proof by:

```lean
  unfold E24 E1 at h ⊢
  ring_nf at h ⊢
  exact h
```

or, for the forward direction, `ring_nf at h ⊢` followed by `simpa using h`.

---

## 2. E1 theorem sufficient for E24

The E1 X-coordinate theorem is sufficient:

```lean
namespace MazurProof.RationalPointsN12

/-- X-coordinate classification on the shifted curve. -/
def E1XCoordinateClassification : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3

/-- Optional stronger affine point list.  This is more than E24 needs. -/
def E1AffinePointList : Prop :=
  ∀ {X Y : ℚ}, E1 X Y →
    (X = -3 ∧ Y = 0) ∨
    (X = 0 ∧ Y = 0) ∨
    (X = 1 ∧ Y = 0) ∨
    (X = -1 ∧ (Y = 2 ∨ Y = -2)) ∨
    (X = 3 ∧ (Y = 6 ∨ Y = -6))

/-- Strong point list implies the X-coordinate list. -/
theorem E1XCoordinateClassification_of_affinePointList
    (hList : E1AffinePointList) :
    E1XCoordinateClassification := by
  intro X Y hE1
  rcases hList hE1 with
    ⟨hX, hY⟩ | ⟨hX, hY⟩ | ⟨hX, hY⟩ | ⟨hX, hY⟩ | ⟨hX, hY⟩
  · exact Or.inl hX
  · exact Or.inr (Or.inl hX)
  · exact Or.inr (Or.inr (Or.inl hX))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hX)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hX)))

/-- E1 X-coordinate classification transfers to the existing E24 U-coordinate list. -/
theorem E24XCoordinateClassification_of_E1X
    (hE1X : E1XCoordinateClassification) :
    E24XCoordinateClassification := by
  intro U V hE24
  have hE1 : E1 (U - 1) V := E24_to_E1_shift hE24
  rcases hE1X hE1 with hXm3 | hX0 | hX1 | hXm1 | hX3
  · left
    nlinarith [hXm3]
  · right; left
    nlinarith [hX0]
  · right; right; left
    nlinarith [hX1]
  · right; right; right; left
    nlinarith [hXm1]
  · right; right; right; right
    nlinarith [hX3]

end MazurProof.RationalPointsN12
```

Coordinate correspondence:

```text
E1 X=-3  <-> E24 U=-2
E1 X= 0  <-> E24 U= 1
E1 X= 1  <-> E24 U= 2
E1 X=-1  <-> E24 U= 0
E1 X= 3  <-> E24 U= 4
```

Thus the E1 X-coordinate theorem is the exact sufficient target.  You do not need the Y-coordinate list to prove `E24XCoordinateClassification`.

---

## 3. Full-cover certificate and squareclass triples

### 3.1 Cover equations

Use the existing cover equations:

```lean
namespace MazurProof.RationalPointsN12

def CoverQ (d0 d1 d3 : ℤ) (A B C T : ℚ) : Prop :=
  (d0 : ℚ)*A^2 - (d1 : ℚ)*B^2 = T^2 ∧
  (d3 : ℚ)*C^2 - (d0 : ℚ)*A^2 = (3:ℚ)*T^2

end MazurProof.RationalPointsN12
```

Interpretation for an E1 point with `Y ≠ 0`:

```text
X     = d0 * (A/T)^2,
X - 1 = d1 * (B/T)^2,
X + 3 = d3 * (C/T)^2.
```

The two cover equations are just the cleared identities

```text
X - (X-1) = 1,
(X+3) - X = 3.
```

The product condition comes from

```text
Y^2 = X(X-1)(X+3),
```

so `d0*d1*d3` is a squareclass one.  Valuation parity away from `{2,3}` gives representatives in

```text
S23 = {±1, ±2, ±3, ±6}.
```

### 3.2 Squareclass extraction interface

This is the non-smuggling extraction theorem.  It says only that a nonzero E1 point gives a cover datum; it does not classify `X`.

```lean
namespace MazurProof.RationalPointsN12

def S23Rep (d : ℤ) : Prop :=
  d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 ∨ d = -1 ∨ d = -2 ∨ d = -3 ∨ d = -6

/-- Product-one in `ℚ*/ℚ*^2`, encoded as the finite table over S23.
For implementation, make this a decidable finite predicate rather than an existential square. -/
def S23ProductOne (d0 d1 d3 : ℤ) : Prop :=
  -- Placeholder definition shape.  Recommended implementation: finite disjunction over the 64 table entries.
  S23Rep d0 ∧ S23Rep d1 ∧ S23Rep d3 ∧
  ((d0 = 1 ∧ d1 = 1 ∧ d3 = 1) ∨ True)

/-- Full-cover extraction for `Y≠0` on E1.
This is valuation/denominator-clearing plumbing, not a classification theorem. -/
def E1FullCoverExtraction : Prop :=
  ∀ {X Y : ℚ},
    E1 X Y → Y ≠ 0 →
      ∃ d0 d1 d3 : ℤ,
      ∃ A B C T : ℚ,
        S23Rep d0 ∧ S23Rep d1 ∧ S23Rep d3 ∧
        S23ProductOne d0 d1 d3 ∧
        A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧ T ≠ 0 ∧
        CoverQ d0 d1 d3 A B C T ∧
        X = (d0 : ℚ) * (A / T)^2

end MazurProof.RationalPointsN12
```

Important implementation note: do **not** literally keep the placeholder `S23ProductOne` above.  Replace it by either:

* a finite 64-entry disjunction/table; or
* a Boolean/decidable squareclass-vector predicate using sign, parity at 2, parity at 3.

The extraction theorem is the place to prove valuation parity and denominator clearing.

### 3.3 Surviving residual triples

After sign and finite local congruence obstructions, only four product-one S23 triples should remain:

```text
(1,1,1)       degenerate residual: only zero coordinate cover solutions
(-3,-1,3)     degenerate residual: only zero coordinate cover solutions
(-1,-2,2)     AP residual, forces X=-1
(3,2,6)       AP residual, forces X=3
```

All other 60 product-one triples are obstructed:

* 32 by real sign directly: product-one sign patterns `+--` and `-+-`;
* 28 by finite primitive projective congruence, the same finite table from Q2378/Q2408.

The same-sign finite-congruence obstruction lists are:

```text
+++ nonresidual finite-congruence triples:
(1,2,2), (1,3,3), (1,6,6),
(2,1,2), (2,2,1), (2,3,6), (2,6,3),
(3,1,3), (3,3,1), (3,6,2),
(6,1,6), (6,2,3), (6,3,2), (6,6,1)

--+ nonresidual finite-congruence triples:
(-1,-1,1), (-1,-3,3), (-1,-6,6),
(-2,-1,2), (-2,-2,1), (-2,-3,6), (-2,-6,3),
(-3,-2,6), (-3,-3,1), (-3,-6,2),
(-6,-1,6), (-6,-2,3), (-6,-3,2), (-6,-6,1)
```

The two AP residuals are handled by the Q2403 wrappers using the independent theorem

```lean
def FourRatSquaresAPConst : Prop :=
  ∀ {w x y z : ℚ},
    x^2 - w^2 = y^2 - x^2 →
    y^2 - x^2 = z^2 - y^2 →
      w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2
```

The two degenerate residuals need an **independent** obstruction, not the current downstream `doubleLeg_of_ratQuarticEisenstein`.

---

## 4. Minimal Lean interfaces for the arithmetic certificate

### 4.1 Local/non-AP obstruction interface

This is the clean way to avoid smuggling the final E1 theorem while hiding the finite table implementation behind one theorem.

```lean
namespace MazurProof.RationalPointsN12

def APResidualTriple (d0 d1 d3 : ℤ) : Prop :=
  (d0 = 3 ∧ d1 = 2 ∧ d3 = 6) ∨
  (d0 = -1 ∧ d1 = -2 ∧ d3 = 2)

/-- Non-AP product-one S23 covers have no nonzero rational solution.
This theorem is assembled from:
1. 32 sign obstructions,
2. 28 finite primitive-projective congruence obstructions,
3. two degenerate residual obstructions `(1,1,1)` and `(-3,-1,3)`.
It is not the final E1 theorem: it speaks only about cover equations and nonzero cover variables. -/
def S23NonAPCoverNoNonzero : Prop :=
  ∀ {d0 d1 d3 : ℤ} {A B C T : ℚ},
    S23Rep d0 → S23Rep d1 → S23Rep d3 →
    S23ProductOne d0 d1 d3 →
    ¬ APResidualTriple d0 d1 d3 →
    A ≠ 0 → B ≠ 0 → C ≠ 0 → T ≠ 0 →
    CoverQ d0 d1 d3 A B C T → False

end MazurProof.RationalPointsN12
```

This is a compact producer theorem for the full-cover assembly.  Internally prove it from the finite table; externally it is a cover-equation theorem, not an E1 coordinate theorem.

### 4.2 Degenerate residual obstruction without circularity

The two degenerate triples can be killed by `DoubleLegRightTrianglesDegenerate`, but the producer of that theorem must be independent.

```lean
namespace MazurProof.RationalPointsN12

def DoubleLegRightTrianglesDegenerate : Prop :=
  ∀ {x y h k : ℚ},
    h^2 = x^2 + y^2 →
    k^2 = (2*x)^2 + y^2 →
      x = 0 ∨ y = 0

/-- `(1,1,1)` has no cover solution with all variables nonzero. -/
theorem coverQ_1_1_1_no_nonzero_of_doubleLeg
    (hDL : DoubleLegRightTrianglesDegenerate)
    {A B C T : ℚ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hT : T ≠ 0)
    (h : CoverQ 1 1 1 A B C T) : False := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have hpy1 : A^2 = T^2 + B^2 := by nlinarith [h1]
  have hpy2 : C^2 = (2*T)^2 + B^2 := by nlinarith [h1, h2]
  rcases hDL hpy1 hpy2 with hT0 | hB0
  · exact hT hT0
  · exact hB hB0

/-- `(-3,-1,3)` has no cover solution with all variables nonzero. -/
theorem coverQ_neg3_neg1_3_no_nonzero_of_doubleLeg
    (hDL : DoubleLegRightTrianglesDegenerate)
    {A B C T : ℚ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hT : T ≠ 0)
    (h : CoverQ (-3) (-1) 3 A B C T) : False := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have hpy1 : T^2 = A^2 + C^2 := by nlinarith [h2]
  have hpy2 : B^2 = (2*A)^2 + C^2 := by nlinarith [h1, h2]
  rcases hDL hpy1 hpy2 with hA0 | hC0
  · exact hA hA0
  · exact hC hC0

end MazurProof.RationalPointsN12
```

Allowed independent producers for `DoubleLegRightTrianglesDegenerate`:

* a direct Fermat/Pythagorean descent proof;
* an external Eisenstein quartic theorem proved without E24/E1;
* a theorem derived from the same independent descent package as Q2407.

Disallowed producer in this route:

```text
E24XCoordinateClassification
  -> C12/E24 map
  -> RatQuarticEisensteinXClassification
  -> doubleLeg_of_ratQuarticEisenstein
  -> degenerate cover obstruction
  -> E1 point list
  -> E24XCoordinateClassification
```

That is circular.

### 4.3 AP residual wrappers

Use the Q2403 wrappers as plumbing:

```lean
namespace MazurProof.RationalPointsN12

-- Already planned/proved in Q2403:
theorem coverQ_3_2_6_forces_X_eq_three
    (hAP : FourRatSquaresAPConst)
    {A B C T X : ℚ}
    (hT : T ≠ 0)
    (hX : X = (3:ℚ) * (A / T)^2)
    (hcover : CoverQ 3 2 6 A B C T) :
    X = 3 := by
  -- existing Q2403 code
  sorry

-- Already planned/proved in Q2403:
theorem coverQ_neg1_neg2_2_forces_X_eq_neg_one
    (hAP : FourRatSquaresAPConst)
    {A B C T X : ℚ}
    (hT : T ≠ 0)
    (hX : X = (-1:ℚ) * (A / T)^2)
    (hcover : CoverQ (-1) (-2) 2 A B C T) :
    X = -1 := by
  -- existing Q2403 code
  sorry

end MazurProof.RationalPointsN12
```

Those wrappers consume only `FourRatSquaresAPConst`; they do not depend on E24 or the quartic classifier.

---

## 5. Full-cover assembly to E1 X-coordinate classification

Split E1 into `Y=0` and `Y≠0`.

### 5.1 Torsion branch `Y=0`

```lean
namespace MazurProof.RationalPointsN12

/-- The `Y=0` branch on E1 gives the three roots. -/
theorem E1_X_of_Y_eq_zero {X : ℚ}
    (h : E1 X 0) :
    X = -3 ∨ X = 0 ∨ X = 1 := by
  unfold E1 at h
  norm_num at h
  have hprod : X * (X - 1) * (X + 3) = 0 := by nlinarith [h]
  have hleft : X * (X - 1) = 0 ∨ X + 3 = 0 := by
    exact mul_eq_zero.mp hprod
  rcases hleft with h01 | hm3
  · have h0or1 : X = 0 ∨ X - 1 = 0 := mul_eq_zero.mp h01
    rcases h0or1 with h0 | h1
    · exact Or.inr (Or.inl h0)
    · right; right; nlinarith [h1]
  · left; nlinarith [hm3]

end MazurProof.RationalPointsN12
```

### 5.2 Nonzero branch from full-cover certificate

```lean
namespace MazurProof.RationalPointsN12

/-- Nonzero E1 branch: full cover plus arithmetic certificate gives `X=-1` or `X=3`. -/
theorem E1_nonzeroY_X_of_fullCoverCertificate
    (hExtract : E1FullCoverExtraction)
    (hNoNonAP : S23NonAPCoverNoNonzero)
    (hAP : FourRatSquaresAPConst)
    {X Y : ℚ}
    (hE1 : E1 X Y)
    (hY : Y ≠ 0) :
    X = -1 ∨ X = 3 := by
  rcases hExtract hE1 hY with
    ⟨d0, d1, d3, A, B, C, T,
      hd0, hd1, hd3, hprod,
      hA, hB, hC, hT, hcover, hX⟩
  by_cases hres : APResidualTriple d0 d1 d3
  · unfold APResidualTriple at hres
    rcases hres with h326 | hn112
    · rcases h326 with ⟨rfl, rfl, rfl⟩
      right
      exact coverQ_3_2_6_forces_X_eq_three hAP hT hX hcover
    · rcases hn112 with ⟨rfl, rfl, rfl⟩
      left
      exact coverQ_neg1_neg2_2_forces_X_eq_neg_one hAP hT hX hcover
  · exfalso
    exact hNoNonAP hd0 hd1 hd3 hprod hres hA hB hC hT hcover

/-- E1 X-coordinate classification from the full-cover arithmetic certificate. -/
theorem E1XCoordinateClassification_of_fullCoverCertificate
    (hExtract : E1FullCoverExtraction)
    (hNoNonAP : S23NonAPCoverNoNonzero)
    (hAP : FourRatSquaresAPConst) :
    E1XCoordinateClassification := by
  intro X Y hE1
  by_cases hY : Y = 0
  · have hroot : X = -3 ∨ X = 0 ∨ X = 1 := by
      simpa [hY] using E1_X_of_Y_eq_zero (X := X) (by simpa [hY] using hE1)
    rcases hroot with hm3 | h0 | h1
    · exact Or.inl hm3
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr (Or.inl h1))
  · have hnon : X = -1 ∨ X = 3 :=
      E1_nonzeroY_X_of_fullCoverCertificate hExtract hNoNonAP hAP hE1 hY
    rcases hnon with hm1 | h3
    · exact Or.inr (Or.inr (Or.inr (Or.inl hm1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h3)))

/-- Final replacement producer for the old residual `E24XCoordinateClassification`. -/
theorem E24XCoordinateClassification_of_E1FullCoverCertificate
    (hExtract : E1FullCoverExtraction)
    (hNoNonAP : S23NonAPCoverNoNonzero)
    (hAP : FourRatSquaresAPConst) :
    E24XCoordinateClassification := by
  exact E24XCoordinateClassification_of_E1X
    (E1XCoordinateClassification_of_fullCoverCertificate hExtract hNoNonAP hAP)

end MazurProof.RationalPointsN12
```

The only arithmetic assumptions exposed to the final E24 wrapper are:

```text
hExtract : E1FullCoverExtraction
hNoNonAP : S23NonAPCoverNoNonzero
hAP      : FourRatSquaresAPConst
```

`hNoNonAP` itself should be produced by finite local obstruction table plus the independent degenerate-cover obstruction.  It should not be an axiom in the final theorem file unless you are deliberately staging the finite-certificate proof.

---

## 6. Recommended theorem DAG for a new module

Suggested module split:

```text
RationalPointsN12/E1Shift.lean
  E1
  E24_to_E1_shift
  E1_to_E24_shift
  E24XCoordinateClassification_of_E1X

RationalPointsN12/E1CoverDefs.lean
  CoverQ
  S23Rep
  S23ProductOne
  APResidualTriple
  E1FullCoverExtraction

RationalPointsN12/E1CoverExtraction.lean
  valuation parity away from {2,3}
  denominator clearing
  theorem e1FullCoverExtraction : E1FullCoverExtraction

RationalPointsN12/E1CoverLocalObstructions.lean
  sign obstructions for 32 triples
  finite ZMod certificates for 28 triples
  independent degenerate residual obstruction for (1,1,1), (-3,-1,3)
  theorem s23NonAPCoverNoNonzero : S23NonAPCoverNoNonzero

RationalPointsN12/FourSquaresAP.lean
  independent Fermat/Euler descent theorem
  theorem fourRatSquaresAPConst : FourRatSquaresAPConst

RationalPointsN12/E1CoverAssembly.lean
  Q2403 AP wrappers
  E1_X_of_Y_eq_zero
  E1_nonzeroY_X_of_fullCoverCertificate
  E1XCoordinateClassification_of_fullCoverCertificate
  E24XCoordinateClassification_of_E1FullCoverCertificate
```

Dependency DAG:

```text
FourSquaresAP.lean      E1CoverLocalObstructions.lean      E1CoverExtraction.lean
       \                         |                                /
        \                        |                               /
         v                       v                              v
                 E1CoverAssembly.lean
                         |
                         v
                 E24XCoordinateClassification
```

No path should go through:

```text
E24XCoordinateClassification -> RatQuarticEisensteinXClassification
```

when proving `E24XCoordinateClassification` itself.

---

## 7. Circularity flags

### Circular in the current local situation

You wrote:

```text
Existing C12→E24 map plus E24XCoordinateClassification proves the Eisenstein quartic x-classification.
```

Therefore this path is circular for proving E24:

```text
E24XCoordinateClassification
  -> RatQuarticEisensteinXClassification
  -> doubleLeg_of_ratQuarticEisenstein
  -> degenerate cover obstruction
  -> E1 full-cover point list
  -> E24XCoordinateClassification
```

Do not use `doubleLeg_of_ratQuarticEisenstein` in `E1CoverLocalObstructions.lean` unless the `RatQuarticEisensteinXClassification` argument is explicitly imported from an independent theorem, not from E24.

### Safe alternatives

Safe producers for the degenerate cover obstruction:

1. Prove `DoubleLegRightTrianglesDegenerate` independently by Pythagorean/Euler descent.
2. Prove the two degenerate cover no-nonzero theorems directly by the same descent.
3. Import an external Eisenstein quartic theorem only if its proof path is independent of E24/E1.

Safe producer for AP residuals:

```text
FourRatSquaresAPConst
```

proved by Q2407's independent Fermat/Euler descent, not by E1 rational points.

---

## 8. Final shortest honest route

The final replacement theorem should look like this:

```lean
theorem E24XCoordinateClassification_nonCircular
    (hExtract : E1FullCoverExtraction)
    (hNoNonAP : S23NonAPCoverNoNonzero)
    (hAP : FourRatSquaresAPConst) :
    E24XCoordinateClassification :=
  E24XCoordinateClassification_of_E1FullCoverCertificate hExtract hNoNonAP hAP
```

Then separately instantiate the three inputs with independent producers:

```lean
#check e1FullCoverExtraction             -- valuation + denominator clearing
#check s23NonAPCoverNoNonzero            -- finite local table + independent degenerate obstruction
#check fourRatSquaresAPConst             -- independent Fermat/Euler descent
```

This route proves the old `E24XCoordinateClassification` residual from an E1 full-2-cover certificate without using the E24-derived quartic classifier or any E1 point classification as an input.
