# Q2387 drop: minimal Lean assembly interface for the `E1` full-cover certificate

Target curve:

```text
E1 : Y^2 = X(X-1)(X+3)
```

Expected affine rational points:

```text
(-3,0), (0,0), (1,0), (-1,2), (-1,-2), (3,6), (3,-6).
```

This note gives a **minimal conditional assembly interface** for

```lean
E1AffinePointList_of_coverCertificate
```

using only the four requested inputs:

1. squareclass/full-cover extraction from a nonzero-`Y` point;
2. the finite local obstruction table for the 28 sign-compatible non-residual triples;
3. `FourRatSquaresAPConst`;
4. `DoubleLegRightTrianglesDegenerate`.

No quotient `ℚˣ/(ℚˣ)^2` is needed.  Everything is expressed with finite integer representatives and existential rational cover variables.

---

## 0. Recommended namespace and imports

Use a new small interface file, for example

```text
FLT/Assumptions/MazurProof/N12E1FullCoverInterface.lean
```

or place this section near the current N=12 rational-point file if avoiding a new import.  The code below deliberately uses only `Prop` fields/parameters, not `axiom`.

```lean
import Mathlib

namespace FLT.Mazur.N12.FullCover

noncomputable section
```

---

## 1. Curve and final point-list predicates

```lean
abbrev E1Rhs (X : ℚ) : ℚ := X * (X - 1) * (X + 3)

def OnE1 (X Y : ℚ) : Prop := Y^2 = E1Rhs X

def E1AffinePointList (X Y : ℚ) : Prop :=
  (X = -3 ∧ Y = 0) ∨
  (X = 0  ∧ Y = 0) ∨
  (X = 1  ∧ Y = 0) ∨
  (X = -1 ∧ Y = 2) ∨
  (X = -1 ∧ Y = -2) ∨
  (X = 3  ∧ Y = 6) ∨
  (X = 3  ∧ Y = -6)
```

The final theorem should have exactly this shape:

```lean
theorem E1AffinePointList_of_coverCertificate
    (cert : E1FullCoverCertificate) (X Y : ℚ) :
    OnE1 X Y ↔ E1AffinePointList X Y := by
  -- assembly described below
  sorry
```

The theorem is conditional only on `cert`; `cert` contains the four requested assumptions as Prop fields.

---

## 2. Finite representatives and cover equations

Use integer representatives for the squareclasses supported at `{2,3}`:

```lean
def S23Rep (d : ℤ) : Prop :=
  d = -6 ∨ d = -3 ∨ d = -2 ∨ d = -1 ∨
  d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6

/-- Product squareclass condition for `d0*d1*d3`.

Since `Y^2 = X(X-1)(X+3)`, the product representative must be a positive
square representative among the products of elements of `S23Rep`.
-/
def ProductSquareOK (d0 d1 d3 : ℤ) : Prop :=
  d0*d1*d3 = 1 ∨ d0*d1*d3 = 4 ∨
  d0*d1*d3 = 9 ∨ d0*d1*d3 = 36

/-- The two rational full-cover equations for the three squareclass reps. -/
def CoverQ (d0 d1 d3 : ℤ) (A B C T : ℚ) : Prop :=
  ((d0 : ℚ) * A^2 - (d1 : ℚ) * B^2 = T^2) ∧
  ((d3 : ℚ) * C^2 - (d0 : ℚ) * A^2 = (3 : ℚ) * T^2)

/-- Full-cover data anchored at a particular affine `X`.

The equalities say

```text
X     = d0*A^2/T^2,
X - 1 = d1*B^2/T^2,
X + 3 = d3*C^2/T^2.
```

The `hcover` field is redundant algebraically from the three anchored equalities
and `T ≠ 0`, but keeping it here makes downstream residual wrappers one-line to
apply.
-/
def CoverAtXQ (X : ℚ) (d0 d1 d3 : ℤ) (A B C T : ℚ) : Prop :=
  S23Rep d0 ∧ S23Rep d1 ∧ S23Rep d3 ∧
  ProductSquareOK d0 d1 d3 ∧
  T ≠ 0 ∧
  CoverQ d0 d1 d3 A B C T ∧
  X = (d0 : ℚ) * A^2 / T^2 ∧
  X - 1 = (d1 : ℚ) * B^2 / T^2 ∧
  X + 3 = (d3 : ℚ) * C^2 / T^2
```

The extraction assumption should be exactly existential data of this form:

```lean
/-- Honest residual or later theorem: extract finite squareclass full-cover data
from a nonzero-`Y` rational point on `E1`.

This is the only place where valuations/squareclasses outside `{2,3}` are used.
No quotient API is needed by consumers.
-/
def FullCoverExtraction : Prop :=
  ∀ {X Y : ℚ}, OnE1 X Y → Y ≠ 0 →
    ∃ (d0 d1 d3 : ℤ) (A B C T : ℚ),
      CoverAtXQ X d0 d1 d3 A B C T
```

This field is assumption **(1)** in the final certificate.

---

## 3. Nonzero-factor and real-sign branch predicates

For the final assembly, the nonzero-`Y` branch first proves the factors are nonzero:

```lean
def NonzeroFactors (X : ℚ) : Prop :=
  X ≠ 0 ∧ X - 1 ≠ 0 ∧ X + 3 ≠ 0
```

The real sign restriction leaves only two intervals:

```text
X > 1       : signs of X, X-1, X+3 are +,+,+;
-3 < X < 0  : signs are -,-,+.
```

Use this Lean predicate:

```lean
def RealSignCompatible (X : ℚ) (d0 d1 d3 : ℤ) : Prop :=
  (1 < X ∧ 0 < d0 ∧ 0 < d1 ∧ 0 < d3) ∨
  (-3 < X ∧ X < 0 ∧ d0 < 0 ∧ d1 < 0 ∧ 0 < d3)
```

Pure algebra/order wrappers that should be local, not trusted residuals:

```lean
theorem nonzeroFactors_of_onE1_ne_zero
    {X Y : ℚ} (hE : OnE1 X Y) (hY : Y ≠ 0) :
    NonzeroFactors X := by
  -- If any factor is zero, `E1Rhs X = 0`, hence `Y^2 = 0`, hence `Y = 0`.
  sorry

theorem realSignCompatible_of_coverAtX
    {X Y : ℚ} {d0 d1 d3 : ℤ} {A B C T : ℚ}
    (hE : OnE1 X Y) (hY : Y ≠ 0)
    (hcov : CoverAtXQ X d0 d1 d3 A B C T) :
    RealSignCompatible X d0 d1 d3 := by
  -- Pure order/algebra:
  -- 1. `Y ≠ 0` and `OnE1` imply `E1Rhs X > 0`.
  -- 2. Therefore `X > 1` or `-3 < X ∧ X < 0`.
  -- 3. The anchored cover equalities and nonzero factors force `d_i` to have
  --    the same sign as `X`, `X-1`, `X+3`, respectively.
  sorry
```

These two wrappers are not part of the trusted mathematical boundary.

---

## 4. Exact residual and obstructed triples

After product-square and real-sign filtering, there are 32 sign-compatible triples.
The four residual triples are exactly those from Q2383:

```text
AP residuals:        (3,2,6), (-1,-2,2)
double-leg residuals:(1,1,1), (-3,-1,3)
```

Define them as predicates:

```lean
def APResidualTriple (d0 d1 d3 : ℤ) : Prop :=
  (d0 = 3 ∧ d1 = 2 ∧ d3 = 6) ∨
  (d0 = -1 ∧ d1 = -2 ∧ d3 = 2)

def DoubleLegResidualTriple (d0 d1 d3 : ℤ) : Prop :=
  (d0 = 1 ∧ d1 = 1 ∧ d3 = 1) ∨
  (d0 = -3 ∧ d1 = -1 ∧ d3 = 3)

def ResidualTriple4 (d0 d1 d3 : ℤ) : Prop :=
  APResidualTriple d0 d1 d3 ∨ DoubleLegResidualTriple d0 d1 d3
```

The 28 finite-obstruction triples are the other sign-compatible triples:

```lean
def ObstructedTriple28 (d0 d1 d3 : ℤ) : Prop :=
  -- positive sign branch, excluding residual `(1,1,1)` and `(3,2,6)`
  (d0 = 1 ∧ d1 = 2 ∧ d3 = 2) ∨
  (d0 = 1 ∧ d1 = 3 ∧ d3 = 3) ∨
  (d0 = 1 ∧ d1 = 6 ∧ d3 = 6) ∨
  (d0 = 2 ∧ d1 = 1 ∧ d3 = 2) ∨
  (d0 = 2 ∧ d1 = 2 ∧ d3 = 1) ∨
  (d0 = 2 ∧ d1 = 3 ∧ d3 = 6) ∨
  (d0 = 2 ∧ d1 = 6 ∧ d3 = 3) ∨
  (d0 = 3 ∧ d1 = 1 ∧ d3 = 3) ∨
  (d0 = 3 ∧ d1 = 3 ∧ d3 = 1) ∨
  (d0 = 3 ∧ d1 = 6 ∧ d3 = 2) ∨
  (d0 = 6 ∧ d1 = 1 ∧ d3 = 6) ∨
  (d0 = 6 ∧ d1 = 2 ∧ d3 = 3) ∨
  (d0 = 6 ∧ d1 = 3 ∧ d3 = 2) ∨
  (d0 = 6 ∧ d1 = 6 ∧ d3 = 1) ∨
  -- negative-negative-positive sign branch, excluding residual `(-1,-2,2)` and `(-3,-1,3)`
  (d0 = -1 ∧ d1 = -1 ∧ d3 = 1) ∨
  (d0 = -1 ∧ d1 = -3 ∧ d3 = 3) ∨
  (d0 = -1 ∧ d1 = -6 ∧ d3 = 6) ∨
  (d0 = -2 ∧ d1 = -1 ∧ d3 = 2) ∨
  (d0 = -2 ∧ d1 = -2 ∧ d3 = 1) ∨
  (d0 = -2 ∧ d1 = -3 ∧ d3 = 6) ∨
  (d0 = -2 ∧ d1 = -6 ∧ d3 = 3) ∨
  (d0 = -3 ∧ d1 = -2 ∧ d3 = 6) ∨
  (d0 = -3 ∧ d1 = -3 ∧ d3 = 1) ∨
  (d0 = -3 ∧ d1 = -6 ∧ d3 = 2) ∨
  (d0 = -6 ∧ d1 = -1 ∧ d3 = 6) ∨
  (d0 = -6 ∧ d1 = -2 ∧ d3 = 3) ∨
  (d0 = -6 ∧ d1 = -3 ∧ d3 = 2) ∨
  (d0 = -6 ∧ d1 = -6 ∧ d3 = 1)
```

The finite partition lemma is pure enumeration and should be proved by case-splitting or a small decidable checker:

```lean
theorem triple_partition_after_sign
    {X : ℚ} {d0 d1 d3 : ℤ}
    (hd0 : S23Rep d0) (hd1 : S23Rep d1) (hd3 : S23Rep d3)
    (hprod : ProductSquareOK d0 d1 d3)
    (hreal : RealSignCompatible X d0 d1 d3) :
    ObstructedTriple28 d0 d1 d3 ∨ ResidualTriple4 d0 d1 d3 := by
  -- Pure finite proof:
  -- `rcases hd0 <;> rcases hd1 <;> rcases hd3 <;> simp_all [ProductSquareOK,
  --  RealSignCompatible, ObstructedTriple28, ResidualTriple4, APResidualTriple,
  --  DoubleLegResidualTriple]`
  -- then `omega`/`norm_num` closes each integer branch.
  sorry
```

The finite local obstruction table, assumption **(2)**, should be only this:

```lean
/-- Finite 2-adic/local obstruction table for the 28 non-residual sign-compatible triples.

This should eventually be proved by a checked finite congruence certificate.  It is not
elliptic-curve theory and not global descent.
-/
def LocalObstructionTable28 : Prop :=
  ∀ {X : ℚ} {d0 d1 d3 : ℤ} {A B C T : ℚ},
    CoverAtXQ X d0 d1 d3 A B C T →
    NonzeroFactors X →
    RealSignCompatible X d0 d1 d3 →
    ObstructedTriple28 d0 d1 d3 →
    False
```

This formulation makes the role of the table precise: it kills exactly the 28 triples after the pure real-sign branch and pure finite partition.  It does not need to mention the four residual covers.

---

## 5. The two global arithmetic residuals as Prop fields

Do not introduce `axiom`s.  Package the two global descent facts as proposition fields:

```lean
/-- Fermat: four rational squares in arithmetic progression are constant. -/
def FourRatSquaresAPConst : Prop :=
  ∀ {w x y z : ℚ},
    x^2 - w^2 = y^2 - x^2 →
    y^2 - x^2 = z^2 - y^2 →
    w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2

/-- Double-leg right-triangle obstruction.

If

```text
h^2 = x^2 + y^2,
k^2 = (2*x)^2 + y^2,
```

then one of the shared-leg parameters is degenerate.
-/
def DoubleLegRightTrianglesDegenerate : Prop :=
  ∀ {x y h k : ℚ},
    h^2 = x^2 + y^2 →
    k^2 = (2*x)^2 + y^2 →
    x = 0 ∨ y = 0
```

These are assumptions **(3)** and **(4)**.

---

## 6. Algebraic wrappers for the four residual covers

These wrappers are pure algebra once `FourRatSquaresAPConst` or `DoubleLegRightTrianglesDegenerate` is available as a parameter.  They should compile now with `nlinarith`/`ring_nf` after minor syntax tuning.

### 6.1 AP residual `(3,2,6)` gives `X=3`

```lean
theorem coverQ_3_2_6_from_fourSquaresAP
    (hAP : FourRatSquaresAPConst)
    {A B C T : ℚ}
    (h : CoverQ 3 2 6 A B C T) :
    A^2 = T^2 ∧ B^2 = T^2 ∧ C^2 = T^2 := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have h2' : 2*C^2 - A^2 = T^2 := by nlinarith
  have hap1 : A^2 - B^2 = C^2 - A^2 := by nlinarith [h1, h2']
  have hap2 : C^2 - A^2 = T^2 - C^2 := by nlinarith [h2']
  have hconst := hAP (w := B) (x := A) (y := C) (z := T) hap1 hap2
  rcases hconst with ⟨hBA, hAC, hCT⟩
  constructor
  · nlinarith [hAC, hCT]
  constructor
  · nlinarith [hBA, hAC, hCT]
  · nlinarith [hCT]
```

### 6.2 AP residual `(-1,-2,2)` gives `X=-1`

```lean
theorem coverQ_neg1_neg2_2_from_fourSquaresAP
    (hAP : FourRatSquaresAPConst)
    {A B C T : ℚ}
    (h : CoverQ (-1) (-2) 2 A B C T) :
    A^2 = T^2 ∧ B^2 = T^2 ∧ C^2 = T^2 := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have hap1 : B^2 - A^2 = T^2 - B^2 := by nlinarith [h1]
  have hap2 : T^2 - B^2 = C^2 - T^2 := by nlinarith [h1, h2]
  have hconst := hAP (w := A) (x := B) (y := T) (z := C) hap1 hap2
  rcases hconst with ⟨hAB, hBT, hTC⟩
  constructor
  · nlinarith [hAB, hBT]
  constructor
  · exact hBT
  · nlinarith [hTC]
```

### 6.3 Double-leg residual `(1,1,1)` is torsion-degenerate

```lean
theorem coverQ_1_1_1_from_doubleLeg
    (hDL : DoubleLegRightTrianglesDegenerate)
    {A B C T : ℚ}
    (hT : T ≠ 0)
    (h : CoverQ 1 1 1 A B C T) :
    B = 0 ∧ A^2 = T^2 ∧ C^2 = (4 : ℚ) * T^2 := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have hpy1 : A^2 = T^2 + B^2 := by nlinarith [h1]
  have hpy2 : C^2 = (2*T)^2 + B^2 := by nlinarith [h1, h2]
  have hdeg := hDL (x := T) (y := B) (h := A) (k := C) hpy1 hpy2
  rcases hdeg with hTzero | hBzero
  · exact (hT hTzero).elim
  · have hA : A^2 = T^2 := by nlinarith [h1, hBzero]
    have hC : C^2 = (4 : ℚ) * T^2 := by nlinarith [h2, hA]
    exact ⟨hBzero, hA, hC⟩
```

The `T ≠ 0` hypothesis is essential for the conclusion `B=0`.

### 6.4 Double-leg residual `(-3,-1,3)` is torsion-degenerate

```lean
theorem coverQ_neg3_neg1_3_from_doubleLeg
    (hDL : DoubleLegRightTrianglesDegenerate)
    {A B C T : ℚ}
    (h : CoverQ (-3) (-1) 3 A B C T) :
    (A = 0 ∧ B^2 = T^2 ∧ C^2 = T^2) ∨
    (C = 0 ∧ A^2 = T^2 ∧ B^2 = (4 : ℚ) * T^2) := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have hpy1 : T^2 = A^2 + C^2 := by nlinarith [h2]
  have hpy2 : B^2 = (2*A)^2 + C^2 := by nlinarith [h1, h2]
  have hdeg := hDL (x := A) (y := C) (h := T) (k := B) hpy1 hpy2
  rcases hdeg with hAzero | hCzero
  · left
    have hB : B^2 = T^2 := by nlinarith [h1, hAzero]
    have hC : C^2 = T^2 := by nlinarith [h2, hAzero]
    exact ⟨hAzero, hB, hC⟩
  · right
    have hA : A^2 = T^2 := by nlinarith [h2, hCzero]
    have hB : B^2 = (4 : ℚ) * T^2 := by nlinarith [h1, hA]
    exact ⟨hCzero, hA, hB⟩
```

---

## 7. The certificate structure

The top-level certificate has exactly the requested assumptions:

```lean
structure E1FullCoverCertificate : Prop where
  extract : FullCoverExtraction
  local28 : LocalObstructionTable28
  fourAP : FourRatSquaresAPConst
  doubleLeg : DoubleLegRightTrianglesDegenerate
```

No EC group law, Mordell-Weil rank, torsion reduction, or squareclass quotient API appears in this certificate.

---

## 8. Assembly lemmas for the nonzero branch

First, a pure finite/algebraic lemma that every nonzero-`Y` point has `X=-1` or `X=3`:

```lean
theorem nonzeroY_forces_X_neg1_or_3
    (cert : E1FullCoverCertificate)
    {X Y : ℚ}
    (hE : OnE1 X Y) (hY : Y ≠ 0) :
    X = -1 ∨ X = 3 := by
  rcases cert.extract hE hY with ⟨d0, d1, d3, A, B, C, T, hcovAt⟩
  have hnz : NonzeroFactors X := nonzeroFactors_of_onE1_ne_zero hE hY
  have hreal : RealSignCompatible X d0 d1 d3 :=
    realSignCompatible_of_coverAtX hE hY hcovAt

  rcases hcovAt with
    ⟨hd0, hd1, hd3, hprod, hT, hcover, hx0, hx1, hx3⟩

  have hpart : ObstructedTriple28 d0 d1 d3 ∨ ResidualTriple4 d0 d1 d3 :=
    triple_partition_after_sign hd0 hd1 hd3 hprod hreal

  cases hpart with
  | inl hobs =>
      exact False.elim (cert.local28 hcovAt hnz hreal hobs)
  | inr hres =>
      rcases hres with hAPres | hDLres
      · rcases hAPres with h326 | hn112
        · -- `(3,2,6)`
          rcases h326 with ⟨rfl, rfl, rfl⟩
          have hs := coverQ_3_2_6_from_fourSquaresAP cert.fourAP hcover
          rcases hs with ⟨hA, hB, hC⟩
          right
          -- `hx0 : X = 3*A^2/T^2`, `hA : A^2 = T^2`, `T ≠ 0`.
          field_simp [hx0, hA, hT]
        · -- `(-1,-2,2)`
          rcases hn112 with ⟨rfl, rfl, rfl⟩
          have hs := coverQ_neg1_neg2_2_from_fourSquaresAP cert.fourAP hcover
          rcases hs with ⟨hA, hB, hC⟩
          left
          -- `hx0 : X = -1*A^2/T^2`, `hA : A^2 = T^2`, `T ≠ 0`.
          field_simp [hx0, hA, hT]
      · rcases hDLres with h111 | hn313
        · -- `(1,1,1)` forces `B=0`, hence `X-1=0`, contradicting nonzero factors.
          rcases h111 with ⟨rfl, rfl, rfl⟩
          have hs := coverQ_1_1_1_from_doubleLeg cert.doubleLeg hT hcover
          rcases hs with ⟨hBzero, hA, hC⟩
          have hx1zero : X - 1 = 0 := by
            -- from `hx1 : X-1 = B^2/T^2` and `B=0`
            field_simp [hx1, hBzero, hT]
          exact False.elim (hnz.2.1 hx1zero)
        · -- `(-3,-1,3)` forces `A=0` or `C=0`, hence `X=0` or `X+3=0`.
          rcases hn313 with ⟨rfl, rfl, rfl⟩
          have hs := coverQ_neg3_neg1_3_from_doubleLeg cert.doubleLeg hcover
          rcases hs with hAdeg | hCdeg
          · rcases hAdeg with ⟨hAzero, hB, hC⟩
            have hx0zero : X = 0 := by
              -- from `hx0 : X = -3*A^2/T^2` and `A=0`
              field_simp [hx0, hAzero, hT]
            exact False.elim (hnz.1 hx0zero)
          · rcases hCdeg with ⟨hCzero, hA, hB⟩
            have hx3zero : X + 3 = 0 := by
              -- from `hx3 : X+3 = 3*C^2/T^2` and `C=0`
              field_simp [hx3, hCzero, hT]
            exact False.elim (hnz.2.2 hx3zero)
```

The above skeleton may need minor `field_simp` syntax tuning because `hx0`, `hx1`, `hx3` are equalities with division.  Mathematically, it is only field arithmetic using `T ≠ 0`.

---

## 9. Zero-`Y` branch and `Y` value classification

Pure algebra branch:

```lean
theorem zeroY_forces_X_torsion {X : ℚ}
    (h : OnE1 X 0) :
    X = -3 ∨ X = 0 ∨ X = 1 := by
  unfold OnE1 E1Rhs at h
  norm_num at h
  -- `0 = X*(X-1)*(X+3)`; use `mul_eq_zero.mp` twice, then linear arithmetic.
  sorry

theorem rat_sq_eq_four {Y : ℚ} (h : Y^2 = 4) :
    Y = 2 ∨ Y = -2 := by
  -- Use `sq_eq_sq_iff_eq_or_eq_neg`, or factor `(Y-2)*(Y+2)=0`.
  sorry

theorem rat_sq_eq_thirtysix {Y : ℚ} (h : Y^2 = 36) :
    Y = 6 ∨ Y = -6 := by
  -- Same proof.
  sorry

theorem Y_values_after_X_neg1_or_3
    {X Y : ℚ} (hE : OnE1 X Y) (hX : X = -1 ∨ X = 3) :
    (X = -1 ∧ (Y = 2 ∨ Y = -2)) ∨
    (X = 3 ∧ (Y = 6 ∨ Y = -6)) := by
  rcases hX with rfl | rfl
  · left
    have hYsq : Y^2 = 4 := by
      norm_num [OnE1, E1Rhs] at hE ⊢
      exact hE
    exact ⟨rfl, rat_sq_eq_four hYsq⟩
  · right
    have hYsq : Y^2 = 36 := by
      norm_num [OnE1, E1Rhs] at hE ⊢
      exact hE
    exact ⟨rfl, rat_sq_eq_thirtysix hYsq⟩
```

Reverse direction of the final iff is just finite evaluation:

```lean
theorem pointList_onE1 {X Y : ℚ}
    (h : E1AffinePointList X Y) : OnE1 X Y := by
  rcases h with h | h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;>
    norm_num [OnE1, E1Rhs]
```

---

## 10. Final assembly proof outline

```lean
theorem E1AffinePointList_of_coverCertificate
    (cert : E1FullCoverCertificate) (X Y : ℚ) :
    OnE1 X Y ↔ E1AffinePointList X Y := by
  constructor
  · intro hE
    by_cases hY0 : Y = 0
    · subst Y
      have hX := zeroY_forces_X_torsion hE
      rcases hX with hXm3 | hX0 | hX1
      · left; exact ⟨hXm3, rfl⟩
      · right; left; exact ⟨hX0, rfl⟩
      · right; right; left; exact ⟨hX1, rfl⟩
    · have hX := nonzeroY_forces_X_neg1_or_3 cert hE hY0
      have hYvals := Y_values_after_X_neg1_or_3 hE hX
      rcases hYvals with hneg | hpos
      · rcases hneg with ⟨hXneg, hY⟩
        rcases hY with hY2 | hYm2
        · right; right; right; left; exact ⟨hXneg, hY2⟩
        · right; right; right; right; left; exact ⟨hXneg, hYm2⟩
      · rcases hpos with ⟨hX3, hY⟩
        rcases hY with hY6 | hYm6
        · right; right; right; right; right; left; exact ⟨hX3, hY6⟩
        · right; right; right; right; right; right; exact ⟨hX3, hYm6⟩
  · intro hlist
    exact pointList_onE1 hlist
```

This is the desired branch structure:

```text
Y = 0
  -> X(X-1)(X+3)=0
  -> X=-3 or X=0 or X=1.

Y ≠ 0
  -> full-cover extraction into S23 representatives and CoverAtXQ
  -> nonzero factors and real sign compatibility
  -> finite partition: obstructed28 or residual4
  -> local table kills obstructed28
  -> residual4:
       (3,2,6)      -> FourRatSquaresAPConst -> A^2=T^2 -> X=3 -> Y=±6
       (-1,-2,2)    -> FourRatSquaresAPConst -> A^2=T^2 -> X=-1 -> Y=±2
       (1,1,1)      -> DoubleLeg -> B=0 -> X=1, contradicts Y≠0 branch
       (-3,-1,3)   -> DoubleLeg -> A=0 or C=0 -> X=0 or X=-3, contradicts Y≠0 branch.
```

---

## 11. What should compile now vs. what is honest residual

### Pure algebra / finite wrappers that should compile now

These are not mathematically trusted inputs:

```text
S23Rep / ProductSquareOK / CoverQ / CoverAtXQ definitions
NonzeroFactors / RealSignCompatible definitions
ObstructedTriple28 / ResidualTriple4 definitions
triple_partition_after_sign
nonzeroFactors_of_onE1_ne_zero
realSignCompatible_of_coverAtX
coverQ_3_2_6_from_fourSquaresAP
coverQ_neg1_neg2_2_from_fourSquaresAP
coverQ_1_1_1_from_doubleLeg
coverQ_neg3_neg1_3_from_doubleLeg
zeroY_forces_X_torsion
rat_sq_eq_four
rat_sq_eq_thirtysix
Y_values_after_X_neg1_or_3
pointList_onE1
final iff assembly after the certificate fields
```

The only mildly annoying wrappers are `realSignCompatible_of_coverAtX` and the final `field_simp` steps, but they are still pure rational order/field arithmetic.

### Honest residuals / assumptions

Exactly these four fields of `E1FullCoverCertificate`:

```lean
structure E1FullCoverCertificate : Prop where
  extract : FullCoverExtraction
  local28 : LocalObstructionTable28
  fourAP : FourRatSquaresAPConst
  doubleLeg : DoubleLegRightTrianglesDegenerate
```

Interpretation:

* `extract` is the squareclass extraction/valuation theorem.  This is where one proves that a nonzero-`Y` E1 point produces representatives in `S23Rep` and the anchored cover equations.
* `local28` is a finite congruence table.  It should eventually be a checked `Int`/`ZMod` certificate, but it is not global arithmetic.
* `fourAP` is Fermat's theorem: no nonconstant four rational squares in AP.
* `doubleLeg` is the Ljunggren/Pocklington/Eisenstein quartic descent in the double-right-triangle form.

No rank-zero theorem, torsion reduction, elliptic-curve group law, or quotient squareclass machinery is needed for this full-cover assembly theorem.

---

## 12. Adversarial checks

1. Do not let the local table kill `(3,2,6)`, `(-1,-2,2)`, `(1,1,1)`, or `(-3,-1,3)`.  Q2383 shows these are genuinely global residual covers, not finite local contradictions.

2. Keep `T ≠ 0` inside `CoverAtXQ`.  It is essential for the `(1,1,1)` double-leg wrapper to conclude `B=0`.

3. The degenerate residual covers are not extra affine nonzero-`Y` points.  In the nonzero branch they force `X=1`, `X=0`, or `X=-3`, which contradicts `Y≠0`; those torsion points are handled only by the `Y=0` branch.

4. Do not use the expected point list in the cover extraction or local table.  The final point list is derived only after the residual wrappers force `X=-1` or `X=3` in the nonzero branch.

5. `ProductSquareOK` is still needed even with `S23Rep`; otherwise the enumeration is `8^3`, not the intended 64 product-square triples.

6. `RealSignCompatible` is pure and should remain outside the local table if you want the table to mean exactly the 28 finite 2-adic obstructions.  The 32 real-sign impossible triples are eliminated before invoking `local28`.

```lean
end
end FLT.Mazur.N12.FullCover
```
