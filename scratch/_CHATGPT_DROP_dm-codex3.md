# Q2396 drop: using Mathlib `not_fermat_42` for four rational squares in AP

Context from Mathlib:

```lean
import Mathlib.NumberTheory.FLT.Four

#check Fermat42
#check Fermat42.mul
#check not_fermat_42
```

The theorem in `.lake/packages/mathlib/Mathlib/NumberTheory/FLT/Four.lean` is:

```lean
theorem not_fermat_42 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
  a ^ 4 + b ^ 4 ≠ c ^ 2
```

## Bottom line

`not_fermat_42` is useful as a final contradiction **if** you can produce a nonzero instance

```lean
a^4 + b^4 = c^2.
```

However, a four-square arithmetic progression does **not** give such an instance by a short direct algebraic substitution.  The standard first reduction from

```text
w^2, x^2, y^2, z^2 in AP
```

lands in a different quartic/equivalent Euler-double-leg problem, not directly in `a^4 + b^4 = c^2`.

So the honest Lean advice is:

* Use `not_fermat_42` only behind an explicit bridge theorem
  `APToFermat42Bridge`, if you are willing to prove that bridge.
* Do **not** pretend the bridge is a `ring_nf`/`nlinarith` wrapper.  The naive Pythagorean-parametrization bridge fails exactly at a quartic with cubic terms, or equivalently at the Ljunggren/Euler double-leg quartic.
* For the FLT N=12 route, it is cleaner to keep `FourRatSquaresAPConst` as its own named residual, or prove it by a dedicated Fermat four-squares descent, rather than try to squeeze it out of `not_fermat_42` by a false one-line formula.

No part of this uses the `E1` rational-point list.

---

## 1. Integer theorem statement

Use the exact integer theorem as a `Prop`, so it can be a certificate field or a theorem later.

```lean
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

namespace FLT.Mazur.N12.FourSquaresAP

noncomputable section

/-- Integer four-square AP constancy. -/
def IntFourSquaresAPConst : Prop :=
  ∀ {w x y z : ℤ},
    x^2 - w^2 = y^2 - x^2 →
    y^2 - x^2 = z^2 - y^2 →
    w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2

/-- Rational four-square AP constancy, the desired N=12 interface. -/
def FourRatSquaresAPConst : Prop :=
  ∀ {w x y z : ℚ},
    x^2 - w^2 = y^2 - x^2 →
    y^2 - x^2 = z^2 - y^2 →
    w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2
```

The corresponding nonconstant bridge-to-Fermat statement is:

```lean
/-- A bridge strong enough to use Mathlib's `not_fermat_42`.

This is the exact missing step if one wants to use `not_fermat_42` as a black box.
The point of this definition is that this bridge is nontrivial; it is not a small
algebraic wrapper around the AP equations.
-/
def APToFermat42Bridge : Prop :=
  ∀ {w x y z : ℤ},
    x^2 - w^2 = y^2 - x^2 →
    y^2 - x^2 = z^2 - y^2 →
    ¬ (w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2) →
    ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a^4 + b^4 = c^2
```

Given such a bridge, `not_fermat_42` closes the integer theorem immediately:

```lean
theorem IntFourSquaresAPConst_of_APToFermat42Bridge
    (hbridge : APToFermat42Bridge) : IntFourSquaresAPConst := by
  intro w x y z h1 h2
  by_contra hnonconst
  obtain ⟨a, b, c, ha, hb, hfermat⟩ := hbridge h1 h2 hnonconst
  exact (not_fermat_42 (a := a) (b := b) (c := c) ha hb) hfermat
```

This theorem is worth adding because it makes the exact dependency boundary explicit.  But it does **not** solve the hard part: `APToFermat42Bridge` still needs a proof.

---

## 2. Where the direct reduction fails

Assume an integer AP of squares:

```text
x^2 - w^2 = y^2 - x^2,
y^2 - x^2 = z^2 - y^2.
```

Equivalently:

```text
w^2 + y^2 = 2*x^2,
x^2 + z^2 = 2*y^2.
```

The first equation gives a Pythagorean triple:

```text
(y + w)^2 + (y - w)^2 = (2*x)^2.
```

If one parametrizes this triple in the usual way, after a scale `λ` and a choice of signs one has, for one branch,

```text
y + w = λ * (2*m*n),
y - w = λ * (m^2 - n^2),
2*x   = λ * (m^2 + n^2).
```

Then

```text
2*y = λ * (m^2 - n^2 + 2*m*n),
2*x = λ * (m^2 + n^2).
```

The fourth-square condition is

```text
z^2 = 2*y^2 - x^2.
```

Multiplying by `4` gives the exact quartic:

```text
4*z^2 = λ^2 *
  (m^4 + 8*m^3*n + 2*m^2*n^2 - 8*m*n^3 + n^4).
```

This is **not** of the form

```text
a^4 + b^4 = c^2.
```

Trying simple substitutions such as `a = m+n`, `b = m-n` gives

```text
(m+n)^4 + (m-n)^4 = 2*m^4 + 12*m^2*n^2 + 2*n^4,
```

which has the wrong cubic terms and the wrong middle coefficient.  Thus this standard Pythagorean route does not provide the requested explicit `a,b,c` formulas.

A second classical normalization leads instead to Euler's double-square/double-leg shape:

```text
R^2 = 4*A^2 + D^2,
S^2 = 16*A^2 + D^2.
```

Parametrizing the first right triangle gives the Ljunggren-type quartic

```text
S^2 = m^4 + 14*m^2*n^2 + n^4,
```

again not `a^4 + b^4 = c^2`.  This is exactly the same global arithmetic frontier that appeared in Q2383 as `DoubleLegRightTrianglesDegenerate`/Ljunggren/Pocklington/Eisenstein, not a local algebra wrapper.

Therefore the requested direct roadmap

```text
nonconstant AP of integer squares -> explicit nonzero a,b,c with a^4+b^4=c^2
```

is not presently a manageable algebraic reduction.  It needs an additional classical descent/birational theorem.  If such a theorem is added, make it explicit as `APToFermat42Bridge`; otherwise keep `IntFourSquaresAPConst` or `FourRatSquaresAPConst` as the named residual.

---

## 3. A better honest intermediate if you still want to reuse existing N=12 residuals

The AP residual is very naturally connected to the double-leg theorem from Q2383:

```lean
/-- Double-leg right-triangle obstruction, same shape as Q2383. -/
def DoubleLegRightTrianglesDegenerate : Prop :=
  ∀ {x y h k : ℚ},
    h^2 = x^2 + y^2 →
    k^2 = (2*x)^2 + y^2 →
    x = 0 ∨ y = 0
```

For integers, use:

```lean
def IntDoubleLegRightTrianglesDegenerate : Prop :=
  ∀ {x y h k : ℤ},
    h^2 = x^2 + y^2 →
    k^2 = (2*x)^2 + y^2 →
    x = 0 ∨ y = 0
```

This immediately kills the Euler double-square shape:

```lean
def IntEulerDoubleSquareNo : Prop :=
  ∀ {A D R S : ℤ},
    A ≠ 0 → D ≠ 0 →
    R^2 = (2*A)^2 + D^2 →
    S^2 = (2*(2*A))^2 + D^2 →
    False

theorem IntEulerDoubleSquareNo_of_doubleLeg
    (hDL : IntDoubleLegRightTrianglesDegenerate) :
    IntEulerDoubleSquareNo := by
  intro A D R S hA hD hR hS
  have hdeg := hDL (x := 2*A) (y := D) (h := R) (k := S) hR hS
  rcases hdeg with h2A | hD0
  · exact hA (by nlinarith)
  · exact hD hD0
```

This is a valid algebra wrapper.  The hard part is proving `IntDoubleLegRightTrianglesDegenerate`, not applying it.

Can `not_fermat_42` prove `IntDoubleLegRightTrianglesDegenerate`?  Possibly by replaying a classical Fermat/Euler descent, but again not by a short substitution.  Parametrizing

```text
h^2 = x^2 + y^2,
k^2 = (2*x)^2 + y^2
```

leads to

```text
k^2 = u^4 + 14*u^2*v^2 + v^4
```

in the primitive branch, so an additional Ljunggren/Euler descent is still required.

---

## 4. Recommended Lean interfaces

### 4.1 If proving via Mathlib `not_fermat_42`

Use this dependency boundary:

```lean
structure FourSquaresAPViaFLT4Certificate : Prop where
  bridge : APToFermat42Bridge

 theorem IntFourSquaresAPConst_of_FLT4Certificate
    (cert : FourSquaresAPViaFLT4Certificate) : IntFourSquaresAPConst := by
  exact IntFourSquaresAPConst_of_APToFermat42Bridge cert.bridge
```

This says exactly what is needed to use Mathlib's theorem.

### 4.2 If not proving the bridge now

For the N=12 `E1` full-cover route, the honest frontier is simply:

```lean
structure FourSquaresAPCertificate : Prop where
  intAP : IntFourSquaresAPConst
```

or directly:

```lean
structure E1FullCoverGlobalInputs : Prop where
  fourRatSquaresAPConst : FourRatSquaresAPConst
  doubleLeg : DoubleLegRightTrianglesDegenerate
```

Do not hide `APToFermat42Bridge` inside a theorem named as if it were algebra.

---

## 5. Rational wrapper by common denominator

Once the integer theorem is available, the rational theorem is routine.

Use a common-denominator helper rather than fighting `Rat.den` at every call site:

```lean
/-- A common integer denominator package for four rationals. -/
structure RatCommonDen4 (w x y z : ℚ) where
  D : ℤ
  hD : D ≠ 0
  W X Y Z : ℤ
  hW : (W : ℚ) = (D : ℚ) * w
  hX : (X : ℚ) = (D : ℚ) * x
  hY : (Y : ℚ) = (D : ℚ) * y
  hZ : (Z : ℚ) = (D : ℚ) * z

/-- Standard denominator clearing helper. -/
def RatCommonDen4Exists : Prop :=
  ∀ w x y z : ℚ, Nonempty (RatCommonDen4 w x y z)
```

Then the wrapper is:

```lean
theorem FourRatSquaresAPConst_of_Int
    (hden : RatCommonDen4Exists)
    (hInt : IntFourSquaresAPConst) :
    FourRatSquaresAPConst := by
  intro w x y z h1 h2
  rcases (hden w x y z) with ⟨den⟩
  rcases den with ⟨D, hD, W, X, Y, Z, hW, hX, hY, hZ⟩

  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hD2 : (D : ℚ)^2 ≠ 0 := pow_ne_zero 2 hDq

  have h1_int : X^2 - W^2 = Y^2 - X^2 := by
    -- Prove by casting to `ℚ`, then use the common denominator identities.
    apply Rat.cast_injective
    calc
      ((X^2 - W^2 : ℤ) : ℚ)
          = (X : ℚ)^2 - (W : ℚ)^2 := by norm_num
      _ = ((D : ℚ) * x)^2 - ((D : ℚ) * w)^2 := by rw [hX, hW]
      _ = (D : ℚ)^2 * (x^2 - w^2) := by ring
      _ = (D : ℚ)^2 * (y^2 - x^2) := by rw [h1]
      _ = ((D : ℚ) * y)^2 - ((D : ℚ) * x)^2 := by ring
      _ = (Y : ℚ)^2 - (X : ℚ)^2 := by rw [hY, hX]
      _ = ((Y^2 - X^2 : ℤ) : ℚ) := by norm_num

  have h2_int : Y^2 - X^2 = Z^2 - Y^2 := by
    apply Rat.cast_injective
    calc
      ((Y^2 - X^2 : ℤ) : ℚ)
          = (Y : ℚ)^2 - (X : ℚ)^2 := by norm_num
      _ = ((D : ℚ) * y)^2 - ((D : ℚ) * x)^2 := by rw [hY, hX]
      _ = (D : ℚ)^2 * (y^2 - x^2) := by ring
      _ = (D : ℚ)^2 * (z^2 - y^2) := by rw [h2]
      _ = ((D : ℚ) * z)^2 - ((D : ℚ) * y)^2 := by ring
      _ = (Z : ℚ)^2 - (Y : ℚ)^2 := by rw [hZ, hY]
      _ = ((Z^2 - Y^2 : ℤ) : ℚ) := by norm_num

  have hconst := hInt h1_int h2_int
  rcases hconst with ⟨hWX, hXY, hYZ⟩

  have h_wx_scaled : (D : ℚ)^2 * w^2 = (D : ℚ)^2 * x^2 := by
    calc
      (D : ℚ)^2 * w^2 = ((D : ℚ) * w)^2 := by ring
      _ = (W : ℚ)^2 := by rw [← hW]
      _ = (X : ℚ)^2 := by exact_mod_cast hWX
      _ = ((D : ℚ) * x)^2 := by rw [hX]
      _ = (D : ℚ)^2 * x^2 := by ring

  have h_xy_scaled : (D : ℚ)^2 * x^2 = (D : ℚ)^2 * y^2 := by
    calc
      (D : ℚ)^2 * x^2 = ((D : ℚ) * x)^2 := by ring
      _ = (X : ℚ)^2 := by rw [← hX]
      _ = (Y : ℚ)^2 := by exact_mod_cast hXY
      _ = ((D : ℚ) * y)^2 := by rw [hY]
      _ = (D : ℚ)^2 * y^2 := by ring

  have h_yz_scaled : (D : ℚ)^2 * y^2 = (D : ℚ)^2 * z^2 := by
    calc
      (D : ℚ)^2 * y^2 = ((D : ℚ) * y)^2 := by ring
      _ = (Y : ℚ)^2 := by rw [← hY]
      _ = (Z : ℚ)^2 := by exact_mod_cast hYZ
      _ = ((D : ℚ) * z)^2 := by rw [hZ]
      _ = (D : ℚ)^2 * z^2 := by ring

  exact ⟨mul_left_cancel₀ hD2 h_wx_scaled,
         mul_left_cancel₀ hD2 h_xy_scaled,
         mul_left_cancel₀ hD2 h_yz_scaled⟩
```

The only missing helper here is `RatCommonDen4Exists`.  That is elementary: take

```lean
D = (w.den * x.den * y.den * z.den : ℤ)
```

and define each integer numerator by multiplying the corresponding `Rat.num` by the other three denominators.  It is safer to prove this helper once than to inline denominator clearing repeatedly.

---

## 6. Lean tactic hints

### Applying `not_fermat_42`

The final contradiction has this shape:

```lean
have hneq : a^4 + b^4 ≠ c^2 :=
  not_fermat_42 (a := a) (b := b) (c := c) ha hb
exact hneq hEq
```

or, with the `Fermat42` predicate:

```lean
have hf : Fermat42 a b c := ⟨ha, hb, hEq⟩
-- `not_fermat_42` wants the equality separately, not `Fermat42`.
exact (not_fermat_42 (a := a) (b := b) (c := c) hf.1 hf.2.1) hf.2.2
```

If a common scale appears, `Fermat42.mul` is already in Mathlib:

```lean
#check Fermat42.mul
```

This is useful for clearing denominators in a Fermat42 bridge, but it does not create the bridge from AP equations.

### PythagoreanTriples

`Mathlib.NumberTheory.FLT.Four` itself uses `PythagoreanTriple.coprime_classification'` internally.  It is relevant if you decide to prove one of the hard bridges by descent.  For example, from

```lean
have hpy : PythagoreanTriple (y + w) (y - w) (2*x) := by
  -- from `(y+w)^2 + (y-w)^2 = (2*x)^2`
```

a primitive/parity-normalized branch gives the parametrization above.  But the next equation is the quartic

```text
4*z^2 = λ^2*(m^4 + 8*m^3*n + 2*m^2*n^2 - 8*m*n^3 + n^4),
```

not `a^4+b^4=c^2`.  So `PythagoreanTriples` is a descent-building tool here, not a short proof of `FourRatSquaresAPConst` from `not_fermat_42`.

---

## 7. Recommended conclusion for the FLT repository

For the current N=12 formalization, I recommend this dependency stack:

```lean
-- hard/global, prove later or keep as a named residual
IntFourSquaresAPConst

-- elementary denominator wrapper
FourRatSquaresAPConst_of_Int

-- E1 full-cover residual wrapper uses
FourRatSquaresAPConst
```

If you specifically want to exploit Mathlib's `not_fermat_42`, add the transparent bridge interface:

```lean
APToFermat42Bridge
IntFourSquaresAPConst_of_APToFermat42Bridge
```

but do not mark `APToFermat42Bridge` as a small algebra lemma.  It is the real missing classical descent.  The naive explicit formula route fails at the quartics displayed above.

```lean
end
end FLT.Mazur.N12.FourSquaresAP
```
