[ask-gpt dm1 tid=9790027a +0s] dispatched, waiting for answer
[ask-gpt dm1 tid=9790027a +90s] waiting (status=processing)
[ask-gpt dm1 tid=9790027a +180s] waiting (status=processing)
[ask-gpt dm1 tid=9790027a +270s] waiting (status=processing)
[ask-gpt dm1 tid=9790027a +360s] waiting (status=processing)
[ask-gpt dm1 tid=9790027a +450s] waiting (status=processing)
[ask-gpt dm1 tid=9790027a +540s] waiting (status=processing)
[ask-gpt dm1 tid=9790027a +553s] terminal: status=completed
## Verdict

The shortest realistic proof of

```lean
xRep (n • Point.some x y h) ~ ![(W.Φ n).eval x, (W.ΨSq n).eval x]
```

is **not** a one-step induction `n → n+1`. A one-step proof needs the `y`-coordinate of `n • P`, hence essentially needs `ωₙ`. Since Mathlib explicitly marks `ωₙ` as TODO, the better route is an **x-only differential-addition induction**:

\[
x(A+B)\quad\text{from}\quad x(A),\,x(B),\,x(A-B).
\]

This avoids `ωₙ` completely. The price is one hard primitive: a projective `x`-only differential-addition formula for general Weierstrass curves.

Mathlib already has the division-polynomial objects `preΨ'`, `preΨ`, `ΨSq`, `Ψ`, `Φ`, `ψ`, `φ`, with the recurrences and the coordinate-ring congruences `mk_ψ`, `mk_Ψ_sq`, `mk_φ`; it also has `Point.xRep`, affine addition lemmas, and the slope/addition formulas. It does **not** currently have the x-coordinate correctness theorem for `[n]`. citeturn273620view0turn273620view2turn800373view1turn715045view2

---

# 1. Core statement and carrier

Use `ℤ` for the division-polynomial index, even if the final theorem is for `ℕ`.

```lean
namespace WeierstrassCurve

open Polynomial

variable {k : Type*} [Field k] [DecidableEq k]
variable (W : WeierstrassCurve k)

abbrev EPoint := W.toAffine.Point

def xPair (n : ℤ) (x : k) : Fin 2 → k :=
  ![(W.Φ n).eval x, (W.ΨSq n).eval x]
```

The target theorem should be:

```lean
theorem xRep_nsmul_same_xPair
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y)
    (n : ℕ) :
    SameP1
      ((n • (WeierstrassCurve.Affine.Point.some x y h : W.EPoint)).xRep)
      (W.xPair (n : ℤ) x) := by
  sorry
```

I would also prove the nonzero target-vector lemma in parallel:

```lean
theorem xPair_ne_zero_of_nonsingular
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y)
    (n : ℕ) :
    W.xPair (n : ℤ) x ≠ 0 := by
  -- easiest after `xRep_nsmul_same_xPair`,
  -- using `Point.xRep_ne_zero` plus a SameP1 nonzero transport lemma
  sorry
```

That nonzero lemma is needed for the reverse direction of

```lean
n • P = 0 ↔ (W.ΨSq n).eval x = 0.
```

---

# 2. The x-only differential-addition primitive

For points \(A,B,D=A-B\), the classical general-Weierstrass identity is

\[
x(A+B)+x(A-B)
=
\frac{
2x_Ax_B(x_A+x_B)
+b_2x_Ax_B
+b_4(x_A+x_B)
+b_6
}{
(x_A-x_B)^2
}.
\]

Equivalently,

\[
x(A+B)
=
\frac{
2x_Ax_B(x_A+x_B)
+b_2x_Ax_B
+b_4(x_A+x_B)
+b_6
}{
(x_A-x_B)^2
}
-x(A-B).
\]

Make this projective on `Fin 2 → k`.

```lean
namespace XOnly

variable {k : Type*} [Field k]
variable (W : WeierstrassCurve k)

@[simp] def X (v : Fin 2 → k) : k := v 0
@[simp] def Z (v : Fin 2 → k) : k := v 1

def Δ (A B : Fin 2 → k) : k :=
  X A * Z B - X B * Z A

def diffAddNum (A B D : Fin 2 → k) : k :=
  let XA := X A
  let ZA := Z A
  let XB := X B
  let ZB := Z B
  let XD := X D
  let ZD := Z D
  let d  := Δ A B
  let s  := XA * ZB + XB * ZA
  let n  :=
      2 * XA * XB * s
    + W.b₂ * XA * XB * ZA * ZB
    + W.b₄ * s * ZA * ZB
    + W.b₆ * (ZA * ZB)^2
  n * ZD - XD * d^2

def diffAddDen (A B D : Fin 2 → k) : k :=
  (Δ A B)^2 * Z D

def diffAddRep (A B D : Fin 2 → k) : Fin 2 → k :=
  ![diffAddNum W A B D, diffAddDen W A B D]
```

The main geometric primitive is:

```lean
theorem xRep_add_of_xRep_sub
    [DecidableEq k] [W.IsElliptic]
    (A B : W.toAffine.Point)
    (hsub : A - B ≠ 0) :
    SameP1
      ((A + B).xRep)
      (XOnly.diffAddRep W A.xRep B.xRep (A - B).xRep) := by
  -- cases A, B, A - B
  -- affine/affine case:
  --   use Point.add_of_X_ne/add_of_Y_eq/add_of_Y_ne as needed
  --   unfold slope/addX/addY/negY
  --   use equations of A and B
  --   field_simp
  --   ring
  -- zero/infinity cases:
  --   simp [XOnly.diffAddRep, XOnly.diffAddNum, XOnly.diffAddDen]
  sorry
```

The affine group-law API you use here is:

```lean
WeierstrassCurve.Affine.Point.add_some
WeierstrassCurve.Affine.Point.add_of_X_ne
WeierstrassCurve.Affine.Point.add_of_Y_eq
WeierstrassCurve.Affine.Point.add_of_Y_ne
WeierstrassCurve.Affine.Point.add_self_of_Y_eq
WeierstrassCurve.Affine.Point.add_self_of_Y_ne
WeierstrassCurve.Affine.Point.xRep_zero
WeierstrassCurve.Affine.Point.xRep_some
WeierstrassCurve.Affine.Point.xRep_neg
```

and the formula API:

```lean
WeierstrassCurve.Affine.slope
WeierstrassCurve.Affine.addX
WeierstrassCurve.Affine.addY
WeierstrassCurve.Affine.negY
WeierstrassCurve.Affine.addPolynomial_slope
```

Mathlib’s docs state the affine addition formulas, including the tangent/secant slope and `addX = ℓ² + a₁ℓ - a₂ - x₁ - x₂`; they also expose `addPolynomial_slope`, which factors the line-substitution cubic by the three relevant `x`-coordinates. citeturn113343view0turn113343view1

You also need homogeneity:

```lean
theorem diffAddRep_congr
    {A A' B B' D D' : Fin 2 → k}
    (hA : SameP1 A A')
    (hB : SameP1 B B')
    (hD : SameP1 D D') :
    SameP1
      (XOnly.diffAddRep W A B D)
      (XOnly.diffAddRep W A' B' D') := by
  -- `diffAddRep` is homogeneous of degrees:
  -- A-degree 2, B-degree 2, D-degree 1.
  -- Prove by expanding SameP1 and ring.
  sorry
```

This lemma is essential because the induction hypothesis gives projective equality, not definitional equality of representatives.

---

# 3. The EDS induction scheme

Do **not** recurse by `n+1`. Recurse by the EDS half-index recurrences.

For odd indices:

\[
2(m+2)+1=(m+3)+(m+2),
\]

with difference

\[
(m+3)-(m+2)=1.
\]

For even indices:

\[
2(m+3)=(m+4)+(m+2),
\]

with difference

\[
(m+4)-(m+2)=2.
\]

So the two algebraic compatibility lemmas are:

```lean
theorem xPair_diffAdd_odd
    (m : ℕ) (x : k) :
    SameP1
      (XOnly.diffAddRep W
        (W.xPair ((m + 3 : ℕ) : ℤ) x)
        (W.xPair ((m + 2 : ℕ) : ℤ) x)
        (W.xPair (1 : ℤ) x))
      (W.xPair ((2 * (m + 2) + 1 : ℕ) : ℤ) x) := by
  -- unfold xPair, diffAddRep, diffAddNum, diffAddDen
  -- reduce SameP1 to cross-multiplication
  -- simp [WeierstrassCurve.ΨSq_ofNat,
  --       WeierstrassCurve.Φ_ofNat,
  --       WeierstrassCurve.preΨ'_odd,
  --       WeierstrassCurve.preΨ'_even]
  -- ring
  sorry

theorem xPair_diffAdd_even
    (m : ℕ) (x : k) :
    SameP1
      (XOnly.diffAddRep W
        (W.xPair ((m + 4 : ℕ) : ℤ) x)
        (W.xPair ((m + 2 : ℕ) : ℤ) x)
        (W.xPair (2 : ℤ) x))
      (W.xPair ((2 * (m + 3) : ℕ) : ℤ) x) := by
  -- same style; this is the even EDS recurrence
  sorry
```

The recurrence lemmas feeding these are:

```lean
WeierstrassCurve.preΨ'_even
WeierstrassCurve.preΨ'_odd
WeierstrassCurve.ΨSq_ofNat
WeierstrassCurve.ΨSq_even
WeierstrassCurve.ΨSq_odd
WeierstrassCurve.Φ_ofNat
```

plus small simp lemmas:

```lean
WeierstrassCurve.preΨ'_zero
WeierstrassCurve.preΨ'_one
WeierstrassCurve.preΨ'_two
WeierstrassCurve.preΨ'_three
WeierstrassCurve.preΨ'_four
WeierstrassCurve.ΨSq_zero
WeierstrassCurve.ΨSq_one
WeierstrassCurve.ΨSq_two
WeierstrassCurve.ΨSq_three
WeierstrassCurve.ΨSq_four
WeierstrassCurve.Φ_zero
WeierstrassCurve.Φ_one
WeierstrassCurve.Φ_two
WeierstrassCurve.Φ_three
WeierstrassCurve.Φ_four
```

Mathlib’s division-polynomial file defines `ΨSq n = preΨ n ^ 2 * if Even n then Ψ₂Sq else 1`, gives the small cases, and provides the even/odd recurrence lemmas for `preΨ'`, `ΨSq`, `ψ`, and `Φ`. citeturn800373view3turn273620view2turn273620view3

The induction skeleton is:

```lean
theorem xRep_nsmul_same_xPair'
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y) :
    ∀ n : ℕ,
      SameP1
        ((n • (WeierstrassCurve.Affine.Point.some x y h : W.EPoint)).xRep)
        (W.xPair (n : ℤ) x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n IH =>
      by_cases hsmall : n ≤ 4
      · interval_cases n <;>
          simp [xPair,
                WeierstrassCurve.Affine.Point.xRep_zero,
                WeierstrassCurve.Affine.Point.xRep_some]
          -- n=2,3,4 need base lemmas below
      · rcases Nat.even_or_odd n with hEven | hOdd
        · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = 2 * (m + 3) := by
            omega
          subst hm

          by_cases h2P : 2 • (WeierstrassCurve.Affine.Point.some x y h : W.EPoint) = 0
          · -- two-torsion specialization branch
            exact xPair_even_twoTorsion W h h2P (m := m)
          ·
            let P : W.EPoint := WeierstrassCurve.Affine.Point.some x y h
            let A : W.EPoint := (m + 4) • P
            let B : W.EPoint := (m + 2) • P

            have hA :
                SameP1 A.xRep (W.xPair ((m + 4 : ℕ) : ℤ) x) := by
              exact IH (m + 4) (by omega)

            have hB :
                SameP1 B.xRep (W.xPair ((m + 2 : ℕ) : ℤ) x) := by
              exact IH (m + 2) (by omega)

            have hD :
                SameP1 (A - B).xRep (W.xPair (2 : ℤ) x) := by
              have hsub : A - B = 2 • P := by
                -- abelian group arithmetic
                simp [A, B, P]
                abel
              simpa [hsub] using IH 2 (by omega)

            have hsub_ne : A - B ≠ 0 := by
              intro hz
              have : 2 • P = 0 := by
                -- same hsub arithmetic
                simpa [A, B, P] using hz
              exact h2P this

            have hgeom :
                SameP1
                  ((A + B).xRep)
                  (XOnly.diffAddRep W A.xRep B.xRep (A - B).xRep) :=
              XOnly.xRep_add_of_xRep_sub W A B hsub_ne

            have halg :
                SameP1
                  (XOnly.diffAddRep W
                    (W.xPair ((m + 4 : ℕ) : ℤ) x)
                    (W.xPair ((m + 2 : ℕ) : ℤ) x)
                    (W.xPair (2 : ℤ) x))
                  (W.xPair ((2 * (m + 3) : ℕ) : ℤ) x) :=
              xPair_diffAdd_even W m x

            -- combine hgeom, diffAddRep_congr hA hB hD, halg,
            -- and `(A+B) = 2*(m+3) • P`
            sorry

        · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = 2 * (m + 2) + 1 := by
            omega
          subst hm

          let P : W.EPoint := WeierstrassCurve.Affine.Point.some x y h
          let A : W.EPoint := (m + 3) • P
          let B : W.EPoint := (m + 2) • P

          have hA :
              SameP1 A.xRep (W.xPair ((m + 3 : ℕ) : ℤ) x) := by
            exact IH (m + 3) (by omega)

          have hB :
              SameP1 B.xRep (W.xPair ((m + 2 : ℕ) : ℤ) x) := by
            exact IH (m + 2) (by omega)

          have hD :
              SameP1 (A - B).xRep (W.xPair (1 : ℤ) x) := by
            have hsub : A - B = P := by
              simp [A, B, P]
              abel
            simpa [hsub] using IH 1 (by omega)

          have hsub_ne : A - B ≠ 0 := by
            have hsub : A - B = P := by
              simp [A, B, P]
              abel
            simpa [hsub, P] using
              WeierstrassCurve.Affine.Point.some_ne_zero h

          have hgeom :
              SameP1
                ((A + B).xRep)
                (XOnly.diffAddRep W A.xRep B.xRep (A - B).xRep) :=
            XOnly.xRep_add_of_xRep_sub W A B hsub_ne

          have halg :
              SameP1
                (XOnly.diffAddRep W
                  (W.xPair ((m + 3 : ℕ) : ℤ) x)
                  (W.xPair ((m + 2 : ℕ) : ℤ) x)
                  (W.xPair (1 : ℤ) x))
                (W.xPair ((2 * (m + 2) + 1 : ℕ) : ℤ) x) :=
            xPair_diffAdd_odd W m x

          -- combine as in the even case
          sorry
```

This is the exact induction I would implement.

---

# 4. Base cases

Prove these as separate lemmas.

```lean
theorem xRep_nsmul_zero
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y) :
    SameP1
      ((0 • (WeierstrassCurve.Affine.Point.some x y h : W.EPoint)).xRep)
      (W.xPair (0 : ℤ) x) := by
  simp [xPair]

theorem xRep_nsmul_one
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y) :
    SameP1
      ((1 • (WeierstrassCurve.Affine.Point.some x y h : W.EPoint)).xRep)
      (W.xPair (1 : ℤ) x) := by
  simp [xPair]
```

For `n=2`, use the actual doubling formula. This is where `Ψ₂Sq` enters first.

```lean
theorem xRep_two_nsmul
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y) :
    SameP1
      ((2 • (WeierstrassCurve.Affine.Point.some x y h : W.EPoint)).xRep)
      (W.xPair (2 : ℤ) x) := by
  classical
  by_cases h2lin : y = W.toAffine.negY x y
  · -- 2P = O
    rw [two_nsmul]
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq h2lin]
    simp [xPair, WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two]
    -- use h2lin + curve equation to show Ψ₂Sq.eval x = 0
    -- via Ψ₂Sq_eq / twoTorsionPolynomial
    sorry
  · -- non-2-torsion doubling
    rw [two_nsmul]
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne h2lin]
    simp [xPair, WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two,
          WeierstrassCurve.Affine.Point.xRep_some,
          WeierstrassCurve.Affine.slope,
          WeierstrassCurve.Affine.addX]
    field_simp
    ring
```

For `n=3` and `n=4`, I recommend using the same differential-add primitive, not raw triple/quadruple affine group-law expansion:

```lean
theorem xRep_three_nsmul
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y) :
    SameP1
      ((3 • (WeierstrassCurve.Affine.Point.some x y h : W.EPoint)).xRep)
      (W.xPair (3 : ℤ) x) := by
  -- A = 2P, B = P, A - B = P.
  -- use xRep_two_nsmul, xRep_nsmul_one, xRep_add_of_xRep_sub,
  -- and a small algebra lemma:
  --   diffAddRep (xPair 2) (xPair 1) (xPair 1) ~ xPair 3
  sorry

theorem xRep_four_nsmul
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y) :
    SameP1
      ((4 • (WeierstrassCurve.Affine.Point.some x y h : W.EPoint)).xRep)
      (W.xPair (4 : ℤ) x) := by
  -- A = 3P, B = P, A - B = 2P,
  -- with a 2-torsion branch if 2P = 0.
  sorry
```

The reason `Ψ₂Sq` appears in every even denominator is exactly Mathlib’s definition:

```lean
W.ΨSq n = W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1
```

and for natural indices:

```lean
W.ΨSq ↑n = W.preΨ' n ^ 2 * if Even n then W.Ψ₂Sq else 1
```

So the even division polynomial vanishes at 2-torsion points, as it must. citeturn273620view2

---

# 5. Where `mk_ψ`, `mk_φ`, and `mk_Ψ_sq` fit

In the x-only differential-add proof above, you mostly **do not need** `mk_ψ` or `mk_φ`. You work directly with the univariate `Φ` and `ΨSq`.

Use `mk_ψ`, `mk_φ`, and `mk_Ψ_sq` only if you also want a coordinate-ring version:

```lean
-- schematic
theorem eval_ψ_sq_eq_eval_ΨSq
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    evalBivar x y (W.ψ n)^2 = (W.ΨSq n).eval x := by
  -- use CoordinateRing.mk_Ψ_sq W n
  sorry

theorem eval_φ_eq_eval_Φ
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    evalBivar x y (W.φ n) = (W.Φ n).eval x := by
  -- use CoordinateRing.mk_φ W n
  sorry
```

The relevant Mathlib declarations are:

```lean
WeierstrassCurve.Affine.CoordinateRing.mk_ψ
WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
WeierstrassCurve.Affine.CoordinateRing.mk_φ
```

They say, in the coordinate ring of the affine curve, that `ψₙ` agrees with `Ψₙ`, that `Ψₙ²` agrees with `C (ΨSqₙ)`, and that `φₙ` agrees with `C (Φₙ)`. These are transfer/congruence lemmas, not multiplication-by-`n` correctness lemmas. citeturn800373view1turn800373view2

So the role is:

```text
classical bivariate formula with ψ, φ
        ↓ mk_ψ / mk_Ψ_sq / mk_φ
univariate formula with ΨSq, Φ
```

but those lemmas alone will not prove the bivariate formula.

---

# 6. Direct consequence: `n • P = 0 ↔ ΨSq.eval x = 0`

Once `xRep_nsmul_same_xPair` and `xPair_ne_zero_of_nonsingular` exist, the root criterion is short.

```lean
theorem nsmul_eq_zero_iff_ΨSq_eval
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y)
    (n : ℕ) :
    n • (WeierstrassCurve.Affine.Point.some x y h : W.EPoint) = 0
      ↔
    (W.ΨSq (n : ℤ)).eval x = 0 := by
  classical
  let P : W.EPoint := WeierstrassCurve.Affine.Point.some x y h
  constructor
  · intro hn
    have hsame :
        SameP1 ((n • P).xRep) (W.xPair (n : ℤ) x) :=
      xRep_nsmul_same_xPair W h n
    rw [hn, WeierstrassCurve.Affine.Point.xRep_zero] at hsame
    -- SameP1 ![1,0] ![Φ,Ψ] gives Ψ = 0.
    exact SameP1.second_eq_zero_of_same_infty hsame

  · intro hψ
    by_contra hnzero
    cases hnp : n • P with
    | zero =>
        exact hnzero hnp
    | some xn yn hnonsing =>
        have hsame :
            SameP1
              ((n • P).xRep)
              (W.xPair (n : ℤ) x) :=
          xRep_nsmul_same_xPair W h n

        have htarget_ne :
            W.xPair (n : ℤ) x ≠ 0 :=
          xPair_ne_zero_of_nonsingular W h n

        rw [hnp, WeierstrassCurve.Affine.Point.xRep_some] at hsame

        -- With second coordinate of target equal to 0,
        -- SameP1 ![xn,1] ![Φ,0] forces Φ = 0.
        have hφ : (W.Φ (n : ℤ)).eval x = 0 :=
          SameP1.first_eq_zero_of_same_affine_and_second_zero hsame hψ

        exact htarget_ne (by
          ext i <;> fin_cases i <;> simp [xPair, hφ, hψ])
```

The exact helper names `second_eq_zero_of_same_infty` and `first_eq_zero_of_same_affine_and_second_zero` depend on your `SameP1` API. They are one-line determinant/projective-equivalence lemmas.

---

# 7. Can this really avoid `ωₙ`?

Yes, **if** you use differential addition. The proof never asks for the `y`-coordinate of `n • P`. It only uses

\[
x(A+B)\quad\text{from}\quad x(A),x(B),x(A-B).
\]

This is why the induction steps are:

```text
odd:  x((m+3)P + (m+2)P), difference P
even: x((m+4)P + (m+2)P), difference 2P
```

rather than

```text
x((n+1)P) from x(nP) and x(P).
```

A one-step proof cannot be x-only: `Point.add_some` computes `addX` from a slope, and the slope uses the `y`-coordinates. Mathlib’s affine formula docs make this explicit: the secant slope is `(y₁-y₂)/(x₁-x₂)`, and the tangent slope uses `2y₁+a₁x₁+a₃` in the denominator. citeturn113343view0

If the differential-add route becomes too hard, the minimal `ω` fragment needed is not all of `ωₙ` as a polished polynomial family, but enough to orient the multiple:

```lean
structure NsmulProjectiveRep
    (W : WeierstrassCurve k) (n : ℤ) where
  Ω : Polynomial (Polynomial k)
  same :
    -- projective representative of nP:
    -- [φₙ(P), Ωₙ(P), ψₙ(P)^3]
    True
```

More concretely, you would need a theorem of shape:

```lean
theorem projective_nsmul_rep_ψφΩ
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y)
    (n : ℤ) :
    SameP2
      ((zsmulPoint n (Point.some x y h)).projectiveRep)
      ![
        evalBivar x y (W.φ n),
        evalBivar x y (Ω W n),
        evalBivar x y (W.ψ n)^3
      ] := by
  sorry
```

Then x-coordinate formula follows by projection. But constructing even this minimal `Ω` essentially reopens the TODO mentioned in Mathlib’s division-polynomial docs. citeturn273620view0

---

# 8. Hardest sub-step

The genuine hard step is:

```lean
theorem xRep_add_of_xRep_sub
    [DecidableEq k] [W.IsElliptic]
    (A B : W.toAffine.Point)
    (hsub : A - B ≠ 0) :
    SameP1
      ((A + B).xRep)
      (XOnly.diffAddRep W A.xRep B.xRep (A - B).xRep)
```

This is the bridge from Mathlib’s affine group law to an x-only projective formula. Once you have it, the EDS induction is largely bookkeeping plus pure polynomial identities using `preΨ'_even`, `preΨ'_odd`, `ΨSq_ofNat`, and `Φ_ofNat`.

The second-hardest step is proving the two algebra lemmas:

```lean
xPair_diffAdd_odd
xPair_diffAdd_even
```

but those are at least “honest algebra”: unfold definitions, rewrite EDS recurrences, and `ring`.

So the best architecture is:

```text
1. Define xPair = [Φₙ(x), ΨSqₙ(x)].
2. Prove x-only differential addition for xRep.
3. Prove xPair is closed under that differential addition using EDS recurrences.
4. Strong-induct on n using:
   odd  n = (m+3)+(m+2), difference 1;
   even n = (m+4)+(m+2), difference 2.
5. Derive nP=0 ↔ ΨSqₙ(x)=0.
6. Use mk_ψ/mk_φ only for optional coordinate-ring/bivariate transfer lemmas.
```

That is the leanest path that avoids `ωₙ` while still proving the projective x-coordinate formula needed by both `n_torsion_card` and `preΨ'` separability.
