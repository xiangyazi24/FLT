# Q325-dm1: division-polynomial x-doubling identity — Mathlib status and formal route

## Executive answer

Current Mathlib does **not** appear to contain the desired multiplication-by-`n` / x-coordinate composition API for division polynomials.  The files currently give definitions and recurrence/degree/map lemmas for `preΨ`, `ΨSq`, `Ψ`, `Φ`, `ψ`, and `φ`, but not a theorem of the shape

```lean
W.Φ (2*n) = dupNumH W (W.Φ n) (W.ΨSq n)
W.ΨSq (2*n) = dupDenH W (W.Φ n) (W.ΨSq n)
```

nor a projective version

```lean
W.Φ (2*n) * dupDenH W (W.Φ n) (W.ΨSq n)
  = W.ΨSq (2*n) * dupNumH W (W.Φ n) (W.ΨSq n)
```

The cleanest route is to prove the **stronger exact composition identities** first:

```lean
lemma ΨSq_two_mul (m : ℤ) :
    W.ΨSq (2*m) = dupDenH W (W.Φ m) (W.ΨSq m)

lemma Φ_two_mul (m : ℤ) :
    W.Φ (2*m) = dupNumH W (W.Φ m) (W.ΨSq m)
```

Then the requested projective equality is immediate by rewriting.

The local proof is parity-split.  After expanding `W.preΨ (2*m)`, `W.preΨ (2*m±1)`, `W.ΨSq (2*m)`, and `W.Φ (2*m)`, the certificate is not best stated as an uncancelled identity in the local ideal.  The good `linear_combination` target is the identity **multiplied by `W.Ψ₃`**.  Over the universal polynomial ring, `W.Ψ₃ ≠ 0`, so cancel there and transport the resulting polynomial identity to arbitrary coefficient rings.

---

## 1. Real Mathlib API currently relevant

The useful current Mathlib names are these.

From `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`:

```lean
WeierstrassCurve.Ψ₂Sq
WeierstrassCurve.Ψ₃
WeierstrassCurve.preΨ₄
WeierstrassCurve.preΨ
WeierstrassCurve.preΨ_even
WeierstrassCurve.preΨ_odd
WeierstrassCurve.ΨSq
WeierstrassCurve.ΨSq_even
WeierstrassCurve.ΨSq_odd
WeierstrassCurve.Φ
WeierstrassCurve.Φ_two
WeierstrassCurve.Φ_four
WeierstrassCurve.ψ
WeierstrassCurve.φ
WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
WeierstrassCurve.Affine.CoordinateRing.mk_φ
WeierstrassCurve.map_preΨ
WeierstrassCurve.map_ΨSq
WeierstrassCurve.map_Φ
```

In particular Mathlib has exactly these definition/recurrence facts:

```lean
W.preΨ_even (m : ℤ) :
  W.preΨ (2*m)
    = W.preΨ (m-1)^2 * W.preΨ m * W.preΨ (m+2)
      - W.preΨ (m-2) * W.preΨ m * W.preΨ (m+1)^2

W.preΨ_odd (m : ℤ) :
  W.preΨ (2*m+1)
    = W.preΨ (m+2) * W.preΨ m^3
        * (if Even m then W.Ψ₂Sq^2 else 1)
      - W.preΨ (m-1) * W.preΨ (m+1)^3
        * (if Even m then 1 else W.Ψ₂Sq^2)

W.ΨSq_even (m : ℤ) :
  W.ΨSq (2*m)
    = (W.preΨ (m-1)^2 * W.preΨ m * W.preΨ (m+2)
       - W.preΨ (m-2) * W.preΨ m * W.preΨ (m+1)^2)^2
      * W.Ψ₂Sq

W.ΨSq_odd (m : ℤ) :
  W.ΨSq (2*m+1)
    = (W.preΨ (m+2) * W.preΨ m^3
        * (if Even m then W.Ψ₂Sq^2 else 1)
       - W.preΨ (m-1) * W.preΨ (m+1)^3
        * (if Even m then 1 else W.Ψ₂Sq^2))^2
```

`Φ_two` is already the base x-duplication numerator:

```lean
@[simp] lemma WeierstrassCurve.Φ_two :
  W.Φ 2 = X^4 - C W.b₄ * X^2 - C (2 * W.b₆) * X - C W.b₈
```

and `ΨSq_two` is already the denominator:

```lean
@[simp] lemma WeierstrassCurve.ΨSq_two :
  W.ΨSq 2 = W.Ψ₂Sq
```

From `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`, the relevant facts are degree/leading coefficient facts only, e.g.

```lean
WeierstrassCurve.natDegree_preΨ
WeierstrassCurve.leadingCoeff_preΨ
WeierstrassCurve.natDegree_ΨSq
WeierstrassCurve.leadingCoeff_ΨSq
WeierstrassCurve.natDegree_Φ
WeierstrassCurve.leadingCoeff_Φ
```

These do not prove the duplication identity.

From `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`, Mathlib has affine group-law formulae:

```lean
WeierstrassCurve.Affine.addX_eq_addX_negY_sub
WeierstrassCurve.Affine.addY_sub_negY_addY
```

The first is the affine differential-addition formula

```text
x(P₁+P₂) = x(P₁-P₂)
           - ψ(P₁)ψ(P₂)/(x(P₂)-x(P₁))²,
ψ(x,y) = 2y + a₁x + a₃.
```

But Mathlib does not currently connect this to `W.Φ n / W.ΨSq n` for division polynomials.  So it is useful later, but it does not shortcut the division-polynomial theorem in one or two rewrites.

---

## 2. Definitions for the projective x-doubling map

Use these univariate homogeneous polynomials:

```lean
noncomputable def dupNumH (W : WeierstrassCurve R) (Xc Zc : R[X]) : R[X] :=
  Xc^4 - C W.b₄ * Xc^2 * Zc^2
    - C (2 * W.b₆) * Xc * Zc^3
    - C W.b₈ * Zc^4

noncomputable def dupDenH (W : WeierstrassCurve R) (Xc Zc : R[X]) : R[X] :=
  C (4 : R) * Xc^3 * Zc
    + C W.b₂ * Xc^2 * Zc^2
    + C (2 * W.b₄) * Xc * Zc^3
    + C W.b₆ * Zc^4
```

Then:

```lean
@[simp] lemma dupNumH_X_one :
    dupNumH W X 1 = W.Φ 2 := by
  simp [dupNumH]
  rw [W.Φ_two]
  ring

@[simp] lemma dupDenH_X_one :
    dupDenH W X 1 = W.ΨSq 2 := by
  simp [dupDenH, WeierstrassCurve.Ψ₂Sq]
```

The curve invariant relation needed in polynomial form is:

```lean
lemma b_relation (W : WeierstrassCurve R) :
    W.b₂ * W.b₆ - W.b₄^2 = 4 * W.b₈ := by
  -- name may already exist near the b-invariant API;
  -- otherwise unfold b₂ b₄ b₆ b₈ and `ring`.
  rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring
```

In polynomial form, the relation is:

```lean
C W.b₂ * C W.b₆ - C W.b₄^2 - C (4 : R) * C W.b₈ = 0
```

or, after `C_simp`,

```text
b₂*b₆ - b₄² - 4*b₈ = 0.
```

---

## 3. Parity-careful local expansion for the doubling theorem

Set the following abbreviations in a local polynomial proof:

```lean
let s  : R[X] := W.Ψ₂Sq
let c3 : R[X] := W.Ψ₃
let d4 : R[X] := W.preΨ₄

let Pm2 : R[X] := W.preΨ (m - 2)
let Pm1 : R[X] := W.preΨ (m - 1)
let P0  : R[X] := W.preΨ m
let P1  : R[X] := W.preΨ (m + 1)
let P2  : R[X] := W.preΨ (m + 2)

let E : R[X] := if Even m then s else 1
let O : R[X] := if Even m then 1 else s
```

Then:

```text
E * O = s
E² = if Even m then s² else 1
O² = if Even m then 1 else s²
```

The local forms of the current point are:

```text
Z := ΨSq(m) = P0² * E
F := Φ(m)   = X * Z - P1*Pm1 * O
```

The even recurrence gives:

```text
L := Pm1²*P2 - Pm2*P1²
preΨ(2m) = P0 * L
ΨSq(2m) = s * P0² * L²
```

The odd recurrences around `2m±1` give:

```text
Aplus  := P2*P0³*E² - Pm1*P1³*O²
Aminus := P1*Pm1³*O² - Pm2*P0³*E²

preΨ(2m+1) = Aplus
preΨ(2m-1) = Aminus
```

Since `2m` is even, the definition of `Φ` gives:

```text
Φ(2m) = X * ΨSq(2m) - preΨ(2m+1)*preΨ(2m-1)
      = X * s * P0² * L² - Aplus*Aminus.
```

These are the exact expansions to use before the polynomial certificate.

Lean skeleton:

```lean
lemma ΨSq_two_mul_expand (m : ℤ) :
    W.ΨSq (2*m)
      = W.Ψ₂Sq
        * W.preΨ m^2
        * (W.preΨ (m-1)^2 * W.preΨ (m+2)
             - W.preΨ (m-2) * W.preΨ (m+1)^2)^2 := by
  rw [W.ΨSq_even m]
  ring

lemma Φ_two_mul_expand (m : ℤ) :
    W.Φ (2*m)
      = X * W.Ψ₂Sq
          * W.preΨ m^2
          * (W.preΨ (m-1)^2 * W.preΨ (m+2)
               - W.preΨ (m-2) * W.preΨ (m+1)^2)^2
        - (W.preΨ (2*m+1) * W.preΨ (2*m-1)) := by
  rw [WeierstrassCurve.Φ]
  rw [W.ΨSq_even m]
  simp [show Even (2*m) from even_two_mul m]
  ring
```

For `preΨ (2m±1)`, use `W.preΨ_odd m` and `W.preΨ_odd (m-1)`, plus:

```lean
have hm1 : Even (m - 1) ↔ ¬ Even m := by omega
```

or prove the parity rewrite directly by `omega` / existing `Int.even_sub` simp lemmas.

---

## 4. Local EDS relations needed for the doubling certificate

The local identities needed are the translated `GapRel(m,2)` and the invariant relation for the actual bivariate `ψ` sequence, rewritten in the `preΨ` variables.

With the abbreviations above:

```text
Adj(m):
Pm2*P2 - O²*Pm1*P1 + c3*P0² = 0.
```

Check by parity:

```text
m even: Pm2*P2 - Pm1*P1 + c3*P0² = 0
m odd:  Pm2*P2 - s²*Pm1*P1 + c3*P0² = 0
```

The invariant relation is:

```text
Inv(m):
c3 * (P2*Pm1² + P1²*Pm2 + E²*P0³)
  - (d4 + s²) * P1*P0*Pm1 = 0.
```

Check by parity:

```text
m even:
c3 * (P2*Pm1² + P1²*Pm2 + s²*P0³)
  - (d4+s²)*P1*P0*Pm1 = 0

m odd:
c3 * (P2*Pm1² + P1²*Pm2 + P0³)
  - (d4+s²)*P1*P0*Pm1 = 0
```

The curve relation is:

```text
bRel:
b₂*b₆ - b₄² - 4*b₈ = 0.
```

Important saturation/cancellation point: the clean local polynomial certificate is:

```text
c3 * (dupDenH(F,Z) - s*P0²*L²) ∈ ideal(Adj(m), Inv(m), bRel)
```

and

```text
c3 * (dupNumH(F,Z) - (X*s*P0²*L² - Aplus*Aminus))
  ∈ ideal(Adj(m), Inv(m), bRel).
```

I verified this algebraically with the parity split.  In Lean, state these as two universal local `ring_nf` / `linear_combination` lemmas after `by_cases hm : Even m`.  Do **not** try to prove the uncancelled local identity directly from `Adj`, `Inv`, and `bRel`; the ideal membership target wants the extra multiplier `c3 = W.Ψ₃`.  After proving the multiplied identity over the universal polynomial ring, cancel `W.Ψ₃ ≠ 0` there and transport to arbitrary rings by the existing map lemmas.

A Lean-facing theorem shape:

```lean
lemma Ψ₃_mul_dupDenH_sub_ΨSq2m_local
    (hm : Even m) :
    W.Ψ₃ *
      (dupDenH W (W.Φ m) (W.ΨSq m) - W.ΨSq (2*m)) = 0 := by
  -- 1. expand `Φ`, `ΨSq`, `preΨ_even`, `preΨ_odd`
  -- 2. rewrite `Adj(m)`, `Inv(m)`, and `b_relation W`
  -- 3. `ring_nf`
  sorry

lemma Ψ₃_mul_dupNumH_sub_Φ2m_local
    (hm : Even m) :
    W.Ψ₃ *
      (dupNumH W (W.Φ m) (W.ΨSq m) - W.Φ (2*m)) = 0 := by
  -- same parity split and same three relations
  sorry
```

Over a universal domain:

```lean
lemma Ψ₃_ne_zero_universal : Wuniv.Ψ₃ ≠ 0 := by
  -- easiest: unfold `Ψ₃`; coefficient of X^4 is 3.
  -- Over ℤ[...] this coefficient is nonzero.
  -- Alternatively use degree/leading coefficient facts if your universal curve is set up for them.
  sorry
```

Then:

```lean
lemma dupDenH_eq_ΨSq_two_mul_universal (m : ℤ) :
    dupDenH Wuniv (Wuniv.Φ m) (Wuniv.ΨSq m) = Wuniv.ΨSq (2*m) := by
  have h := Ψ₃_mul_dupDenH_sub_ΨSq2m_local (W := Wuniv) m
  exact sub_eq_zero.mp <| mul_left_cancel₀ Ψ₃_ne_zero_universal h

lemma dupNumH_eq_Φ_two_mul_universal (m : ℤ) :
    dupNumH Wuniv (Wuniv.Φ m) (Wuniv.ΨSq m) = Wuniv.Φ (2*m) := by
  have h := Ψ₃_mul_dupNumH_sub_Φ2m_local (W := Wuniv) m
  exact sub_eq_zero.mp <| mul_left_cancel₀ Ψ₃_ne_zero_universal h
```

Finally map to arbitrary `R` using:

```lean
WeierstrassCurve.map_Ψ₂Sq
WeierstrassCurve.map_Ψ₃
WeierstrassCurve.map_preΨ₄
WeierstrassCurve.map_preΨ
WeierstrassCurve.map_ΨSq
WeierstrassCurve.map_Φ
```

This is the same universal-polynomial transport pattern as your unconditional Ward theorem.

---

## 5. Resulting projective equality

Once the two exact identities are proved, the projective equality is just:

```lean
lemma Φ_ΨSq_two_mul_projective (m : ℤ) :
    W.Φ (2*m) * dupDenH W (W.Φ m) (W.ΨSq m)
      = W.ΨSq (2*m) * dupNumH W (W.Φ m) (W.ΨSq m) := by
  rw [dupDenH_eq_ΨSq_two_mul, dupNumH_eq_Φ_two_mul]
  ring
```

Here the exact identities show the scalar `c` in the projective equality is actually `1`.

---

## 6. Differential-addition companion

Mathlib has the affine differential-addition lemma

```lean
WeierstrassCurve.Affine.addX_eq_addX_negY_sub
```

but it does **not** have the corresponding division-polynomial / Kummer-line composition theorem.

There is, however, a very clean EDS-core denominator identity for consecutive indices.  Define:

```text
Z0 := ΨSq(m)
F0 := Φ(m)
Z1 := ΨSq(m+1)
F1 := Φ(m+1)
Δ  := F1*Z0 - F0*Z1.
```

With the same `P_i`, `E`, `O` as above:

```text
Z0 = P0² * E
F0 = X*Z0 - P1*Pm1*O

Z1 = P1² * O
F1 = X*Z1 - P2*P0*E
```

Therefore:

```text
Δ = F1*Z0 - F0*Z1
  = -P2*P0³*E² + Pm1*P1³*O²
  = -preΨ(2m+1).
```

Hence the denominator identity is exact and needs no curve relation:

```lean
lemma ΨSq_two_mul_add_one_diffDen (m : ℤ) :
    W.ΨSq (2*m + 1)
      = (W.Φ (m+1) * W.ΨSq m - W.Φ m * W.ΨSq (m+1))^2 := by
  -- expand `Φ`, `ΨSq`, and `preΨ_odd m`; split on `Even m`; ring
  sorry
```

The numerator has the exact formal expansion:

```text
Φ(2m+1)
= X * Δ² - s * preΨ(2m) * preΨ(2m+2).
```

Using even recurrences:

```text
preΨ(2m) = P0 * (Pm1²*P2 - Pm2*P1²),
preΨ(2m+2) = P1 * (P0²*P3 - Pm1*P2²),
```

so

```text
Φ(2m+1)
= X*Δ²
  - s * P0*P1
      * (Pm1²*P2 - Pm2*P1²)
      * (P0²*P3 - Pm1*P2²).
```

This is the exact EDS formal identity:

```lean
lemma Φ_two_mul_add_one_diff_formal (m : ℤ) :
    W.Φ (2*m + 1)
      = X * (W.Φ (m+1) * W.ΨSq m - W.Φ m * W.ΨSq (m+1))^2
        - W.Ψ₂Sq * W.preΨ (2*m) * W.preΨ (2*m+2) := by
  rw [WeierstrassCurve.Φ]
  rw [ΨSq_two_mul_add_one_diffDen]
  simp [show ¬ Even (2*m+1) from Int.not_even_two_mul_add_one m]
  ring
```

This numerator identity still contains the signed product

```text
s * preΨ(2m) * preΨ(2m+2),
```

which is the x-only Kummer differential-addition sign data.  If you want a formula using only the three projective x-pairs

```text
[Φ_m, ΨSq_m], [Φ_{m+1}, ΨSq_{m+1}], [X,1],
```

then you need to formalize the generalized Weierstrass Kummer differential-addition biquadratic.  Mathlib's affine lemma `addX_eq_addX_negY_sub` is the right source, but the homogeneous Kummer formula is not currently exposed as a ready-to-use theorem.

So the practical companion sequence is:

```lean
-- easy denominator, EDS-only:
ΨSq(2*m+1)
  = (Φ(m+1)*ΨSq(m) - Φ(m)*ΨSq(m+1))^2

-- exact numerator, still carrying the signed product:
Φ(2*m+1)
  = X*(Φ(m+1)*ΨSq(m) - Φ(m)*ΨSq(m+1))^2
    - Ψ₂Sq * preΨ(2*m) * preΨ(2*m+2)
```

Do not claim a pure two-pair x-only numerator until the Kummer biquadratic has been separately stated and CAS-checked.

---

## 7. Recommended implementation order

1. Add `dupNumH` and `dupDenH`.
2. Prove the base simp lemmas:

   ```lean
   dupNumH W X 1 = W.Φ 2
   dupDenH W X 1 = W.ΨSq 2
   ```

3. Prove local parity expansion lemmas for `Φ m`, `ΨSq m`, `preΨ(2m)`, `preΨ(2m±1)`.
4. Prove translated local relations `Adj(m)` and `Inv(m)` for `preΨ` from your Ward/invariant infrastructure for the actual `ψ`/EDS sequence.
5. Prove the multiplied local certificates:

   ```lean
   W.Ψ₃ * (dupDenH W (W.Φ m) (W.ΨSq m) - W.ΨSq (2*m)) = 0
   W.Ψ₃ * (dupNumH W (W.Φ m) (W.ΨSq m) - W.Φ (2*m)) = 0
   ```

6. Over the universal curve polynomial ring, cancel `W.Ψ₃ ≠ 0`.
7. Transport the exact identities to arbitrary rings via the existing `map_...` lemmas.
8. Derive the requested projective cross-multiplication by rewriting.
9. Separately add the odd/consecutive denominator identity:

   ```lean
   W.ΨSq (2*m+1)
     = (W.Φ (m+1)*W.ΨSq m - W.Φ m*W.ΨSq (m+1))^2
   ```

10. For a fully x-only differential-addition numerator, first formalize the generalized Weierstrass Kummer biquadratic from `Affine.addX_eq_addX_negY_sub`; it is not currently a Mathlib division-polynomial theorem.
