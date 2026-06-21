[ask-gpt dm2 tid=1e697303 +0s] dispatched, waiting for answer
[ask-gpt dm2 tid=1e697303 +90s] waiting (status=processing)
[ask-gpt dm2 tid=1e697303 +180s] waiting (status=processing)
[ask-gpt dm2 tid=1e697303 +270s] waiting (status=processing)
[ask-gpt dm2 tid=1e697303 +360s] waiting (status=processing)
[ask-gpt dm2 tid=1e697303 +450s] waiting (status=processing)
[ask-gpt dm2 tid=1e697303 +540s] waiting (status=processing)
[ask-gpt dm2 tid=1e697303 +630s] waiting (status=processing)
[ask-gpt dm2 tid=1e697303 +720s] waiting (status=processing)
[ask-gpt dm2 tid=1e697303 +810s] waiting (status=processing)
[ask-gpt dm2 tid=1e697303 +900s] waiting (status=processing)
[ask-gpt dm2 tid=1e697303 +990s] waiting (status=processing)
[ask-gpt dm2 tid=1e697303 +1059s] terminal: status=completed
## High-level verdict

For the **forward obstruction axioms**, do **not** model N14 or N16 as elliptic obstruction curves unless the obstruction is deliberately factoring through a cyclic-level quotient. The correct full moduli objects are higher genus:

```lean
X1(2,14)  -- genus 4, explicit bidegree-(3,3) curve in P¹ × P¹
X1(2,16)  -- higher genus; treat as genus-5/full-level object, not 20a4
```

The tractable Lean route is probably **not** to prove the full higher-genus rational-point theorems. For the **over-ℚ torsion exclusion**, use the forgetful maps:

```text
Z/2 × Z/14  ⇒  point of order 14  ⇒ X1(14)(ℚ)
Z/2 × Z/16  ⇒  point of order 16  ⇒ X1(16)(ℚ)
```

provided the project already has, or can separately prove, the cyclic `14` and `16` obstructions. That is much cheaper than formalizing rational points on `X1(2,14)` or `X1(2,16)` directly.

---

## 1. Correct obstruction curves / varieties

### N14: full curve is `X1(2,14)`, genus 4

The correct full modular curve is

```text
XΓ = X1(2,14)
```

with `Γ = Γ(2) ∩ Γ1(7)` in the Bruin–Najman setup. They state that `XΓ = X1(2,14)`, that `X1(14)` has genus `1`, and that `X1(14)` is the elliptic curve with Cremona label `14a4`, i.e. LMFDB-style `14.a4`. citeturn459706view0

They then prove:

```text
genus X1(2,14) = 4
```

and it has `18` cusps, `9` of index `2` and `9` of index `14`. citeturn459706view1

The explicit model they use is a smooth projective bidegree `(3,3)` curve in `P¹ × P¹`:

```text
(u^3 + u^2 - 2u - 1) v (v + 1)
+
(v^3 + v^2 - 2v - 1) u (u + 1)
= 0.
```

The nine rational cusps are:

```text
(0,0), (0,-1), (0,∞),
(-1,0), (-1,-1), (-1,∞),
(∞,0), (∞,-1), (∞,∞).
```

The other nine cusps are over `ℚ(ζ₇)^+`. citeturn459706view2

There is also an optimized affine model in Derickx–Sutherland:

```text
(u^2 + u) v^3
+ (u^3 + 2u^2 - u - 1) v^2
+ (u^3 - u^2 - 4u - 1) v
- u^2 - u
= 0.
```

They derive this from Jain’s elliptic-surface family for `X1(2,2n)` with `n = 7`; they note that the optimized equation has degree matching the gonality `3` of `X1(2,14)`. citeturn175566view1

So for N14:

```text
full obstruction curve: X1(2,14)
genus: 4
elliptic quotient: X1(14) ≅ 14.a4
not an elliptic curve itself
```

### N16: full curve is `X1(2,16)`, not `20a4`

The correct full moduli object for a rational subgroup

```text
ℤ/2ℤ × ℤ/16ℤ
```

is

```text
X1(2,16)
```

in the `X1(m,mn)` notation with `(m,mn) = (2,16)`, i.e. `m=2`, `n=8`.

Derickx–Sutherland define `Y1(m,mn)` as parameterizing triples `(E,P,Q)` with independent points `P` of order `m` and `Q` of order `mn`; `X1(m,mn)` is its compactification by cusps. They also give the associated congruence subgroup conditions. citeturn175566view3

For `m=2`, they explicitly describe a construction of models for `X1(2,2n)` using Jain’s family:

```text
E₂(q,t) : y² = x³ + (t² - qt - 2)x² - (t² - 1)(qt + 1)²x,
```

with a rational point of order `2` and a point of infinite order; imposing an equation on multiples of this point constructs `X1(2,2n)`. citeturn175566view1

They say optimized models for `X1(m,mn)` with `m² n ≤ 120` were constructed and made available electronically. Since `X1(2,16)` corresponds to `m=2,n=8`, we have `m²n = 32`, so it lies in their computed range. citeturn175566view0

I would **not** identify this curve with any elliptic curve label. In particular, it is **not** the earlier `20.a4` / `20a4` curve. The correct full N16 object is higher genus. I would treat the “genus 5” statement as the right project scope, but I did **not** find a compact printed model/LMFDB label for `X1(2,16)` in the sources I checked; I would verify the genus/model from the Derickx–Sutherland electronic model data before starting Lean code.

There is a smaller cyclic-level curve:

```text
X1(16)
```

which is genus `2`, and Bruin–Najman give the equation:

```text
v² - (u³ + u² - u + 1)v + u² = 0.
```

This is the correct curve for a **point of order 16**, not for the full `ℤ/2 × ℤ/16` structure. citeturn459706view5

So for N16:

```text
full obstruction curve: X1(2,16), higher genus, not elliptic, not 20.a4
cyclic quotient/forgetful target: X1(16), genus 2, equation above
```

---

## 2. Is there an N12-style elementary route?

### N14

For the **full curve** `X1(2,14)`, no: the published method is not an N12-style elementary elliptic descent.

Bruin–Najman determine the Jacobian:

```text
JΓ(ℚ) ≅ C₂ × C₂ × C₆ × C₁₈,
```

generated by differences of rational cusps. Their proof uses a decomposition of the genus-4 Jacobian up to isogeny, computations with newforms, nonvanishing of L-functions, Kato/BSD results for modular abelian varieties, finite-field reduction, and Khuri–Makdisi-style divisor computations. citeturn459706view3

That is far beyond current Mathlib/FLT infrastructure.

However, for **excluding rational `ℤ/2 × ℤ/14` torsion over ℚ**, there is a much cheaper route if cyclic order `14` is already excluded:

```text
ℤ/2 × ℤ/14 rational torsion
⇒ rational point of exact order 14
⇒ noncuspidal point on X1(14)(ℚ)
⇒ contradiction from the cyclic-14 obstruction.
```

This factors through the elliptic quotient

```text
X1(14) ≅ 14.a4.
```

So if the project already has the `X1(14)` / cyclic-14 obstruction, N14 forward should be reduced to a one-line group-theory/forgetful-map lemma rather than a genus-4 proof.

### N16

For the **full curve** `X1(2,16)`, also no elementary N12-style route is apparent. It is higher genus, and the explicit models are part of a modular-curve database/algorithmic construction, not a small rank-zero elliptic curve.

For **excluding rational `ℤ/2 × ℤ/16` torsion over ℚ**, the cheapest route is again forgetful:

```text
ℤ/2 × ℤ/16 rational torsion
⇒ rational point of exact order 16
⇒ noncuspidal point on X1(16)(ℚ)
⇒ contradiction from cyclic-16 obstruction.
```

This avoids the full `X1(2,16)` model. But it still requires a cyclic-16 rational-point theorem. The cyclic curve `X1(16)` is genus `2`, with the explicit model above, so this is a genus-2 rational-point problem rather than a genus-5 one. Bruin–Najman cite earlier work on the hyperelliptic involution of `X1(16)` and use the model in their quadratic-point analysis. citeturn459706view5

That is still not currently “Mathlib-easy,” but it is much more plausible than directly proving rational points on `X1(2,16)`.

---

## 3. Tractability verdicts and first lemmas to attempt

### N14 verdict

**Best Lean strategy:** avoid the full genus-4 curve if possible.

First lemma to attempt:

```lean
/--
A rational `Z/2 × Z/14` torsion structure gives a rational point
of exact order `14`.
-/
theorem Z2xZ14_has_point_order_14
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : HasSubgroupZ2xZN E 14) :
    ∃ P : (E⁄ℚ).Point, AddOrderOf P = 14 := by
  -- purely group-theoretic extraction from the second generator
  -- or from the embedding `ZMod 2 × ZMod 14 →+ E(ℚ)`
  ...
```

Then wire it to the existing cyclic-14 obstruction:

```lean
theorem no_Z2xZ14_of_no_cyclic14
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hno14 : ¬ ∃ P : (E⁄ℚ).Point, AddOrderOf P = 14) :
    ¬ HasSubgroupZ2xZN E 14 := by
  intro h
  exact hno14 (Z2xZ14_has_point_order_14 E h)
```

If the project does **not** yet have cyclic-14, the next cheapest route is not `X1(2,14)` but `X1(14) ≅ 14.a4`. Bruin–Najman explicitly identify `X1(14)` with Cremona label `14a4`. citeturn459706view0

Only if the architecture truly requires the full forward map should you start with:

```lean
/--
Moduli map from a rational `Z/2 × Z/14` structure to the explicit
bidegree-(3,3) model of `X1(2,14)`.
-/
theorem Z2xZ14_gives_point_on_X1_2_14
    ... :
    ∃ u v : ℚ,
      (u^3 + u^2 - 2*u - 1) * v * (v + 1)
        + (v^3 + v^2 - 2*v - 1) * u * (u + 1) = 0
      ∧ NonCuspidal_N14 u v := by
  ...
```

But proving that all such rational points are cusps would be a genuine high-genus gap.

### N16 verdict

**Best Lean strategy:** also avoid the full `X1(2,16)` if possible.

First lemma to attempt:

```lean
/--
A rational `Z/2 × Z/16` torsion structure gives a rational point
of exact order `16`.
-/
theorem Z2xZ16_has_point_order_16
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : HasSubgroupZ2xZN E 16) :
    ∃ P : (E⁄ℚ).Point, AddOrderOf P = 16 := by
  -- extract the order-16 generator
  ...
```

Then:

```lean
theorem no_Z2xZ16_of_no_cyclic16
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hno16 : ¬ ∃ P : (E⁄ℚ).Point, AddOrderOf P = 16) :
    ¬ HasSubgroupZ2xZN E 16 := by
  intro h
  exact hno16 (Z2xZ16_has_point_order_16 E h)
```

If cyclic-16 is missing, first target the genus-2 curve `X1(16)` rather than full `X1(2,16)`:

```lean
/--
A rational point of exact order `16` gives a rational noncuspidal point
on the genus-2 model of `X1(16)`.
-/
theorem point_order_16_gives_X1_16_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : AddOrderOf P = 16) :
    ∃ u v : ℚ,
      v^2 - (u^3 + u^2 - u + 1) * v + u^2 = 0
      ∧ NonCuspidal_X1_16 u v := by
  ...
```

Then the hard theorem is:

```lean
theorem X1_16_rational_points_are_cusps :
    ∀ u v : ℚ,
      v^2 - (u^3 + u^2 - u + 1) * v + u^2 = 0 →
      IsCusp_X1_16 u v
```

This is a genus-2 rational-points theorem, still substantial. But it is the right smaller obstruction. Direct `X1(2,16)` should be a last resort.

---

## 4. Mathlib / FLT support and missing pieces

### What exists

FLT currently imports an axiom-level Mazur statement:

```lean
axiom Mazur_statement (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16
```

The comments in `FLT/Assumptions/Mazur.lean` explicitly state Mazur’s classification/bound and say the torsion subgroup size is at most `16`; the actual formal theorem is still an axiom. fileciteturn61file0L35-L41 fileciteturn61file0L105-L108

FLT’s elliptic torsion file has:

```lean
WeierstrassCurve.nTorsion
Module (ZMod n) (E.nTorsion n)
WeierstrassCurve.n_torsion_card
WeierstrassCurve.n_torsion_dimension
WeierstrassCurve.galoisRep
```

but many of these are still WIP or depend on earlier `sorry`s in the public mainline. fileciteturn62file0L33-L44 fileciteturn62file0L46-L74 fileciteturn62file0L98-L119

Mathlib has good **Weierstrass elliptic curve** infrastructure, affine point group law, rational arithmetic, polynomials/resultants, and division polynomials. That is enough for explicit genus-1 obstruction curves like the N10/N12-style work if you hand-code the curve and descent.

### What is missing

For the full N14/N16 forward obstructions, the missing infrastructure is much larger:

```lean
-- not currently available as reusable Mathlib/FLT APIs
ModularCurve X1(m,n)
explicit coarse moduli maps from torsion structures to X1(m,n)
high-genus curve models as first-class objects
Jacobian of a genus 4/5 curve
Picard group / symmetric powers / Abel-Jacobi maps
Khuri-Makdisi computations
Chabauty / Mordell-Weil sieve
rank-zero certificates for higher-genus Jacobians
```

This matters because the published N14 proof uses exactly such high-genus Jacobian machinery: genus-4 curve, Jacobian decomposition, rank zero, finite-field Jacobian computations, and effective divisor enumeration. citeturn459706view3 citeturn459706view4

Derickx–Sutherland’s general framework also leans on Jacobian rank-zero and gonality methods; they prove rank-zero results for many `J1(m,mn)` using modular forms/L-ratios and Magma computations. citeturn175566view0 citeturn175566view3

So the **Lean tractability verdict** is:

```text
N14 full X1(2,14) proof: deep gap.
N16 full X1(2,16) proof: deep gap.
N14 via cyclic 14 quotient: tractable if cyclic-14 obstruction exists.
N16 via cyclic 16 quotient: tractable only modulo a genus-2 X1(16)(ℚ) theorem.
```

---

## Recommended scoping decision

Do **not** start by formalizing `X1(2,14)` or `X1(2,16)`.

Instead, try to delete the two forward axioms by factoring through cyclic obstructions:

```lean
theorem Z2xZ14_excluded_by_cyclic14
    (cyc14 : ∀ E : WeierstrassCurve ℚ, [E.IsElliptic] →
      ¬ ∃ P : (E⁄ℚ).Point, AddOrderOf P = 14) :
    ∀ E : WeierstrassCurve ℚ, [E.IsElliptic] →
      ¬ HasSubgroupZ2xZN E 14 := ...

theorem Z2xZ16_excluded_by_cyclic16
    (cyc16 : ∀ E : WeierstrassCurve ℚ, [E.IsElliptic] →
      ¬ ∃ P : (E⁄ℚ).Point, AddOrderOf P = 16) :
    ∀ E : WeierstrassCurve ℚ, [E.IsElliptic] →
      ¬ HasSubgroupZ2xZN E 16 := ...
```

If cyclic `14` and `16` are not available, then the first real mathematical obstruction lemmas should be:

```lean
-- N14, preferred over full X1(2,14):
theorem X1_14_rational_points_are_cusps : ...

-- N16, preferred over full X1(2,16):
theorem X1_16_rational_points_are_cusps : ...
```

The full `X1(2,14)`/`X1(2,16)` rational-point determinations should be treated as **major future work**, not the next Lean build target.
