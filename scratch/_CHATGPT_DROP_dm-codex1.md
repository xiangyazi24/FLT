# Q2849 (dm-codex1): replacing `kubert_C12_square`

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Local file from prompt: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`  
Namespace: likely `MazurProof.RationalPointsN12`

Connector note: the local WIP file is not visible on GitHub `scratch`, so this is an API/formalization route audit from the prompt. Mathlib search shows no existing Tate-normal-form/Kubert-normal-form/modular-curve API; current public API is mainly `WeierstrassCurve` invariants, two-torsion polynomial, and limited division-polynomial infrastructure.

## 1. What theorem the axiom uses

The axiom is using the Kubert/Tate normal form classification for rational elliptic curves with a rational point of order `12`, plus the elementary full-rational-2-torsion criterion on the resulting Kubert `C12` family.

Mathematically, the route is:

```text
E(ℚ) contains Z/2 × Z/12
  ⇒ E has a rational point P of exact order 12
  ⇒ E is ℚ-isomorphic to the Kubert C12 family, parameterized by t
  ⇒ in the transformed model y^2 = x^3 + A12(t) x^2 + B12(t) x,
     nonsingularity is Delta12(t) ≠ 0
  ⇒ because E also has full rational 2-torsion, the quadratic factor
       x^2 + A12(t) x + B12(t)
     splits over ℚ
  ⇒ ∃ s : ℚ, s^2 = A12(t)^2 - 4*B12(t).
```

So the axiom is not merely a division-polynomial statement. It is a moduli/classification statement for `X_1(12)` plus a `full 2` splitting condition.

The statement is faithful as a **weak consequence** of Kubert: it only concludes the square condition on the `C12` parameter, not an actual isomorphism to the Kubert curve. A stronger faithful theorem would expose the isomorphism to the Kubert model and then derive this square condition.

## 2. Current Mathlib ingredients and gap

Mathlib has enough for the following low-level pieces:

```lean
#check WeierstrassCurve
#check WeierstrassCurve.Δ
#check WeierstrassCurve.twoTorsionPolynomial
#check WeierstrassCurve.IsElliptic
#check WeierstrassCurve.j
```

and some division-polynomial material, but search did not reveal a Tate normal form, Kubert family, `X_1(12)` moduli theorem, or quotient-by-subgroup machinery. Therefore a full proof from current Mathlib is not a small “use existing API” proof. It requires formalizing at least one of:

1. Tate normal form and Kubert’s `n=12` specialization; or
2. a direct algebraic normal-form theorem for curves with a rational point of order `12`; or
3. a modular-curve `X_1(12)` parametrization theorem.

The smallest viable route is option 1, because it is explicit algebra and avoids quotient-by-subgroup geometry.

## 3. Recommended local definitions

Expose the Kubert C12 model used downstream. The `A12/B12` formulas indicate the transformed model

```text
y^2 = x^3 + A12(t) x^2 + B12(t) x.
```

In Mathlib `WeierstrassCurve` convention

```text
Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆,
```

that is:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

noncomputable def KubertC12Curve (t : ℚ) : WeierstrassCurve ℚ :=
  { a₁ := 0
    a₂ := A12 t
    a₃ := 0
    a₄ := B12 t
    a₆ := 0 }

/-- Local placeholder if Mathlib has no convenient isomorphism relation for
Weierstrass curves preserving rational points. Replace this by the actual
Mathlib isomorphism/change-of-variables API if available locally. -/
def WeierstrassQIso (E W : WeierstrassCurve ℚ) : Prop :=
  ∃ u r s t0 : ℚ, u ≠ 0 ∧ True
```

Do not use this placeholder as a final theorem; it is only a marker for the missing change-of-variables API. If the local development already has a curve-isomorphism relation, use that instead.

## 4. Minimal honest replacement interfaces

### Layer A: group-theoretic extraction from `ZMod 2 × ZMod 12`

This layer should be easy and does not need Kubert.

```lean
/-- The injection supplies a point of exact order 12. -/
theorem point_order12_of_zmod2_zmod12_injection
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point)
    (hf : Function.Injective f) :
    ∃ P : (E⁄ℚ).Point, orderOf P = 12 := by
  refine ⟨f (0, 1), ?_⟩
  -- Use `orderOf_injective`/map-order APIs if available.
  -- The source element `(0,1)` has order 12 in `ZMod 2 × ZMod 12`.
  -- Injectivity gives preservation of order.
  sorry

/-- The injection also supplies full rational 2-torsion. -/
theorem full_two_torsion_of_zmod2_zmod12_injection
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point)
    (hf : Function.Injective f) :
    ∃ g : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point, Function.Injective g := by
  -- Restrict along `(a,b) ↦ (a, 6*b)`.
  let i : (ZMod 2 × ZMod 2) →+ (ZMod 2 × ZMod 12) :=
    { toFun := fun x => (x.1, (6 : ZMod 12) * (x.2 : ZMod 12))
      map_zero' := by ext <;> simp
      map_add' := by intro x y; ext <;> simp [mul_add] }
  refine ⟨f.comp i, ?_⟩
  -- Prove `i` injective by cases on `ZMod 2`; then compose with `hf`.
  intro x y hxy
  apply_fun id at hxy
  -- finite `native_decide`/`fin_cases` proof recommended.
  sorry
```

If `orderOf` on `(E⁄ℚ).Point` is annoying, define a lightweight exact-order predicate:

```lean
def HasPointOfExactOrder (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  ∃ P : (E⁄ℚ).Point, orderOf P = n
```

### Layer B: Kubert/Tate normal form theorem

This is the real mathematical replacement for the axiom.

```lean
/-- Kubert/Tate normal form for a rational point of exact order 12. This is
the main moduli theorem, and is the honest large replacement for the current axiom. -/
theorem kubert_C12_model_of_point_order12
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hP : ∃ P : (E⁄ℚ).Point, orderOf P = 12) :
    ∃ t : ℚ,
      Delta12 t ≠ 0 ∧
      WeierstrassQIso E (KubertC12Curve t) := by
  -- Requires formalizing Tate normal form and Kubert's n=12 specialization.
  sorry
```

A more explicit and more formalizable split is:

```lean
/-- General Tate normal form: a curve with a rational point of order at least 4
is isomorphic to a Tate normal form `E(b,c)` with the point `(0,0)`. -/
theorem tate_normal_form_of_point_order_ge_four
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {n : ℕ} (hn : 4 ≤ n)
    (hP : ∃ P : (E⁄ℚ).Point, orderOf P = n) :
    ∃ b c : ℚ, b ≠ 0 ∧ WeierstrassQIso E (TateNormalForm b c) := by
  sorry

/-- Kubert's explicit `n=12` condition and reparametrization. -/
theorem kubert_n12_parameter_from_tate_normal_form
    {b c : ℚ}
    (h : TateNormalFormHasPointOrder12 b c) :
    ∃ t : ℚ,
      Delta12 t ≠ 0 ∧
      WeierstrassQIso (TateNormalForm b c) (KubertC12Curve t) := by
  sorry
```

This is preferable to one monolithic theorem because the second theorem is just explicit rational algebra once the Tate normal form addition formulas are available.

### Layer C: full 2-torsion gives the square discriminant

This is the small algebraic bridge and should be checked locally.

For a curve

```text
y² = x³ + A x² + B x = x (x² + A x + B),
```

nonzero 2-torsion points have `y = 0`; besides `(0,0)`, the other two rational 2-torsion points exist iff the quadratic factor splits over `ℚ`, i.e. iff `A² - 4B` is a square.

```lean
/-- Full rational 2-torsion on `y^2 = x^3 + A*x^2 + B*x` forces the quadratic
factor to split, hence discriminant square. -/
theorem square_discriminant_of_full_two_torsion_on_monic_cubic
    {A B : ℚ}
    (hB : B ≠ 0)
    (hfull2 : ∃ g : (ZMod 2 × ZMod 2) →+ (({ a₁ := 0, a₂ := A, a₃ := 0, a₄ := B, a₆ := 0 } : WeierstrassCurve ℚ)⁄ℚ).Point,
      Function.Injective g) :
    ∃ s : ℚ, s ^ 2 = A ^ 2 - 4 * B := by
  -- Route:
  -- 1. Full 2-torsion gives at least two nonzero rational roots of
  --      x * (x^2 + A*x + B).
  -- 2. Since one root is `0` and `B ≠ 0`, the other nonzero 2-torsion roots
  --    are roots of `x^2 + A*x + B`.
  -- 3. A monic quadratic over Q with a rational root has discriminant square:
  --      if root is u, other root is -A-u, so discriminant = (u - (-A-u))^2.
  sorry

/-- Isomorphism transports full rational 2-torsion to the Kubert model. -/
theorem square_discriminant_of_full_two_torsion_on_kubertC12
    {E : WeierstrassCurve ℚ} [E.IsElliptic] {t : ℚ}
    (hDelta : Delta12 t ≠ 0)
    (hiso : WeierstrassQIso E (KubertC12Curve t))
    (hfull2 : ∃ g : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point, Function.Injective g) :
    ∃ s : ℚ, s ^ 2 = A12 t ^ 2 - 4 * B12 t := by
  -- Transport `hfull2` across `hiso`, then apply the previous theorem.
  -- `hDelta` should imply `B12 t ≠ 0`; prove as a small polynomial factor lemma.
  sorry
```

The polynomial implication is mechanical:

```lean
theorem B12_ne_zero_of_Delta12_ne_zero {t : ℚ} (hΔ : Delta12 t ≠ 0) :
    B12 t ≠ 0 := by
  intro hB
  unfold B12 Delta12 at hB hΔ
  -- `B12=0` means `(t^2-1)^6*(1+3t^2)^2=0`; then `Delta12=0`.
  -- `nlinarith`/`ring_nf` after `mul_eq_zero` splitting.
  sorry
```

### Layer D: final assembly theorem replacing the axiom

```lean
theorem kubert_C12_square_checked
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ t s : ℚ, Delta12 t ≠ 0 ∧ s ^ 2 = A12 t ^ 2 - 4 * B12 t := by
  rcases hE with ⟨f, hf⟩
  have hP12 : ∃ P : (E⁄ℚ).Point, orderOf P = 12 :=
    point_order12_of_zmod2_zmod12_injection E f hf
  have hfull2 : ∃ g : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point, Function.Injective g :=
    full_two_torsion_of_zmod2_zmod12_injection E f hf
  rcases kubert_C12_model_of_point_order12 E hP12 with ⟨t, hDelta, hiso⟩
  rcases square_discriminant_of_full_two_torsion_on_kubertC12 hDelta hiso hfull2 with ⟨s, hs⟩
  exact ⟨t, s, hDelta, hs⟩
```

## 5. More honest smaller replacement interface

If the full Tate normal form is too large now, replace the axiom by two smaller statements: one moduli statement and one checked algebra statement.

```lean
/-- Moduli/Kubert residual: a curve with a point of order 12 is isomorphic to
the explicit C12 Kubert model. -/
def KubertC12ModuliStatement : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    (∃ P : (E⁄ℚ).Point, orderOf P = 12) →
      ∃ t : ℚ, Delta12 t ≠ 0 ∧ WeierstrassQIso E (KubertC12Curve t)

/-- Algebraic residual: on the Kubert C12 model, an independent rational 2-torsion
subgroup forces the quadratic factor discriminant to be a square. -/
def KubertC12FullTwoAlgebraStatement : Prop :=
  ∀ {E : WeierstrassCurve ℚ} [E.IsElliptic] {t : ℚ},
    Delta12 t ≠ 0 →
    WeierstrassQIso E (KubertC12Curve t) →
    (∃ g : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point, Function.Injective g) →
      ∃ s : ℚ, s ^ 2 = A12 t ^ 2 - 4 * B12 t

theorem kubert_C12_square_of_moduli_and_fullTwo_algebra
    (hmod : KubertC12ModuliStatement)
    (halg : KubertC12FullTwoAlgebraStatement) :
    ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
      (∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) →
      ∃ t s : ℚ, Delta12 t ≠ 0 ∧ s ^ 2 = A12 t ^ 2 - 4 * B12 t := by
  intro E hEll hE
  letI := hEll
  rcases hE with ⟨f, hf⟩
  have hP12 := point_order12_of_zmod2_zmod12_injection E f hf
  have hfull2 := full_two_torsion_of_zmod2_zmod12_injection E f hf
  rcases hmod E hP12 with ⟨t, hDelta, hiso⟩
  rcases halg hDelta hiso hfull2 with ⟨s, hs⟩
  exact ⟨t, s, hDelta, hs⟩
```

This is a strict improvement over the current axiom: the first residual is a known Kubert moduli theorem; the second is elementary algebra and can be attacked independently.

## 6. Is anything false or overstrong?

No obvious falsehood in the current axiom, assuming the formulas `A12`, `B12`, `Delta12` are indeed the transformed Kubert `C12` family used downstream.

Important caveats:

1. The current conclusion is weaker than the true Kubert theorem because it drops the isomorphism to the Kubert model.
2. The statement depends on the exact normalization of `A12`, `B12`, and `Delta12`. A faithful proof must include an algebraic bridge from Kubert/Tate parameters to these formulas.
3. `s` is not required to be nonzero. That is fine: the downstream only needs a square witness. In fact, under `Delta12 t ≠ 0`, the discriminant should be nonzero anyway, but no need to strengthen the axiom.
4. The injection from `ZMod 2 × ZMod 12` is stronger than “there is a point of order 12”; it supplies full rational 2-torsion. This is exactly why the square condition follows.
5. Do not try to prove the square condition from `j`-invariant equality alone unless you also prove the full-2-torsion condition is transported to the chosen model. The square condition is model-specific to the `x^3 + A x^2 + B x` normalization.

## 7. Prioritized plan

### P0: shrink the axiom immediately

Replace `kubert_C12_square` by:

```lean
axiom kubert_C12_moduli : KubertC12ModuliStatement

theorem kubert_C12_square
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ t s : ℚ, Delta12 t ≠ 0 ∧ s ^ 2 = A12 t ^ 2 - 4 * B12 t :=
  kubert_C12_square_of_moduli_and_fullTwo_algebra kubert_C12_moduli
    kubertC12FullTwoAlgebra_checked E hE
```

where `kubertC12FullTwoAlgebra_checked` is proved by elementary 2-torsion/quadratic algebra.

### P1: prove the algebraic full-two bridge

Implement:

```lean
B12_ne_zero_of_Delta12_ne_zero
square_discriminant_of_full_two_torsion_on_monic_cubic
square_discriminant_of_full_two_torsion_on_kubertC12
```

This is much smaller than Kubert normal form.

### P2: formalize Tate normal form

Define `TateNormalForm b c`, prove the point `(0,0)` formulas, addition multiples, and the coordinate change from a curve with a point of exact order `n ≥ 4`.

### P3: formalize Kubert `n=12`

Prove the explicit parameter relation and transformation to `KubertC12Curve t`, including the displayed `A12/B12/Delta12` formulas. This is polynomial algebra after the Tate-normal-form setup.

## Bottom line

The current axiom is a mathematically faithful weak consequence of Kubert/Tate normal form plus full rational 2-torsion. Current Mathlib does not appear to contain the necessary Tate-normal-form or `X_1(12)` moduli theorem, so the honest replacement is a split interface:

```text
KubertC12ModuliStatement        -- large, known theorem / future formalization
KubertC12FullTwoAlgebraStatement -- small, checkable algebra
```

This decomposition is the best way to reduce the live axiom while keeping the remaining assumptions precise and non-misleading.
