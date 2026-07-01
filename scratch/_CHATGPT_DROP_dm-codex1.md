# Q2879 (dm-codex1): attacking the remaining Kubert C12 normal-form residual

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`  
Namespace: `MazurProof.RationalPointsN12`

Current residual:

```lean
structure KubertC12ShortWProjectiveModel (E : WeierstrassCurve ℚ) where
  t : ℚ
  hDelta : Delta12 t ≠ 0
  hB : B12 t ≠ 0
  pointAddEquiv :
    (E⁄ℚ).Point ≃+
      WeierstrassCurve.Projective.Point
        (WeierstrassCurve.toProjective (shortW (A12 t) (B12 t)))

axiom kubert_C12_shortW_projective_normal_form
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12ShortWProjectiveModel E
```

The right attack is to separate the number-theoretic Kubert/Tate theorem from two generic/checkable pieces:

1. the **Tate C12 parametrization**;
2. the **explicit variable change** from Tate C12 to your `shortW (A12 t) (B12 t)`;
3. the **generic point-group transport** induced by a Weierstrass `VariableChange`.

The important mathematical point is that your `A12/B12` model is **not** the raw Tate normal form. It is the short model obtained from the Tate normal form after a Möbius parameter choice, moving `6P` to `(0,0)`, killing the `a₁/a₃` terms, and scaling.

References for orientation: Kubert's universal torsion table; the Tate-normal-form algorithm paper by García--Olalla--Tornero; and the later geometric parametrization paper of Halbeisen--Hungerbühler--Voznyy--Shamsi Zargar for short models `y^2 = x^3 + ax^2 + bx` with `Z/12Z` torsion.

## 1. Standard Tate/Kubert C12 normal form

Use Tate normal form

```text
T(b,c) : y^2 + (1 - c)xy - b y = x^3 - b x^2,
P0 = (0,0).
```

In Mathlib coefficients:

```lean
def tateW (b c : ℚ) : WeierstrassCurve ℚ :=
  { a₁ := 1 - c
    a₂ := -b
    a₃ := -b
    a₄ := 0
    a₆ := 0 }
```

A convenient C12 parametrization is:

```text
b(q) = q(q - 1)(q^2 + 1)(3q^2 + 1) / (q + 1)^4,
c(q) = q(q - 1)(3q^2 + 1) / (q + 1)^3.
```

The point `(0,0)` on `T(b(q),c(q))` has exact order `12` when the usual nondegeneracy factors do not vanish. A good Lean predicate is deliberately factor-oriented:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open scoped WeierstrassCurve

namespace MazurProof.RationalPointsN12

noncomputable section

def tateW (b c : ℚ) : WeierstrassCurve ℚ :=
  { a₁ := 1 - c
    a₂ := -b
    a₃ := -b
    a₄ := 0
    a₆ := 0 }

def tateC12_b (q : ℚ) : ℚ :=
  q * (q - 1) * (q ^ 2 + 1) * (3 * q ^ 2 + 1) / (q + 1) ^ 4

def tateC12_c (q : ℚ) : ℚ :=
  q * (q - 1) * (3 * q ^ 2 + 1) / (q + 1) ^ 3

def tateC12W (q : ℚ) : WeierstrassCurve ℚ :=
  tateW (tateC12_b q) (tateC12_c q)

/--
Factor-level nondegeneracy for the C12 Tate parameter.
Over `ℚ`, `q^2 + 1` and `3*q^2 + 1` are automatic, but keeping them here makes
`Delta` proofs just `field_simp`/`ring` plus `mul_ne_zero`.
-/
structure TateC12Good (q : ℚ) : Prop where
  hq_ne_zero : q ≠ 0
  hq_sub_one : q - 1 ≠ 0
  hq_add_one : q + 1 ≠ 0
  hq_sq_add_one : q ^ 2 + 1 ≠ 0
  hthree_q_sq_add_one : 3 * q ^ 2 + 1 ≠ 0
  hthree_q_sq_sub_one : 3 * q ^ 2 - 1 ≠ 0

end MazurProof.RationalPointsN12
```

The Tate discriminant is:

```text
Δ(T_q) = q^6 (q - 1)^12 (q^2 + 1)^3 (3q^2 - 1) (3q^2 + 1)^4 / (q + 1)^24.
```

That formula is a pure algebra lemma once `tateC12_b/c` are defined.

```lean
namespace MazurProof.RationalPointsN12

noncomputable section

/-- Algebra-only discriminant formula for the Tate C12 model. -/
theorem tateC12W_discriminant_formula (q : ℚ) (hq1 : q + 1 ≠ 0) :
    (tateC12W q).Δ =
      q ^ 6 * (q - 1) ^ 12 * (q ^ 2 + 1) ^ 3 *
        (3 * q ^ 2 - 1) * (3 * q ^ 2 + 1) ^ 4 / (q + 1) ^ 24 := by
  -- Expand `WeierstrassCurve.Δ`, `b₂`, `b₄`, `b₆`, `b₈`, then clear denominators.
  -- This should be a `field_simp [tateC12W, tateW, tateC12_b, tateC12_c, hq1] <;> ring` proof.
  sorry

end MazurProof.RationalPointsN12
```

The standard theorem itself can be stated in two strengths.

### Stage 1A: immediate smaller residual, still returning `AddEquiv`

This is the least disruptive replacement for the current residual. It moves the residual target from your final short model back to the Tate C12 model.

```lean
namespace MazurProof.RationalPointsN12

noncomputable section

structure KubertC12TateProjectiveModel (E : WeierstrassCurve ℚ) where
  q : ℚ
  hgood : TateC12Good q
  pointAddEquiv :
    (E⁄ℚ).Point ≃+
      WeierstrassCurve.Projective.Point
        (WeierstrassCurve.toProjective (tateC12W q))

/--
Smaller Kubert residual: exact order-12 point puts the curve into Tate C12 normal form.
This is still a point-group equivalence residual, but no longer knows anything about the
special short model `A12/B12` or the full-two discriminant argument.
-/
axiom kubert_C12_tate_projective_normal_form
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12TateProjectiveModel E

end MazurProof.RationalPointsN12
```

### Stage 1B: better final residual, returning only a variable-change equality

This is the eventual target if you add a generic point-transport theorem for `VariableChange`.

```lean
namespace MazurProof.RationalPointsN12

noncomputable section

structure KubertC12TateVariableChangeModel (E : WeierstrassCurve ℚ) where
  q : ℚ
  hgood : TateC12Good q
  C : WeierstrassCurve.VariableChange ℚ
  hCurve : C • E = tateC12W q

/--
Best long-term Kubert residual: pure curve-level Tate normal form.
No full point-group equivalence is asserted here.
-/
axiom kubert_C12_tate_variableChange_normal_form
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12TateVariableChangeModel E

end MazurProof.RationalPointsN12
```

If you want the mathematically sharp version, add a field saying that the variable-change point map sends `P` to `(0,0)` on the Tate model. I would **not** add that field until the generic point map is available, because otherwise it forces another bespoke point-transport residual.

## 2. How this Tate model becomes your `shortW (A12 q) (B12 q)`

The C12 Tate parameters above are related to one raw conic parameter `v` by

```text
v = (1 - 3q) / (1 + q).
```

In Tate coordinates, the sixth multiple of `(0,0)` has coordinates

```text
x6(q) = (q - 1)(3q^2 + 1) / (4(q + 1)),
y6(q) = (q - 1)^2(3q^2 + 1)^2 / (8(q + 1)^3).
```

The variable change from the Tate model to your short model is the Mathlib `VariableChange` with

```text
u = 1 / (2(q + 1)^3),
r = x6(q),
s = (c(q) - 1) / 2,
t = y6(q).
```

Under Mathlib's convention, this means the admissible change

```text
X_old = u^2 X_new + r,
Y_old = u^3 Y_new + u^2 s X_new + t.
```

With these choices:

```text
C(q) • tateC12W q = shortW (A12 q) (B12 q).
```

Here are pasteable declarations/skeletons.

```lean
namespace MazurProof.RationalPointsN12

noncomputable section

def tateC12_x6 (q : ℚ) : ℚ :=
  (q - 1) * (3 * q ^ 2 + 1) / (4 * (q + 1))

def tateC12_y6 (q : ℚ) : ℚ :=
  (q - 1) ^ 2 * (3 * q ^ 2 + 1) ^ 2 / (8 * (q + 1) ^ 3)

noncomputable def tateC12ToShortVariableChange
    (q : ℚ) (hq1 : q + 1 ≠ 0) : WeierstrassCurve.VariableChange ℚ :=
  { u := Units.mk0 (1 / (2 * (q + 1) ^ 3)) (by
      -- `norm_num` proves `2 ≠ 0`; `hq1` proves `(q+1)^3 ≠ 0`.
      field_simp [hq1])
    r := tateC12_x6 q
    s := (tateC12_c q - 1) / 2
    t := tateC12_y6 q }

/--
Pure algebra: the explicit Tate C12 variable change is exactly the existing short model.
This is one of the highest-value checkable lemmas to add next.
-/
theorem tateC12_variableChange_eq_shortW
    (q : ℚ) (hq1 : q + 1 ≠ 0) :
    tateC12ToShortVariableChange q hq1 • tateC12W q =
      shortW (A12 q) (B12 q) := by
  -- `ext <;>` gives the five coefficient goals.
  -- The `a₁`, `a₃`, `a₆` goals close to zero; the `a₂/a₄` goals are exactly `A12/B12`.
  ext <;>
    simp [tateC12ToShortVariableChange, tateC12W, tateW,
      tateC12_b, tateC12_c, tateC12_x6, tateC12_y6,
      A12, B12, WeierstrassCurve.variableChange_def] <;>
    field_simp [hq1] <;>
    ring

end MazurProof.RationalPointsN12
```

This answers the “direct Kubert parameter?” question precisely: `A12/B12` is a **short-Weierstrass reparametrization of the C12 Tate family**, not the raw Tate normal form. The formulas above give the explicit rational substitution and the explicit Mathlib `VariableChange`.

## 3. Generic point transport for `VariableChange`

Mathlib has `VariableChange` as an action on curves, but not, as far as your local check indicates, a ready-made additive equivalence on `Projective.Point`. The next reusable theorem to prove or temporarily isolate is:

```lean
namespace MazurProof.RationalPointsN12

noncomputable section

/--
Generic missing Mathlib-style theorem: an admissible Weierstrass variable change induces an
additive equivalence on projective nonsingular point groups.

This is not Kubert-specific and should be much easier to audit than the current residual.
-/
axiom projectivePointAddEquivOfVariableChange
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective W) ≃+
      WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective (C • W))

/-- Same theorem with a named target curve, convenient for composition after a coefficient equality. -/
noncomputable def projectivePointAddEquivOfVariableChangeEq
    (W W' : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (hC : C • W = W') :
    WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective W) ≃+
      WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective W') := by
  subst hC
  exact projectivePointAddEquivOfVariableChange W C

end MazurProof.RationalPointsN12
```

Once this generic theorem exists, Stage 1B becomes preferable: the Kubert residual only gives `C • E = tateC12W q`; all point-group equivalences are produced generically.

Until then, Stage 1A is a safe intermediate split: the Kubert residual returns an `AddEquiv` to the Tate model, and only the Tate-to-short point transport is isolated in the generic variable-change theorem.

## 4. Rebuilding the current residual from smaller pieces

### From Stage 1A plus generic Tate-to-short transport

```lean
namespace MazurProof.RationalPointsN12

noncomputable section

/--
Reconstruct the current short-model residual from a smaller Tate residual plus the explicit
Tate-to-short variable change.
-/
theorem kubert_C12_shortW_projective_normal_form_from_tate_projective
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12ShortWProjectiveModel E := by
  rcases kubert_C12_tate_projective_normal_form E P hP with ⟨q, hgood, φTate⟩
  let Cshort := tateC12ToShortVariableChange q hgood.hq_add_one
  have hCshort : Cshort • tateC12W q = shortW (A12 q) (B12 q) := by
    simpa [Cshort] using tateC12_variableChange_eq_shortW q hgood.hq_add_one
  let φShort :
      WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective (tateC12W q)) ≃+
        WeierstrassCurve.Projective.Point
          (WeierstrassCurve.toProjective (shortW (A12 q) (B12 q))) :=
    projectivePointAddEquivOfVariableChangeEq
      (tateC12W q) (shortW (A12 q) (B12 q)) Cshort hCshort
  refine
    { t := q
      hDelta := ?_
      hB := ?_
      pointAddEquiv := φTate.trans φShort }
  · exact Delta12_ne_zero_of_TateC12Good hgood
  · exact B12_ne_zero_of_Delta12_ne_zero (Delta12_ne_zero_of_TateC12Good hgood)

end MazurProof.RationalPointsN12
```

### From Stage 1B plus generic source and Tate-to-short transport

This is the long-term final shape. The only Kubert residual is a curve-level variable-change statement.

```lean
namespace MazurProof.RationalPointsN12

noncomputable section

/--
Long-term replacement for the current residual: all point equivalences come from generic
variable-change transport.
-/
theorem kubert_C12_shortW_projective_normal_form_from_variable_changes
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12ShortWProjectiveModel E := by
  rcases kubert_C12_tate_variableChange_normal_form E P hP with ⟨q, hgood, CE, hCE⟩

  -- First equivalence: E to Tate C12.
  -- Depending on definitional unfolding of `(E⁄ℚ).Point`, this may need a tiny base-change-self
  -- adapter. Keep this adapter generic, not Kubert-specific.
  let φEtoTate :
      (E⁄ℚ).Point ≃+
        WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective (tateC12W q)) := by
    -- Skeleton: use `projectivePointAddEquivOfVariableChangeEq E (tateC12W q) CE hCE`.
    -- If `(E⁄ℚ).Point` is not definally the same as `Projective.Point (toProjective E)`,
    -- add a one-line generic `baseChangeSelfProjectivePointAddEquiv` adapter.
    exact by
      subst hCE
      exact projectivePointAddEquivOfVariableChange E CE

  -- Second equivalence: Tate C12 to the polynomial short model.
  let Cshort := tateC12ToShortVariableChange q hgood.hq_add_one
  have hCshort : Cshort • tateC12W q = shortW (A12 q) (B12 q) := by
    simpa [Cshort] using tateC12_variableChange_eq_shortW q hgood.hq_add_one
  let φTateToShort :
      WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective (tateC12W q)) ≃+
        WeierstrassCurve.Projective.Point
          (WeierstrassCurve.toProjective (shortW (A12 q) (B12 q))) :=
    projectivePointAddEquivOfVariableChangeEq
      (tateC12W q) (shortW (A12 q) (B12 q)) Cshort hCshort

  refine
    { t := q
      hDelta := ?_
      hB := ?_
      pointAddEquiv := φEtoTate.trans φTateToShort }
  · exact Delta12_ne_zero_of_TateC12Good hgood
  · exact B12_ne_zero_of_Delta12_ne_zero (Delta12_ne_zero_of_TateC12Good hgood)

end MazurProof.RationalPointsN12
```

## 5. Low-hanging checked algebra to add now

These are independent of the hard Kubert theorem and should be formalizable immediately.

### 5.1 Short-model cubic discriminant identities

For `shortW A B`, Mathlib's Weierstrass discriminant has the factor `16`; your `Delta12` is the cubic discriminant part `B^2 * (A^2 - 4B)`.

```lean
namespace MazurProof.RationalPointsN12

noncomputable section

/-- For the short model `y^2 = x^3 + A x^2 + B x`. -/
theorem shortW_discriminant_formula (A B : ℚ) :
    (shortW A B).Δ = 16 * B ^ 2 * (A ^ 2 - 4 * B) := by
  simp [shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- Key factorization behind the square-discriminant theorem. -/
theorem A12_sq_sub_four_B12 (q : ℚ) :
    A12 q ^ 2 - 4 * B12 q =
      256 * q ^ 6 * (q ^ 2 + 1) ^ 3 * (3 * q ^ 2 - 1) := by
  simp [A12, B12]
  ring

/-- Your `Delta12` is exactly `B12^2 * (A12^2 - 4B12)`. -/
theorem Delta12_eq_B12_sq_mul_A12_sq_sub_four_B12 (q : ℚ) :
    Delta12 q = B12 q ^ 2 * (A12 q ^ 2 - 4 * B12 q) := by
  rw [A12_sq_sub_four_B12]
  simp [Delta12, B12]
  ring

/-- Therefore `hB` is derivable from `hDelta`; it need not be a residual field. -/
theorem B12_ne_zero_of_Delta12_ne_zero {q : ℚ}
    (hDelta : Delta12 q ≠ 0) : B12 q ≠ 0 := by
  intro hB
  apply hDelta
  rw [Delta12_eq_B12_sq_mul_A12_sq_sub_four_B12, hB]
  simp

end MazurProof.RationalPointsN12
```

After this, you can simplify the current structure by removing `hB`:

```lean
structure KubertC12ShortWProjectiveModel' (E : WeierstrassCurve ℚ) where
  t : ℚ
  hDelta : Delta12 t ≠ 0
  pointAddEquiv :
    (E⁄ℚ).Point ≃+
      WeierstrassCurve.Projective.Point
        (WeierstrassCurve.toProjective (shortW (A12 t) (B12 t)))
```

and derive `hB` downstream using `B12_ne_zero_of_Delta12_ne_zero`.

### 5.2 Delta nonzero from factor-level Tate-good predicate

```lean
namespace MazurProof.RationalPointsN12

noncomputable section

theorem Delta12_ne_zero_of_TateC12Good {q : ℚ}
    (h : TateC12Good q) : Delta12 q ≠ 0 := by
  -- Unfold `Delta12`, then use `mul_ne_zero` and `pow_ne_zero` from the fields of `h`.
  simp [Delta12]
  repeat' apply mul_ne_zero
  · norm_num
  · exact pow_ne_zero 12 h.hq_sub_one
  · exact pow_ne_zero 12 h.hq_add_one
  · exact pow_ne_zero 4 h.hthree_q_sq_add_one
  · exact pow_ne_zero 6 h.hq_ne_zero
  · exact pow_ne_zero 3 h.hq_sq_add_one
  · exact h.hthree_q_sq_sub_one

/-- Convenient extraction of the denominator fact needed by `field_simp`. -/
theorem TateC12Good.denominator_ne {q : ℚ} (h : TateC12Good q) :
    (q + 1) ^ 24 ≠ 0 :=
  pow_ne_zero 24 h.hq_add_one

end MazurProof.RationalPointsN12
```

Depending on how `Delta12` is defined locally, the first proof may need a more explicit rewrite of `(q^2 - 1)^12` into `(q - 1)^12 * (q + 1)^12`. If so, add this helper:

```lean
theorem sq_sub_one_pow_twelve (q : ℚ) :
    (q ^ 2 - 1) ^ 12 = (q - 1) ^ 12 * (q + 1) ^ 12 := by
  have h : q ^ 2 - 1 = (q - 1) * (q + 1) := by ring
  rw [h, mul_pow]
```

### 5.3 Coordinate identities behind the Tate-to-short variable change

These are pure field/ring lemmas and should be checked before touching point groups.

```lean
namespace MazurProof.RationalPointsN12

noncomputable section

/-- The Tate order-2 condition for the computed `6P` coordinate. -/
theorem tateC12_sixP_order_two_coordinate_identity
    (q : ℚ) (hq1 : q + 1 ≠ 0) :
    2 * tateC12_y6 q + (1 - tateC12_c q) * tateC12_x6 q - tateC12_b q = 0 := by
  simp [tateC12_x6, tateC12_y6, tateC12_b, tateC12_c]
  field_simp [hq1]
  ring

/-- The `a₁` coefficient is killed by `s = (c-1)/2`. -/
theorem tateC12_kill_a1_identity (q : ℚ) :
    (1 - tateC12_c q) + 2 * ((tateC12_c q - 1) / 2) = 0 := by
  ring

/-- The `a₃` coefficient is killed after translating to the `6P` point. -/
theorem tateC12_kill_a3_identity (q : ℚ) (hq1 : q + 1 ≠ 0) :
    -tateC12_b q + tateC12_x6 q * (1 - tateC12_c q) +
      2 * tateC12_y6 q = 0 := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    tateC12_sixP_order_two_coordinate_identity q hq1

end MazurProof.RationalPointsN12
```

### 5.4 Distinguished point exact-order theorem

This is useful but lower priority than the algebra above. It touches Mathlib's group law, so I would isolate it after the variable-change algebra compiles.

```lean
namespace MazurProof.RationalPointsN12

noncomputable section

/-- Nonsingularity of `(0,0)` on the Tate C12 model. -/
theorem tateC12_origin_nonsingular {q : ℚ} (h : TateC12Good q) :
    (tateC12W q).toAffine.Nonsingular 0 0 := by
  -- Unfold `Affine.Nonsingular`, use `b(q) ≠ 0` from `h` and the discriminant formula.
  -- This should be algebraic.
  sorry

/-- The affine distinguished point `(0,0)` on the Tate C12 model. -/
noncomputable def tateC12OriginAffine (q : ℚ) (h : TateC12Good q) :
    WeierstrassCurve.Affine.Point (tateC12W q) :=
  .some 0 0 (tateC12_origin_nonsingular h)

/-- The projective distinguished point corresponding to `(0,0)`. -/
noncomputable def tateC12OriginProjective (q : ℚ) (h : TateC12Good q) :
    WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective (tateC12W q)) :=
  WeierstrassCurve.Affine.Point.toProjective (tateC12OriginAffine q h)

/-- Eventually checkable by explicit multiple formulas; keep separate from the main bridge. -/
theorem tateC12Origin_addOrderOf {q : ℚ} (h : TateC12Good q) :
    addOrderOf (tateC12OriginProjective q h) = 12 := by
  -- Prove explicit formulas for `2P`, `3P`, `4P`, `6P`; show `6P` is nonzero 2-torsion;
  -- rule out orders `1,2,3,4,6` using the nonzero factors in `h`.
  sorry

end MazurProof.RationalPointsN12
```

I would not block the main residual split on `tateC12Origin_addOrderOf`. The theorem is for proving the family has a point of order 12; the direction currently needed is the converse, from an existing order-12 point to the model.

## 6. Recommended staged work plan

### Stage 0: cleanup current residual fields

Add:

```lean
A12_sq_sub_four_B12
Delta12_eq_B12_sq_mul_A12_sq_sub_four_B12
B12_ne_zero_of_Delta12_ne_zero
```

Then remove `hB` from any residual structure if convenient, because `hB` follows from `hDelta`.

### Stage 1: introduce Tate C12 definitions and algebra

Add:

```lean
tateW
tateC12_b
tateC12_c
tateC12W
TateC12Good
tateC12W_discriminant_formula
Delta12_ne_zero_of_TateC12Good
```

No point maps yet.

### Stage 2: prove the explicit Tate-to-short variable change

Add:

```lean
tateC12_x6
tateC12_y6
tateC12ToShortVariableChange
tateC12_variableChange_eq_shortW
```

This is the highest-signal checkable step. It proves that the `A12/B12` family is not magic: it is the explicit short form of Tate C12.

### Stage 3: split the residual

Short-term split:

```lean
axiom kubert_C12_tate_projective_normal_form
```

plus generic variable-change point transport:

```lean
axiom projectivePointAddEquivOfVariableChange
```

Long-term split:

```lean
axiom kubert_C12_tate_variableChange_normal_form
```

and prove `projectivePointAddEquivOfVariableChange` once and for all.

### Stage 4: prove generic `VariableChange` point transport

This is a Mathlib-style project, not a Kubert project. The expected construction is:

1. define the projective coordinate map induced by `C : VariableChange ℚ`;
2. prove it preserves `Projective.Nonsingular`;
3. define forward and inverse maps using `C` and `C⁻¹`;
4. prove inverse laws by projective extensionality;
5. prove `map_add'` by reducing to the explicit projective group-law formulas or by transporting through affine formulas on charts.

Once this is done, the Kubert residual can stop returning `AddEquiv` entirely.
