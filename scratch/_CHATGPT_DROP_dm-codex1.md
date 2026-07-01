# Q2855 (dm-codex1): short Weierstrass full-2 algebra layer audit

Target local file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`  
Namespace: `MazurProof.RationalPointsN12`

## 0. Exact API names/shapes to check

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

#check WeierstrassCurve
#check WeierstrassCurve.IsElliptic
#check WeierstrassCurve.twoTorsionPolynomial
#check WeierstrassCurve.twoTorsionPolynomial_discr
#check WeierstrassCurve.twoTorsionPolynomial_discr_ne_zero_of_isElliptic

#check WeierstrassCurve.Affine.Equation
#check WeierstrassCurve.Affine.Nonsingular
#check WeierstrassCurve.Affine.equation_iff
#check WeierstrassCurve.Affine.nonsingular_iff
#check WeierstrassCurve.Affine.nonsingular_zero
#check WeierstrassCurve.Affine.negY

#check WeierstrassCurve.Affine.Point
#check WeierstrassCurve.Affine.Point.zero
#check WeierstrassCurve.Affine.Point.some
#check WeierstrassCurve.Affine.Point.mk
#check WeierstrassCurve.Affine.pointEquiv
#check WeierstrassCurve.Affine.pointEquiv_zero
#check WeierstrassCurve.Affine.pointEquiv_some
#check WeierstrassCurve.Affine.Point.some_ne_zero
#check WeierstrassCurve.Affine.Point.neg_some
#check WeierstrassCurve.Affine.Point.add_self_of_Y_eq
#check WeierstrassCurve.Affine.Point.add_self_of_Y_ne
#check WeierstrassCurve.Affine.Point.xRep
#check WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff

#check addOrderOf_injective
#check ZMod.addOrderOf_one
```

Important: `WeierstrassCurve.twoTorsionPolynomial` currently has discriminant support, but I did **not** find a ready theorem saying “nonzero 2-torsion points over `F` are exactly roots of `twoTorsionPolynomial`.” For this task, the affine point constructors and group-law lemmas are more direct than the polynomial API.

## 1. Short curve definition

```lean
namespace MazurProof.RationalPointsN12

noncomputable def shortW (A B : ℚ) : WeierstrassCurve ℚ :=
  { a₁ := 0
    a₂ := A
    a₃ := 0
    a₄ := B
    a₆ := 0 }
```

For this curve,

```text
Equation x y ↔ y^2 = x^3 + A*x^2 + B*x
negY x y = -y
(0,0) is nonsingular iff B ≠ 0
```

Useful local simp lemmas:

```lean
@[simp] theorem shortW_equation_iff {A B x y : ℚ} :
    (shortW A B).Equation x y ↔ y ^ 2 = x ^ 3 + A * x ^ 2 + B * x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [shortW]
  ring_nf

@[simp] theorem shortW_negY {A B x y : ℚ} :
    (shortW A B).negY x y = -y := by
  simp [shortW, WeierstrassCurve.Affine.negY]

@[simp] theorem shortW_nonsingular_zero_iff {A B : ℚ} :
    (shortW A B).Nonsingular 0 0 ↔ B ≠ 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_zero]
  simp [shortW]
```

If `ring_nf` struggles in `shortW_equation_iff`, use:

```lean
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [shortW]
  norm_num
  ring
```

## 2. The distinguished point `(0,0)`

Avoid `Point.mk` unless you have `[shortW A B).IsElliptic]`. You only need `B ≠ 0`, so construct the nonsingular point directly with `.some`.

```lean
noncomputable def shortW_zeroTwoPoint {A B : ℚ} (hB : B ≠ 0) :
    (shortW A B).Point :=
  WeierstrassCurve.Affine.Point.some 0 0
    ((shortW_nonsingular_zero_iff (A := A) (B := B)).mpr hB)

@[simp] theorem shortW_zeroTwoPoint_ne_zero {A B : ℚ} (hB : B ≠ 0) :
    shortW_zeroTwoPoint (A := A) (B := B) hB ≠ 0 := by
  exact WeierstrassCurve.Affine.Point.some_ne_zero _
```

If your local statement is written with `(shortW A B ⁄ ℚ).Point`, then either:

```lean
change ((shortW A B).Point) at *
```

when the base-change is defeq over `ℚ`, or define `shortWQ A B := shortW A B ⁄ ℚ` and repeat the same lemmas with `simp [shortWQ, shortW]`.

## 3. Extracting a nonzero 2-torsion point not equal to `(0,0)` from the injected `ZMod 2 × ZMod 2`

This part is small group theory and should compile. The point is: if `g(1,0)` is not `(0,0)`, use it; otherwise use `g(0,1)`, which cannot also be `(0,0)` by injectivity.

```lean
private theorem zmod2x2_pair_ne_10_00 :
    ((1, 0) : ZMod 2 × ZMod 2) ≠ 0 := by
  intro h
  have := congrArg Prod.fst h
  norm_num at this

private theorem zmod2x2_pair_ne_01_00 :
    ((0, 1) : ZMod 2 × ZMod 2) ≠ 0 := by
  intro h
  have := congrArg Prod.snd h
  norm_num at this

private theorem zmod2x2_pair_ne_10_01 :
    ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) := by
  intro h
  have := congrArg Prod.fst h
  norm_num at this

/-- A full `ZMod 2 × ZMod 2` injection gives a nonzero 2-torsion point not equal
`(0,0)`. This is the exact group-theoretic extraction needed for the algebra layer. -/
theorem exists_two_torsion_ne_zeroTwoPoint_of_fullTwo
    {A B : ℚ} (hB : B ≠ 0)
    (g : (ZMod 2 × ZMod 2) →+ (shortW A B).Point)
    (hg : Function.Injective g) :
    ∃ Q : (shortW A B).Point,
      Q ≠ 0 ∧ Q ≠ shortW_zeroTwoPoint (A := A) (B := B) hB ∧ 2 • Q = 0 := by
  let P0 := shortW_zeroTwoPoint (A := A) (B := B) hB
  by_cases h10 : g ((1, 0) : ZMod 2 × ZMod 2) = P0
  · refine ⟨g ((0, 1) : ZMod 2 × ZMod 2), ?_, ?_, ?_⟩
    · intro hz
      have : ((0, 1) : ZMod 2 × ZMod 2) = 0 := hg (by simpa using hz)
      exact zmod2x2_pair_ne_01_00 this
    · intro h01
      have hEq : g ((1, 0) : ZMod 2 × ZMod 2) = g ((0, 1) : ZMod 2 × ZMod 2) := by
        rw [h10, h01]
      exact zmod2x2_pair_ne_10_01 (hg hEq)
    · rw [← map_nsmul]
      norm_num
  · refine ⟨g ((1, 0) : ZMod 2 × ZMod 2), ?_, h10, ?_⟩
    · intro hz
      have : ((1, 0) : ZMod 2 × ZMod 2) = 0 := hg (by simpa using hz)
      exact zmod2x2_pair_ne_10_00 this
    · rw [← map_nsmul]
      norm_num
```

If `norm_num` does not prove `2 • ((1,0) : ZMod 2 × ZMod 2) = 0`, use:

```lean
      ext <;> norm_num
```

inside a `change g (2 • ((1,0) : ZMod 2 × ZMod 2)) = 0` step.

## 4. Point-level 2-torsion on the short curve gives `y=0`

This is the smallest Mathlib-affine API lemma. It uses `Point.add_self_of_Y_ne` by contradiction.

```lean
theorem shortW_y_eq_zero_of_two_nsmul_eq_zero
    {A B x y : ℚ} {h : (shortW A B).Nonsingular x y}
    (h2 : 2 • (WeierstrassCurve.Affine.Point.some x y h : (shortW A B).Point) = 0) :
    y = 0 := by
  rw [two_nsmul] at h2
  by_contra hy0
  have hy : y ≠ (shortW A B).negY x y := by
    simp [shortW_negY]
    linarith
  have hadd := WeierstrassCurve.Affine.Point.add_self_of_Y_ne (W := shortW A B) (h₁ := h) hy
  rw [hadd] at h2
  exact WeierstrassCurve.Affine.Point.some_ne_zero _ h2
```

The theorem uses only public names:

```lean
WeierstrassCurve.Affine.Point.add_self_of_Y_ne
WeierstrassCurve.Affine.Point.some_ne_zero
two_nsmul
```

## 5. A nonzero 2-torsion point not `(0,0)` gives a nonzero quadratic root

This is the main point-destructor lemma. It cases on `Q`; the zero case contradicts `Q≠0`; the affine case uses the previous lemma and the curve equation.

```lean
theorem exists_quadratic_root_of_two_torsion_ne_zeroTwoPoint
    {A B : ℚ} (hB : B ≠ 0)
    {Q : (shortW A B).Point}
    (hQ0 : Q ≠ 0)
    (hQP0 : Q ≠ shortW_zeroTwoPoint (A := A) (B := B) hB)
    (h2Q : 2 • Q = 0) :
    ∃ x : ℚ, x ≠ 0 ∧ x ^ 2 + A * x + B = 0 := by
  rcases Q with _ | ⟨x, y, hxy⟩
  · exact False.elim (hQ0 rfl)
  · have hy0 : y = 0 := shortW_y_eq_zero_of_two_nsmul_eq_zero (A := A) (B := B) (x := x) (y := y) h2Q
    have hx0 : x ≠ 0 := by
      intro hx
      apply hQP0
      subst x
      subst y
      -- both sides are `.some 0 0 _`; proof irrelevance closes the nonsingularity proof.
      rfl
    have heq : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x :=
      (shortW_equation_iff (A := A) (B := B) (x := x) (y := y)).mp hxy.1
    refine ⟨x, hx0, ?_⟩
    subst y
    have : x * (x ^ 2 + A * x + B) = 0 := by
      nlinarith [heq]
    exact (mul_eq_zero.mp this).resolve_left hx0
```

If the `rfl` in the `hQP0` proof does not close because of proof-irrelevance elaboration, use:

```lean
      apply Eq.ndrec
      rfl
```

or simply:

```lean
      simp [shortW_zeroTwoPoint]
```

## 6. Quadratic root gives discriminant square

This part is fully elementary and should be checked locally.

```lean
theorem exists_square_discriminant_of_quadratic_root
    {A B x : ℚ} (hx : x ^ 2 + A * x + B = 0) :
    ∃ s : ℚ, s ^ 2 = A ^ 2 - 4 * B := by
  refine ⟨2 * x + A, ?_⟩
  nlinarith
```

## 7. Final desired theorem, in the directly checkable shape

```lean
theorem square_discriminant_of_full_two_torsion_on_shortW
    {A B : ℚ} (hB : B ≠ 0)
    (g : (ZMod 2 × ZMod 2) →+ (shortW A B).Point)
    (hg : Function.Injective g) :
    ∃ s : ℚ, s ^ 2 = A ^ 2 - 4 * B := by
  rcases exists_two_torsion_ne_zeroTwoPoint_of_fullTwo hB g hg with ⟨Q, hQ0, hQP0, h2Q⟩
  rcases exists_quadratic_root_of_two_torsion_ne_zeroTwoPoint hB hQ0 hQP0 h2Q with ⟨x, hx0, hx⟩
  exact exists_square_discriminant_of_quadratic_root hx
```

For the exact target with `(shortW A B ⁄ ℚ).Point`, add a wrapper:

```lean
theorem square_discriminant_of_full_two_torsion_on_shortW_baseChange
    {A B : ℚ} (hB : B ≠ 0)
    (g : (ZMod 2 × ZMod 2) →+ ((shortW A B)⁄ℚ).Point)
    (hg : Function.Injective g) :
    ∃ s : ℚ, s ^ 2 = A ^ 2 - 4 * B := by
  -- In most local snapshots this is defeq; otherwise use `Point.map_id`/baseChange
  -- transport. Try this first:
  change ∃ s : ℚ, s ^ 2 = A ^ 2 - 4 * B
  exact square_discriminant_of_full_two_torsion_on_shortW (A := A) (B := B) hB g hg
```

If the type is not defeq, define `shortWQ A B := (shortW A B)⁄ℚ` and duplicate the `shortW_*` simp lemmas for `shortWQ`; all algebra is identical.

## 8. Why not use `twoTorsionPolynomial` directly?

`WeierstrassCurve.twoTorsionPolynomial` is available and for `shortW A B` simplifies to the cubic

```lean
4 * X^3 + 4*A*X^2 + 4*B*X
```

because

```text
b₂ = 4A, b₄ = 2B, b₆ = 0,
twoTorsionPolynomial = ⟨4, b₂, 2*b₄, b₆⟩.
```

But Mathlib currently appears to provide only the discriminant relation:

```lean
#check WeierstrassCurve.twoTorsionPolynomial_discr
#check WeierstrassCurve.twoTorsionPolynomial_discr_ne_zero_of_isElliptic
```

I did not find a public theorem of the form:

```lean
P ≠ 0 → 2 • P = 0 ↔
  ∃ x, W.twoTorsionPolynomial.toPoly.eval x = 0 ∧ P.xRep = ![x, 1]
```

So the smallest honest residual boundary, if the direct point proof above becomes too slow, is:

```lean
def ShortWFullTwoAlgebraResidual : Prop :=
  ∀ {A B : ℚ}, B ≠ 0 →
    (∃ g : (ZMod 2 × ZMod 2) →+ (shortW A B).Point, Function.Injective g) →
      ∃ x : ℚ, x ≠ 0 ∧ x ^ 2 + A * x + B = 0

theorem square_discriminant_of_shortW_residual
    (hres : ShortWFullTwoAlgebraResidual) {A B : ℚ} (hB : B ≠ 0)
    (g : (ZMod 2 × ZMod 2) →+ (shortW A B).Point)
    (hg : Function.Injective g) :
    ∃ s : ℚ, s ^ 2 = A ^ 2 - 4 * B := by
  rcases hres hB ⟨g, hg⟩ with ⟨x, hx0, hx⟩
  exact exists_square_discriminant_of_quadratic_root hx
```

This residual is much smaller and more honest than the original Kubert axiom: it is purely the affine group-law statement that full rational 2-torsion supplies a nonzero root of the quadratic factor.

## 9. Recommended next step

Try to compile the direct chain in this order:

1. `shortW_equation_iff`, `shortW_negY`, `shortW_nonsingular_zero_iff`.
2. `exists_two_torsion_ne_zeroTwoPoint_of_fullTwo`.
3. `shortW_y_eq_zero_of_two_nsmul_eq_zero`.
4. `exists_quadratic_root_of_two_torsion_ne_zeroTwoPoint`.
5. `square_discriminant_of_full_two_torsion_on_shortW`.

The likely friction points are only base-change defeq and proof-irrelevance around `.some 0 0 h`; both are local API issues, not mathematical gaps.
