# Q2863 (dm-codex1): performance-aware `shortW` full-two algebra layer

Target local file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`  
Namespace: `MazurProof.RationalPointsN12`

The main performance fix is: **do not prove the full-two source extraction directly over EC points**. Prove one tiny generic finite-source lemma over an arbitrary additive commutative monoid, then instantiate it with `((shortW A B)⁄ℚ).Point`. This avoids repeatedly elaborating affine point/group-law instances while doing `ZMod 2 × ZMod 2` casework.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open scoped WeierstrassCurve

namespace MazurProof.RationalPointsN12

noncomputable def shortW (A B : ℚ) : WeierstrassCurve ℚ :=
  { a₁ := 0
    a₂ := A
    a₃ := 0
    a₄ := B
    a₆ := 0 }

/-- Use this abbreviation to prevent Lean from repeatedly unfolding the base-change target. -/
abbrev shortWQ (A B : ℚ) : WeierstrassCurve ℚ := (shortW A B)⁄ℚ

/-! ## Fast source-side group extraction -/

private abbrev V4 : Type := ZMod 2 × ZMod 2

private abbrev e10 : V4 := ((1, 0) : ZMod 2 × ZMod 2)
private abbrev e01 : V4 := ((0, 1) : ZMod 2 × ZMod 2)

private theorem e10_ne_zero : e10 ≠ 0 := by
  native_decide

private theorem e01_ne_zero : e01 ≠ 0 := by
  native_decide

private theorem e10_ne_e01 : e10 ≠ e01 := by
  native_decide

private theorem two_nsmul_e10 : 2 • e10 = 0 := by
  ext <;> norm_num [e10]

private theorem two_nsmul_e01 : 2 • e01 = 0 := by
  ext <;> norm_num [e01]

/-- Exact replacement for the slow `rw [← map_nsmul]` branches.
This uses only `congrArg g hsrc`; `simp` rewrites both sides by `map_nsmul`/`map_zero`. -/
private theorem map_two_nsmul_eq_zero
    {G : Type*} [AddCommMonoid G]
    (g : V4 →+ G) {x : V4} (hsrc : 2 • x = 0) :
    2 • g x = 0 := by
  have h := congrArg g hsrc
  simpa using h

/-- Fast generic V4 extraction.  No elliptic-curve point constructors appear here. -/
private theorem exists_v4_image_ne_zero_ne
    {G : Type*} [AddCommMonoid G]
    (g : V4 →+ G) (hg : Function.Injective g)
    {P0 : G} (hP0 : P0 ≠ 0) :
    ∃ Q : G, Q ≠ 0 ∧ Q ≠ P0 ∧ 2 • Q = 0 := by
  by_cases h10 : g e10 = P0
  · refine ⟨g e01, ?_, ?_, ?_⟩
    · intro hz
      have hEq : g e01 = g 0 := by simpa using hz
      exact e01_ne_zero (hg hEq)
    · intro h01
      have hEq : g e10 = g e01 := h10.trans h01.symm
      exact e10_ne_e01 (hg hEq)
    · exact map_two_nsmul_eq_zero g two_nsmul_e01
  · refine ⟨g e10, ?_, h10, ?_⟩
    · intro hz
      have hEq : g e10 = g 0 := by simpa using hz
      exact e10_ne_zero (hg hEq)
    · exact map_two_nsmul_eq_zero g two_nsmul_e10

/-! ## Fast coordinate lemmas for `shortWQ` -/

@[simp] theorem shortWQ_equation_iff {A B x y : ℚ} :
    (shortWQ A B).Equation x y ↔ y ^ 2 = x ^ 3 + A * x ^ 2 + B * x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [shortWQ, shortW]

@[simp] theorem shortWQ_negY {A B x y : ℚ} :
    (shortWQ A B).negY x y = -y := by
  simp [shortWQ, shortW, WeierstrassCurve.Affine.negY]

@[simp] theorem shortWQ_nonsingular_zero_iff {A B : ℚ} :
    (shortWQ A B).Nonsingular 0 0 ↔ B ≠ 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_zero]
  simp [shortWQ, shortW]

noncomputable def shortWQ_zeroTwoPoint {A B : ℚ} (hB : B ≠ 0) :
    (shortWQ A B).Point :=
  WeierstrassCurve.Affine.Point.some 0 0
    ((shortWQ_nonsingular_zero_iff (A := A) (B := B)).mpr hB)

@[simp] theorem shortWQ_zeroTwoPoint_ne_zero {A B : ℚ} (hB : B ≠ 0) :
    shortWQ_zeroTwoPoint (A := A) (B := B) hB ≠ 0 := by
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- Exact `y = 0` lemma with the real `negY` shape.  The key is the `intro hneg;
simp [shortWQ, shortW, WeierstrassCurve.Affine.negY] at hneg; linarith` block. -/
theorem shortWQ_y_eq_zero_of_two_nsmul_eq_zero
    {A B x y : ℚ} {h : (shortWQ A B).Nonsingular x y}
    (h2 : 2 • (WeierstrassCurve.Affine.Point.some x y h : (shortWQ A B).Point) = 0) :
    y = 0 := by
  rw [two_nsmul] at h2
  by_contra hy0
  have hy : y ≠ (shortWQ A B).negY x y := by
    intro hneg
    simp [shortWQ, shortW, WeierstrassCurve.Affine.negY] at hneg
    linarith
  have hadd :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne
      (W := shortWQ A B) (h₁ := h) hy
  rw [hadd] at h2
  exact WeierstrassCurve.Affine.Point.some_ne_zero _ h2

/-- Point-coordinate step.  If this is the only remaining slow theorem, use the
residual boundary below. -/
theorem exists_quadratic_root_of_two_torsion_ne_zeroTwoPoint
    {A B : ℚ} (hB : B ≠ 0)
    {Q : (shortWQ A B).Point}
    (hQ0 : Q ≠ 0)
    (hQP0 : Q ≠ shortWQ_zeroTwoPoint (A := A) (B := B) hB)
    (h2Q : 2 • Q = 0) :
    ∃ x : ℚ, x ≠ 0 ∧ x ^ 2 + A * x + B = 0 := by
  rcases Q with _ | ⟨x, y, hxy⟩
  · exact False.elim (hQ0 rfl)
  · have hy0 : y = 0 :=
      shortWQ_y_eq_zero_of_two_nsmul_eq_zero
        (A := A) (B := B) (x := x) (y := y) h2Q
    have hx0 : x ≠ 0 := by
      intro hx
      apply hQP0
      subst x
      subst y
      simp [shortWQ_zeroTwoPoint]
    have heq : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x :=
      (shortWQ_equation_iff (A := A) (B := B) (x := x) (y := y)).mp hxy.1
    refine ⟨x, hx0, ?_⟩
    subst y
    have hprod : x * (x ^ 2 + A * x + B) = 0 := by
      calc
        x * (x ^ 2 + A * x + B) = x ^ 3 + A * x ^ 2 + B * x := by ring
        _ = 0 := by nlinarith
    exact (mul_eq_zero.mp hprod).resolve_left hx0

/-- Fast polynomial endgame. -/
theorem exists_square_discriminant_of_quadratic_root
    {A B x : ℚ} (hx : x ^ 2 + A * x + B = 0) :
    ∃ s : ℚ, s ^ 2 = A ^ 2 - 4 * B := by
  refine ⟨2 * x + A, ?_⟩
  nlinarith

/-- Desired theorem.  The only EC-point group extraction is the single fast generic
`exists_v4_image_ne_zero_ne` instantiation. -/
theorem square_discriminant_of_full_two_torsion_on_shortW
    {A B : ℚ} (hB : B ≠ 0)
    (g : (ZMod 2 × ZMod 2) →+ (shortWQ A B).Point)
    (hg : Function.Injective g) :
    ∃ s : ℚ, s ^ 2 = A ^ 2 - 4 * B := by
  rcases exists_v4_image_ne_zero_ne
      (g := g) (hg := hg)
      (P0 := shortWQ_zeroTwoPoint (A := A) (B := B) hB)
      (shortWQ_zeroTwoPoint_ne_zero (A := A) (B := B) hB) with
    ⟨Q, hQ0, hQP0, h2Q⟩
  rcases exists_quadratic_root_of_two_torsion_ne_zeroTwoPoint
      (A := A) (B := B) hB hQ0 hQP0 h2Q with
    ⟨x, hx0, hx⟩
  exact exists_square_discriminant_of_quadratic_root hx

end MazurProof.RationalPointsN12
```

## Exact replacement for the two source 2-torsion branches

Use this instead of `rw [← map_nsmul]; ext` in EC-point goals:

```lean
have hsrc : 2 • ((0, 1) : ZMod 2 × ZMod 2) = 0 := by
  ext <;> norm_num
have h := congrArg g hsrc
simpa using h
```

and similarly:

```lean
have hsrc : 2 • ((1, 0) : ZMod 2 × ZMod 2) = 0 := by
  ext <;> norm_num
have h := congrArg g hsrc
simpa using h
```

The helper `map_two_nsmul_eq_zero` packages exactly this pattern.

## If the EC coordinate theorem is still too slow

Do **not** reintroduce the original Kubert axiom. Use this much smaller residual boundary:

```lean
def ShortWFullTwoPointResidual : Prop :=
  ∀ {A B : ℚ} (hB : B ≠ 0)
    {Q : (shortWQ A B).Point},
      Q ≠ 0 →
      Q ≠ shortWQ_zeroTwoPoint (A := A) (B := B) hB →
      2 • Q = 0 →
        ∃ x : ℚ, x ≠ 0 ∧ x ^ 2 + A * x + B = 0

theorem square_discriminant_of_full_two_torsion_on_shortW_of_pointResidual
    (hres : ShortWFullTwoPointResidual)
    {A B : ℚ} (hB : B ≠ 0)
    (g : (ZMod 2 × ZMod 2) →+ (shortWQ A B).Point)
    (hg : Function.Injective g) :
    ∃ s : ℚ, s ^ 2 = A ^ 2 - 4 * B := by
  rcases exists_v4_image_ne_zero_ne
      (g := g) (hg := hg)
      (P0 := shortWQ_zeroTwoPoint (A := A) (B := B) hB)
      (shortWQ_zeroTwoPoint_ne_zero (A := A) (B := B) hB) with
    ⟨Q, hQ0, hQP0, h2Q⟩
  rcases hres hB hQ0 hQP0 h2Q with ⟨x, hx0, hx⟩
  exact exists_square_discriminant_of_quadratic_root hx
```

This residual is the smallest honest boundary: it contains only the affine group-law fact “a nonzero 2-torsion point not `(0,0)` has nonzero `x` satisfying `x² + A*x + B = 0`.” The remaining source extraction and polynomial discriminant endgame are fast and local.

## Known/proposed status

* Known from your local report: `shortWQ_equation_iff` closes after `rw [equation_iff]; simp [shortWQ, shortW]`; no `ring_nf` needed.
* Known source-branch replacement: the `hsrc; congrArg g hsrc; simpa` pattern avoids `ext` on EC points.
* Known y-shape fix: the `hy` proof must use `simp [shortWQ, shortW, WeierstrassCurve.Affine.negY] at hneg; linarith`.
* Proposed but should be small: `exists_quadratic_root_of_two_torsion_ne_zeroTwoPoint`; if this is slow, use `ShortWFullTwoPointResidual` above.
