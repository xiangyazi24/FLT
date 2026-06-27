# Q1232 (dm1): IVT-only proof sketch for the real locus and the `E(ℝ)[m]` combinatorial partition

## Bottom line

Yes, the **real-cubic branch classification** behind the statement “`E(ℝ)` has at most two real branches/components” can be formalized in Lean 4 with Mathlib using only generic IVT plus polynomial/root-count facts.

But no, the desired torsion bound

```lean
Nat.card {P : (E⁄ℝ).Point // (m : ℕ) • P = 0} ≤ 2 * m
```

cannot be proved from the x-interval partition alone. The partition gives at most two geometric regions. The estimate “each region contributes at most `m` torsion points” still needs the group/circle input: the relevant real component is a circle/torsor for a circle, and its `m`-torsion injects into `ZMod m` or has cardinal at most `m`. That is not a consequence of IVT alone.

So the right Lean plan is:

1. Use IVT/polynomial algebra to build a **branch index**
   ```lean
   branchIndex : (E⁄ℝ).Point → Fin 2
   ```
   from the x-coordinate and the roots of the cubic `Ψ₂Sq`.
2. Prove a generic finite-combinatorial lemma: if each branch fiber has cardinal `≤ m`, then the whole torsion set has cardinal `≤ 2 * m`.
3. Supply the fiber bound from a separate real-component/circle theorem. The IVT branch argument helps identify the two fibers but does not itself prove the fiber bound.

## Mathlib API check

Mathlib does **not** have a special theorem named `Polynomial.IVT`. It has generic IVT for continuous functions on intervals/connected sets, and polynomials are continuous.

Useful checks:

```lean
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Polynomial.Order

#check intermediate_value_Icc
#check IsPreconnected.intermediate_value
#check intermediate_value_univ
#check mem_range_of_exists_le_of_exists_ge

#check Polynomial.continuous
#check Polynomial.continuousOn

#check Polynomial.card_roots'
#check Polynomial.card_le_degree_of_subset_roots
#check Polynomial.finite_setOf_isRoot

#check Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
#check Polynomial.zero_le_eval_of_roots_le_of_leadingCoeff_nonneg
#check Polynomial.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
#check Polynomial.zero_le_negOnePow_mul_eval_of_le_roots_of_leadingCoeff_nonneg
```

The file `Mathlib.Analysis.Polynomial.Order` is especially relevant: it proves eventual/root-side sign lemmas for real polynomials. Those lemmas themselves use `intermediate_value_Icc`, so they are essentially packaged IVT plus polynomial algebra. If “ONLY IVT” means no real closed field machinery and no advanced curve topology, these are acceptable. If it means literally no imported lemma whose proof used anything besides IVT, then reprove the required sign lemmas locally from `intermediate_value_Icc` and `Polynomial.continuous`.

## Important coordinate correction

For a general Weierstrass equation in Mathlib, the curve is not literally stored as

```text
y^2 = f(x)
```

Instead, after completing the square, the relevant coordinate is

```text
u = 2*y + a₁*x + a₃
```

and the cubic is

```text
u^2 = Ψ₂Sq(x)
```

where

```lean
(E⁄ℝ).Ψ₂Sq = 4*X^3 + b₂*X^2 + 2*b₄*X + b₆
```

This is exactly the `Ψ₂Sq` polynomial from `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`.

So in Lean the branch classifier should be based on `Ψ₂Sq.eval x ≥ 0`, not on the original `y^2` unless the curve has already been put into short Weierstrass form.

A useful local lemma to prove is schematic like this:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Analysis.Polynomial.Order

noncomputable section

open Polynomial
open WeierstrassCurve
open scoped Polynomial.Bivariate

/-- Schematic: on a real point, the completed-square coordinate has square `Ψ₂Sq(x)`. -/
private lemma completed_square_eq_Ψ₂Sq
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {x y : ℝ} (hxy : (E⁄ℝ).Nonsingular x y) :
    ((E⁄ℝ).toAffine.polynomialY.evalEval x y) ^ 2 =
      ((E⁄ℝ).Ψ₂Sq).eval x := by
  -- Prove by evaluating the identity `ψ₂_sq` or `C_Ψ₂Sq` at `(x,y)`
  -- and using `hxy.left`, i.e. the Weierstrass equation at `(x,y)`.
  -- In the division-polynomial file the identity is:
  --   W.ψ₂ ^ 2 = C W.Ψ₂Sq + 4 * W.toAffine.polynomial
  -- Evaluating at a point on the curve kills the final polynomial term.
  -- The exact simp set will involve:
  --   WeierstrassCurve.ψ₂
  --   WeierstrassCurve.ψ₂_sq
  --   WeierstrassCurve.Affine.evalEval_polynomialY
  --   the equation part of `hxy`.
  -- Fill this as the first API lemma.
  omega -- placeholder in this sketch; do not use in final code
```

The last line is intentionally marked as a placeholder for the sketch; the actual implementation should replace it with evaluation/simp/ring reasoning, not `omega`.

## Cubic root and sign classification

The main algebraic classification lemma should be stated independently of elliptic curves.

For a squarefree cubic `f : ℝ[X]` with positive leading coefficient, the nonnegative locus is one of two shapes:

```text
one real root r:
  {x | 0 ≤ f(x)} = [r, ∞)

three real roots r₁ < r₂ < r₃:
  {x | 0 ≤ f(x)} = [r₁, r₂] ∪ [r₃, ∞)
```

The squarefree hypothesis is needed to rule out the double-root case. For elliptic curves it should follow from nonsingularity/discriminant nonzero, but prove that as a separate bridge lemma for `Ψ₂Sq`.

Suggested shape theorem:

```lean
import Mathlib.Analysis.Polynomial.Order

noncomputable section

open Polynomial Set

/-- The two possible nonnegative loci for a squarefree real cubic with positive leading coefficient.
This is the useful IVT/polynomial output for the elliptic-curve branch partition. -/
inductive CubicNonnegShape (f : ℝ[X]) : Type
  | oneRoot
      (r : ℝ)
      (hr : f.IsRoot r)
      (h_nonneg_iff : ∀ x : ℝ, 0 ≤ f.eval x ↔ r ≤ x)
  | threeRoots
      (r₁ r₂ r₃ : ℝ)
      (h₁₂ : r₁ < r₂)
      (h₂₃ : r₂ < r₃)
      (hr₁ : f.IsRoot r₁)
      (hr₂ : f.IsRoot r₂)
      (hr₃ : f.IsRoot r₃)
      (h_nonneg_iff : ∀ x : ℝ, 0 ≤ f.eval x ↔ x ∈ Icc r₁ r₂ ∨ r₃ ≤ x)

/-- Schematic theorem to prove. -/
private theorem cubic_nonneg_shape
    (f : ℝ[X])
    (hdeg : f.natDegree = 3)
    (hlc : 0 < f.leadingCoeff)
    (hsqfree : f.Squarefree) :
    CubicNonnegShape f := by
  -- Proof plan:
  -- 1. `f ≠ 0` follows from `hdeg`.
  -- 2. Existence of at least one real root follows from IVT:
  --    show `f.eval x < 0` for some very negative `x` and `0 < f.eval y`
  --    for some very positive `y`, then apply `intermediate_value_Icc`.
  -- 3. `Polynomial.card_roots'` or `Polynomial.card_le_degree_of_subset_roots`
  --    bounds the number of distinct roots by 3.
  -- 4. `hsqfree` rules out multiplicities, hence the number of distinct real roots is 1 or 3,
  --    not 2 with a double root.
  -- 5. In the one-root case use the packaged sign lemmas:
  --      * to the right of the unique root, all roots are `≤ x`, so `0 ≤ f.eval x`;
  --      * to the left, the odd-degree/positive-leading-coefficient sign lemma gives `f.eval x ≤ 0`.
  -- 6. In the three-root case, either factor using the three roots and compute signs of
  --    `(x-r₁)*(x-r₂)*(x-r₃)`, or use the sign lemmas interval-by-interval.
  -- This theorem is a real proof obligation; do not leave it as a declaration in final code.
  fail_if_success exact (by trivial : CubicNonnegShape f)
  -- End of sketch.
  exact by
    -- no actual proof supplied in this dispatch
    -- replace this entire block in implementation
    contradiction
```

The code above is a **shape of the desired theorem**, not final code. The key point is that this theorem is independent of elliptic curves and should be proved first.

### Root count snippet

This helper is close to final Lean and is often useful when avoiding root-multiset details at first:

```lean
import Mathlib.Algebra.Polynomial.Roots

open Polynomial

private lemma cubic_root_finset_card_le
    (f : ℝ[X]) (hdeg : f.natDegree = 3) (Z : Finset ℝ)
    (hZ : ∀ x ∈ Z, f.IsRoot x) :
    Z.card ≤ 3 := by
  classical
  have hf0 : f ≠ 0 := by
    intro hf
    simpa [hf] using hdeg
  have hsub : Z.val ⊆ f.roots := by
    intro x hx
    exact (Polynomial.mem_roots hf0).2 (hZ x hx)
  calc
    Z.card ≤ f.natDegree := Polynomial.card_le_degree_of_subset_roots hsub
    _ = 3 := hdeg
```

### IVT root-existence snippet

A generic IVT root-existence lemma can be organized like this:

```lean
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial

open Polynomial Set

private lemma exists_root_between_of_eval_neg_pos
    (f : ℝ[X]) {a b : ℝ} (hab : a ≤ b)
    (ha : f.eval a ≤ 0) (hb : 0 ≤ f.eval b) :
    ∃ x ∈ Icc a b, f.IsRoot x := by
  classical
  have h0 : 0 ∈ Icc (f.eval a) (f.eval b) := ⟨ha, hb⟩
  rcases intermediate_value_Icc hab f.continuous.continuousOn h0 with ⟨x, hx, hx0⟩
  exact ⟨x, hx, by simpa [Polynomial.IsRoot.def] using hx0.symm⟩
```

For a positive-leading cubic, produce `a` and `b` by proving the tail signs. You can do this manually from the explicit formula

```lean
C 4 * X^3 + C b₂ * X^2 + C (2*b₄) * X + C b₆
```

or use Mathlib’s polynomial asymptotic/sign facts. The manual route is longer but closer to “only IVT”.

## Branch index for real points

Once `cubic_nonneg_shape` is proved for `(E⁄ℝ).Ψ₂Sq`, define a branch index on real points.

In the one-root case, all affine real points and the point at infinity are assigned to the same branch.

In the three-root case, the compact oval is the interval `[r₁,r₂]`, and the unbounded branch is `[r₃,∞)` plus infinity. The condition `x ≤ r₂` distinguishes them because every real point has `Ψ₂Sq(x) ≥ 0`.

Schematic code:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Analysis.Polynomial.Order

noncomputable section

open Polynomial Set
open WeierstrassCurve

private def realBranchIndex
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℝ]
    (shape : CubicNonnegShape ((E⁄ℝ).Ψ₂Sq)) :
    (E⁄ℝ).Point → Fin 2 := by
  intro P
  cases shape with
  | oneRoot r hr h_nonneg_iff =>
      exact 0
  | threeRoots r₁ r₂ r₃ h₁₂ h₂₃ hr₁ hr₂ hr₃ h_nonneg_iff =>
      cases P with
      | zero =>
          -- Infinity belongs to the unbounded branch.
          exact 1
      | some x y hxy =>
          -- Since a real point satisfies `0 ≤ Ψ₂Sq(x)`, `h_nonneg_iff x` says
          -- `x ∈ [r₁,r₂] ∨ r₃ ≤ x`.
          -- Use `if x ≤ r₂ then 0 else 1` as the branch classifier.
          exact if x ≤ r₂ then 0 else 1
```

The proof that this classifier is mathematically correct is a lemma about real points:

```lean
private lemma realBranchIndex_eq_zero_iff_oval
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℝ]
    {r₁ r₂ r₃ : ℝ} (h₁₂ : r₁ < r₂) (h₂₃ : r₂ < r₃)
    (hshape : ∀ x : ℝ, 0 ≤ ((E⁄ℝ).Ψ₂Sq).eval x ↔ x ∈ Icc r₁ r₂ ∨ r₃ ≤ x)
    {x y : ℝ} (hxy : (E⁄ℝ).Nonsingular x y) :
    (if x ≤ r₂ then (0 : Fin 2) else 1) = 0 ↔ x ∈ Icc r₁ r₂ := by
  -- Direction `→`:
  --   if `x ≤ r₂`, then use real-point nonnegativity and `hshape x`.
  --   The alternative `r₃ ≤ x` contradicts `x ≤ r₂` and `r₂ < r₃`.
  -- Direction `←`:
  --   `x ∈ Icc r₁ r₂` gives `x ≤ r₂`, so simp on the if.
  -- Requires the completed-square lemma to get `0 ≤ Ψ₂Sq.eval x`.
  -- This is an ordinary order proof after the algebraic lemma.
  fail_if_success exact (by simp : (if x ≤ r₂ then (0 : Fin 2) else 1) = 0 ↔ x ∈ Icc r₁ r₂)
  exact by contradiction
```

Again: this is proof architecture, not final Lean.

## The purely finite combinatorial lemma

This is the part that really is combinatorial. It does not mention topology or elliptic curves.

If a finite type `T` has a branch map into `Fin 2`, and each fiber injects into `ZMod m`, then `T` injects into `Fin 2 × ZMod m`, hence `Nat.card T ≤ 2*m`.

Recommended statement:

```lean
import Mathlib.Data.ZMod.Basic

noncomputable section

open scoped Classical

/-- If every branch fiber embeds into `ZMod m`, then the whole finite type embeds into
`Fin 2 × ZMod m`. -/
private def embed_into_two_times_zmod
    {T : Type*} {m : ℕ} (branch : T → Fin 2)
    (fiberCode : ∀ i : Fin 2, {t : T // branch t = i} ↪ ZMod m) :
    T ↪ Fin 2 × ZMod m where
  toFun t := (branch t, fiberCode (branch t) ⟨t, rfl⟩)
  inj' := by
    intro a b h
    -- `congrArg Prod.fst h` gives `branch a = branch b`.
    -- Then transport the equality of second coordinates across that branch equality
    -- and use `(fiberCode i).injective`.
    -- This dependent cast is the only slightly annoying part.
    -- Alternative: use sigma codomain `Σ i : Fin 2, ZMod m`, where the cast is more explicit.
    -- Finish by subtype extensionality.
    cases hbranch : branch a
    all_goals
      -- local proof omitted in sketch
      admit

private theorem card_le_two_mul_of_fiber_embeddings
    {T : Type*} [Finite T] {m : ℕ} (hm : 0 < m)
    (branch : T → Fin 2)
    (fiberCode : ∀ i : Fin 2, {t : T // branch t = i} ↪ ZMod m) :
    Nat.card T ≤ 2 * m := by
  classical
  have h := Nat.card_le_card_of_injective
    (f := embed_into_two_times_zmod branch fiberCode)
    (embed_into_two_times_zmod branch fiberCode).injective
  -- Then simplify:
  --   Nat.card (Fin 2 × ZMod m) = Nat.card (Fin 2) * Nat.card (ZMod m) = 2 * m.
  -- Use local names for `ZMod` card: try `ZMod.card`, `Nat.card_zmod`, or simp.
  -- Final line is typically:
  --   simpa [Nat.card_prod, Nat.card_fin, ZMod.card] using h
  admit
```

Do not leave `admit` in final code. I include it only to show the proof structure. In practice, if dependent equality in `embed_into_two_times_zmod` is irritating, use a sigma codomain first:

```lean
T ↪ Σ _ : Fin 2, ZMod m
```

then compose with the standard equivalence

```lean
(Σ _ : Fin 2, ZMod m) ≃ Fin 2 × ZMod m
```

or compare cardinalities directly by a finite sum over `Fin 2`.

## Applying the combinatorial lemma to `E(ℝ)[m]`

Let

```lean
private abbrev RealMTorsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℝ] (m : ℕ) :=
  {P : (E⁄ℝ).Point // (m : ℕ) • P = 0}
```

The branch map is:

```lean
fun P : RealMTorsion E m => realBranchIndex E shape P.1
```

To finish the cardinal bound, it is enough to prove this missing theorem:

```lean
/-- Missing non-IVT input: each real branch contributes at most `m` many `m`-torsion points. -/
private theorem real_branch_torsion_fiber_embeds_zmod
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℝ]
    (m : ℕ) (hm : 0 < m)
    (shape : CubicNonnegShape ((E⁄ℝ).Ψ₂Sq))
    (i : Fin 2) :
    {P : RealMTorsion E m // realBranchIndex E shape P.1 = i} ↪ ZMod m := by
  -- This is where IVT is no longer enough.
  -- Needed input:
  --   * the branch is a connected component or a torsor for the identity component;
  --   * the identity component is additively equivalent/homeomorphic to `UnitAddCircle`;
  --   * `UnitAddCircle` `m`-torsion embeds into `ZMod m` or has card ≤ m.
  -- Use `Mathlib.Topology.Instances.AddCircle.Real`:
  --   #check UnitAddCircle
  --   #check ZMod.toAddCircle
  --   #check ZMod.toAddCircle_injective
  --   #check AddCircle.card_torsion_le_of_isSMulRegular
  -- Do not try to prove this from the x-interval partition alone.
  admit
```

Then the final theorem is straightforward:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Analysis.Polynomial.Order
import Mathlib.Topology.Instances.AddCircle.Real

noncomputable section

open scoped Classical
open Polynomial Set
open WeierstrassCurve

private abbrev RealMTorsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℝ] (m : ℕ) :=
  {P : (E⁄ℝ).Point // (m : ℕ) • P = 0}

/-- Final shape of the combinatorial proof. -/
theorem real_mTorsion_card_le_via_branch_index
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℝ]
    (m : ℕ) (hm : 0 < m) :
    Nat.card (RealMTorsion E m) ≤ 2 * m := by
  classical
  -- 1. Get cubic shape for `Ψ₂Sq`.
  --    Need bridge lemmas:
  --      * `((E⁄ℝ).Ψ₂Sq).natDegree = 3` and positive leading coefficient;
  --      * `((E⁄ℝ).Ψ₂Sq).Squarefree` from `E.IsElliptic`.
  let shape : CubicNonnegShape ((E⁄ℝ).Ψ₂Sq) := by
    -- exact cubic_nonneg_shape ((E⁄ℝ).Ψ₂Sq) hdeg hlc hsqfree
    admit

  -- 2. Branch map from torsion points to at most two branches.
  let branch : RealMTorsion E m → Fin 2 := fun P => realBranchIndex E shape P.1

  -- 3. Each branch fiber embeds into `ZMod m` by the non-IVT group/circle input.
  have fiberCode : ∀ i : Fin 2, {P : RealMTorsion E m // branch P = i} ↪ ZMod m := by
    intro i
    -- exact real_branch_torsion_fiber_embeds_zmod E m hm shape i
    admit

  -- 4. Pure finite combinatorics.
  exact card_le_two_mul_of_fiber_embeddings hm branch fiberCode
```

This is the clean “combinatorial” formulation: the only topological/group-theoretic input is pushed into `real_branch_torsion_fiber_embeds_zmod`.

## Why the x-interval partition alone cannot bound each fiber by `m`

The interval classification says where the x-coordinate of a real point can lie. It does not describe how the elliptic-curve group law moves points inside that interval, nor does it give a cyclic coordinate on a branch.

The bound “one component has at most `m` m-torsion points” is a theorem about compact connected abelian Lie groups/circles, or more concretely about an additive circle parameter. In Lean, use `UnitAddCircle`, `ZMod.toAddCircle`, or `AddCircle.card_torsion_le_of_isSMulRegular` for this part.

Thus, an IVT-only proof can establish:

```text
real points lie on at most two x-branches
```

but it cannot by itself establish:

```text
each branch contains at most m m-torsion points
```

The latter is the same circle-torsion input from the previous plan, just localized to each branch fiber.

## Recommended implementation order

1. Prove `completed_square_eq_Ψ₂Sq` for real affine points.
2. Prove or reuse `Ψ₂Sq` cubic facts:
   ```lean
   ((E⁄ℝ).Ψ₂Sq).natDegree = 3
   0 < ((E⁄ℝ).Ψ₂Sq).leadingCoeff
   ((E⁄ℝ).Ψ₂Sq).Squarefree
   ```
3. Prove `cubic_nonneg_shape` for squarefree positive-leading cubics.
4. Define `realBranchIndex` from `CubicNonnegShape`.
5. Prove the finite combinatorial lemma reducing `Nat.card T ≤ 2*m` to fiber embeddings into `ZMod m`.
6. Discharge the fiber embedding using the real component/circle theorem. Do not expect IVT alone to do this final step.
