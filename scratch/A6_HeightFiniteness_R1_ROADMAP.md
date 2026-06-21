
═══ BRIDGE  Q12 →dm4  SUBMITTED ═══
     "Q11 (dm4): Lean 4 / Mathlib. flt-ai. CONCRETE path: prove `Finite (Add…"
     ↳ debug: task c4e1eb9a

[ask-gpt Q12 dm4 tid=c4e1eb9a +0s] dispatched, waiting for answer
[ask-gpt Q12 dm4 tid=c4e1eb9a +90s] waiting (status=processing)
[ask-gpt Q12 dm4 tid=c4e1eb9a +180s] waiting (status=processing)
[ask-gpt Q12 dm4 tid=c4e1eb9a +270s] waiting (status=processing)
[ask-gpt Q12 dm4 tid=c4e1eb9a +360s] waiting (status=processing)
[ask-gpt Q12 dm4 tid=c4e1eb9a +450s] waiting (status=processing)
[ask-gpt Q12 dm4 tid=c4e1eb9a +540s] waiting (status=processing)
[ask-gpt Q12 dm4 tid=c4e1eb9a +630s] waiting (status=processing)
[ask-gpt Q12 dm4 tid=c4e1eb9a +720s] waiting (status=processing)
[ask-gpt Q12 dm4 tid=c4e1eb9a +810s] waiting (status=processing)
[ask-gpt Q12 dm4 tid=c4e1eb9a +859s] terminal: status=completed

═══ BRIDGE  Q12 →dm4  ✅ COMPLETE (14.7KB, 14m19s) ═══
     "Q11 (dm4): Lean 4 / Mathlib. flt-ai. CONCRETE path: prove `Finite (Add…"
     ↳ debug: task c4e1eb9a

## Current verdict

The height route is **much cheaper than full Mordell-Weil**, but it is **not currently a one-file discharge**. Current Mathlib does **not** have canonical/Néron-Tate height on elliptic curves, and it does **not** yet have a point-level naïve-height torsion bound. The right bounded project is:

```lean
xHeight_northcott
+
xHeight_two_nsmul_lower
+
pure abstract finite-torsion-from-height lemma
```

No weak Mordell-Weil, no Selmer groups, no canonical height are logically required.

---

## 1. What `Mathlib.NumberTheory.Height.EllipticCurve` actually exposes

Current `Mathlib.NumberTheory.Height.EllipticCurve` imports:

```lean
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
public import Mathlib.NumberTheory.Height.MvPolynomial
```

and its TODO list still includes:

```lean
* Define the naïve height
* Add the further ingredients needed for the approximate parallelogram law
* Add the statement and proof of the approximate parallelogram law
```

So despite the module docstring saying “naïve height,” the file does **not** currently define a point-height function, and it does **not** define the canonical/Néron-Tate height. fileciteturn17file0L12-L33

The one main exported theorem is the polynomial-map height estimate:

```lean
namespace WeierstrassCurve

open Height MvPolynomial

variable {K : Type*} [Field K] [AdmissibleAbsValues K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

theorem abs_logHeight_addSubMap_sub_two_mul_logHeight_le :
    ∃ C, ∀ x : Fin 3 → K,
      |logHeight (fun i ↦ (addSubMap W i).eval x) - 2 * logHeight x| ≤ C := by
  ...
```

This is a height estimate for the homogeneous polynomial map `addSubMap W`, not yet a theorem about points `P Q : W.Point`. fileciteturn17file0L42-L56

The underlying `AddSubMap` file defines the polynomial map:

```lean
@[expose] noncomputable def WeierstrassCurve.addSubMap :
    Fin 3 → MvPolynomial (Fin 3) R :=
  ![s ^ 2 - C W.b₄ * s * u - C W.b₆ * t * u - C W.b₈ * u ^ 2,
    C 2 * t * s + C W.b₂ * s * u + C W.b₄ * t * u + C W.b₆ * u ^ 2,
    t ^ 2 - C 4 * s * u]
```

but the file’s TODO explicitly says:

```lean
TODO: Show that the map really does what it is claimed to do.
```

So the missing bridge is exactly the point-level compatibility needed for elliptic-curve heights. fileciteturn20file0L17-L31 fileciteturn20file0L48-L58

What Mathlib **does** have in the general height stack:

```lean
Height.AdmissibleAbsValues
Height.mulHeight₁
Height.logHeight₁
Height.mulHeight
Height.logHeight
Finsupp.mulHeight
Finsupp.logHeight
Height.logHeight₁_eq_logHeight
Height.logHeight₁_div_eq_logHeight
Height.logHeight_pow
Height.logHeight₁_pow
Height.logHeight₁_zpow
```

The docs describe `Height.mulHeight₁`/`Height.logHeight₁` for field elements, and `Height.mulHeight`/`Height.logHeight` for finite tuples representing projective points. citeturn449909view0

For elliptic points, Mathlib already has the projective x-coordinate representative:

```lean
noncomputable def WeierstrassCurve.Affine.Point.xRep :
    W'.Point → Fin 2 → R
```

with:

```lean
@[simp] theorem WeierstrassCurve.Affine.Point.xRep_zero :
    xRep 0 = ![1, 0]

@[simp] theorem WeierstrassCurve.Affine.Point.xRep_some
    (h : W'.Nonsingular x y) :
    (some x y h).xRep = ![x, 1]
```

and the crucial finite-fiber lemma:

```lean
theorem WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff :
    P.xRep = Q.xRep ↔ P = Q ∨ P = -Q
```

This is exactly what we need for a point-height Northcott argument: the x-map is two-to-one away from the usual sign ambiguity. citeturn932529view0

---

## 2. The Northcott route: exact Lean chain

Define the point x-height using `Point.xRep`:

```lean
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.NumberTheory.Height.Northcott
import Mathlib.GroupTheory.OrderOfElement

open Height
open WeierstrassCurve
open WeierstrassCurve.Affine

noncomputable def WeierstrassCurve.xHeight
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (E⁄ℚ).Point → ℝ :=
  fun P => Height.logHeight P.xRep
```

This is a naïve logarithmic height of the x-coordinate, with `0` represented by `![1, 0]` and affine `P = (x,y)` represented by `![x,1]`.

The abstract Northcott class is:

```lean
class Northcott (h : α → β) [LE β] : Prop where
  finite_le : ∀ b, {a : α | h a ≤ b}.Finite
```

so once we have `Northcott (E.xHeight)`, bounded height immediately gives finite sublevel sets. citeturn306446view3

The desired proof chain is:

```lean
-- 1. Point-height Northcott.
theorem xHeight_northcott
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Northcott (E.xHeight) := by
  -- reduce to rational x-coordinate Northcott and finite fibers of `Point.xRep`
  sorry

-- 2. Naïve height doubling lower bound.
theorem xHeight_two_nsmul_lower
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : ℝ, ∀ P : (E⁄ℚ).Point,
      4 * E.xHeight P - C ≤ E.xHeight (2 • P) := by
  -- main missing elliptic-height theorem
  sorry

-- 3. Pure abstract argument: torsion + doubling lower bound ⇒ bounded height.
theorem finite_torsion_of_northcott_double_lower
    {G : Type*} [AddCommGroup G]
    (h : G → ℝ) [Northcott h]
    (hdouble : ∃ C : ℝ, ∀ P : G, 4 * h P - C ≤ h (2 • P)) :
    {P : G | IsOfFinAddOrder P}.Finite := by
  classical
  rcases hdouble with ⟨C, hC⟩
  refine (Northcott.finite_le (h := h) (C / 3)).subset ?_
  intro P hP
  -- finite doubling orbit: `{2^n • P | n : ℕ}` is finite because `P` has finite additive order.
  -- choose `R` in the doubling orbit where `h` is maximal.
  -- Then `2 • R` is also in the orbit, so `h (2 • R) ≤ h R`.
  -- But `hC R` gives `4 * h R - C ≤ h (2 • R)`.
  -- Therefore `h R ≤ C / 3`.
  -- Since `P` belongs to the same orbit, `h P ≤ h R ≤ C / 3`.
  sorry
```

Then the elliptic theorem is shallow:

```lean
theorem rational_torsion_set_finite_of_xHeight
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    {P : (E⁄ℚ).Point | IsOfFinAddOrder P}.Finite := by
  exact finite_torsion_of_northcott_double_lower
    (h := E.xHeight)
    (xHeight_two_nsmul_lower E)
```

And the subtype version is:

```lean
theorem rational_torsion_subtype_finite_of_xHeight
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Finite {P : (E⁄ℚ).Point // IsOfFinAddOrder P} := by
  exact Set.Finite.finite_subtype
    (rational_torsion_set_finite_of_xHeight E)
```

If your local API has:

```lean
AddCommGroup.torsion (E⁄ℚ).Point
```

as a subtype/subgroup of elements satisfying `IsOfFinAddOrder`, the final conversion is just via the coercion:

```lean
theorem rational_torsion_finite_of_xHeight
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Finite (AddCommGroup.torsion (E⁄ℚ).Point) := by
  -- if `AddCommGroup.torsion` is definitionally the subtype:
  infer_instance
  -- otherwise:
  -- exact Finite.of_injective
  --   (fun P : AddCommGroup.torsion (E⁄ℚ).Point => (P : (E⁄ℚ).Point))
  --   Subtype.val_injective
```

Current Mathlib’s standard predicate for “finite additive order” is:

```lean
IsOfFinAddOrder P
```

with API:

```lean
isOfFinAddOrder_iff_nsmul_eq_zero
IsOfFinAddOrder.exists_nsmul_eq_zero
addOrderOf
addOrderOf_nsmul_eq_zero
addOrderOf_pos_iff
mod_addOrderOf_nsmul
IsOfFinAddOrder.add
```

These are in `Mathlib.GroupTheory.OrderOfElement`; the docs list `IsOfFinAddOrder`, `addOrderOf`, `isOfFinAddOrder_iff_nsmul_eq_zero`, and related additive-order lemmas. citeturn561210view0

---

## 3. What is missing in Mathlib for this chain?

There are three missing or not-yet-packaged pieces.

### Missing piece A: Northcott for rational x-height on points

This should be very manageable.

Mathlib has rational height formulas:

```lean
theorem Rat.mulHeight₁_eq_max (q : ℚ) :
    Height.mulHeight₁ q = ↑(max q.num.natAbs q.den)

theorem Rat.logHeight₁_eq_log_max (q : ℚ) :
    Height.logHeight₁ q = Real.log ↑(max q.num.natAbs q.den)
```

These are exactly the formulas needed to prove that `{q : ℚ | Height.logHeight₁ q ≤ B}` is finite. citeturn306446view0

Then point-level Northcott follows from:

```lean
P.xRep = ![1,0]       -- point at infinity
P.xRep = ![x,1]       -- affine point with x-coordinate x
P.xRep = Q.xRep ↔ P = Q ∨ P = -Q
```

So the x-coordinate fibers are finite. The exact target is:

```lean
theorem xHeight_finite_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (B : ℝ) :
    {P : (E⁄ℚ).Point | E.xHeight P ≤ B}.Finite := by
  -- reduce to finite set of rational x with `Height.logHeight₁ x ≤ B`
  -- use `Point.xRep_eq_xRep_iff` for finite fibers
  sorry

instance xHeight_northcott
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Northcott (E.xHeight) where
  finite_le := xHeight_finite_le E
```

One caveat: Mathlib’s `Height.Northcott` file currently gives only:

```lean
instance [AdmissibleAbsValues K] [Northcott (mulHeight₁ (K := K))] :
    Northcott (logHeight₁ (K := K))
```

and explicitly still has TODOs for projectivization heights. citeturn306446view2

But for `ℚ`, we can avoid projectivization by using the normalized representatives `![1,0]` and `![x,1]`, plus `Rat.logHeight₁_eq_log_max`.

### Missing piece B: torsion has bounded naïve x-height

This is the central missing theorem:

```lean
theorem xHeight_two_nsmul_lower
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : ℝ, ∀ P : (E⁄ℚ).Point,
      4 * E.xHeight P - C ≤ E.xHeight (2 • P) := by
  sorry
```

This is much weaker than full canonical height theory. It is the duplication-map height lower bound:

\[
h_x(2P) \ge 4 h_x(P) - C_E.
\]

From this alone, torsion is bounded: if `P` is torsion, its doubling orbit is finite; take a point `R` of maximal height in that orbit. Then `2R` is still in the orbit, so

```text
E.xHeight (2 • R) ≤ E.xHeight R
```

but the duplication lower bound gives

```text
4 * E.xHeight R - C ≤ E.xHeight (2 • R)
```

hence

```text
E.xHeight R ≤ C / 3
```

and therefore

```text
E.xHeight P ≤ C / 3.
```

No canonical height needed.

### Missing piece C: point-level compatibility of `addSubMap` / duplication

The file `Height.EllipticCurve` already proves a polynomial height estimate for `addSubMap`, but to get `xHeight_two_nsmul_lower`, one still needs a theorem connecting those polynomial formulas to the group law on points. The `AddSubMap` file explicitly says this compatibility is still TODO. fileciteturn20file0L17-L31

A useful intermediate target is:

```lean
theorem xRep_two_nsmul_height_formula
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : ℝ, ∀ P : (E⁄ℚ).Point,
      |E.xHeight (2 • P) - 4 * E.xHeight P| ≤ C := by
  -- via duplication formula / division polynomials / addSubMap compatibility
  sorry
```

Then:

```lean
theorem xHeight_two_nsmul_lower
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : ℝ, ∀ P : (E⁄ℚ).Point,
      4 * E.xHeight P - C ≤ E.xHeight (2 • P) := by
  rcases xRep_two_nsmul_height_formula E with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro P
  have h := hC P
  -- from `|a - b| ≤ C`, get `b - C ≤ a`
  linarith [abs_le.mp h |>.1]
```

---

## 4. Can we avoid canonical height?

Yes.

The canonical-height route would require defining:

```lean
canonicalHeight E P = lim n, 4^(-n) * xHeight E ((2^n) • P)
```

then proving:

```lean
canonicalHeight_two_nsmul :
    canonicalHeight E (2 • P) = 4 * canonicalHeight E P

canonicalHeight_eq_zero_iff_isOfFinAddOrder :
    canonicalHeight E P = 0 ↔ IsOfFinAddOrder P

abs_xHeight_sub_canonicalHeight_le :
    ∃ C, ∀ P, |E.xHeight P - canonicalHeight E P| ≤ C
```

None of this appears to be present in current `Height.EllipticCurve`.

But for torsion finiteness, canonical height is overkill. The finite-orbit argument only needs the naïve duplication lower bound:

```lean
∃ C, ∀ P, 4 * xHeight P - C ≤ xHeight (2 • P)
```

This theorem is essentially one of the inputs used to construct canonical height, but it is significantly weaker than constructing canonical height and proving all of its properties.

So the answer to Q3 is:

```lean
-- canonical height unavailable:
canonicalHeight : not in current Mathlib

-- enough replacement:
xHeight_two_nsmul_lower :
  ∃ C, ∀ P, 4 * xHeight P - C ≤ xHeight (2 • P)
```

This should be provable from the existing height stack plus the duplication/addSubMap compatibility theorem, but that compatibility theorem is still missing.

---

## 5. Buildability verdict

Height-based rational torsion finiteness is a **real but bounded project** on current Mathlib. It is not a one-evening seam, but it is far more feasible than full Mordell-Weil.

The project splits cleanly:

```lean
-- Pure group/height lemma: small.
finite_torsion_of_northcott_double_lower

-- Rational/point Northcott: small-to-medium.
xHeight_northcott

-- Elliptic height duplication lower bound: main missing theorem.
xHeight_two_nsmul_lower
```

The first concrete lemma I would dispatch is the pure one:

```lean
theorem finite_torsion_of_northcott_double_lower
    {G : Type*} [AddCommGroup G]
    (h : G → ℝ) [Northcott h]
    (hdouble : ∃ C : ℝ, ∀ P : G, 4 * h P - C ≤ h (2 • P)) :
    {P : G | IsOfFinAddOrder P}.Finite := by
  classical
  rcases hdouble with ⟨C, hC⟩
  refine (Northcott.finite_le (h := h) (C / 3)).subset ?_
  intro P hP
  -- Dispatch by finite maximum on the doubling orbit.
  --
  -- Let `S = {n • P | n < addOrderOf P}`.
  -- Since `P` has finite additive order, `0 < addOrderOf P`.
  -- The doubling orbit is contained in `S`, using `mod_addOrderOf_nsmul`.
  -- Pick `R ∈ S` with maximal `h R`.
  -- Then `2 • R ∈ S`, so `h (2 • R) ≤ h R`.
  -- From `hC R`, `4 * h R - C ≤ h (2 • R)`.
  -- Hence `h R ≤ C / 3`.
  -- Since `P ∈ S`, `h P ≤ h R`.
  -- Therefore `h P ≤ C / 3`.
  sorry
```

Then add:

```lean
noncomputable def WeierstrassCurve.xHeight
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (E⁄ℚ).Point → ℝ :=
  fun P => Height.logHeight P.xRep

theorem xHeight_northcott
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Northcott (E.xHeight) := by
  -- finite rational x-values using `Rat.logHeight₁_eq_log_max`
  -- finite fibers using `Point.xRep_eq_xRep_iff`
  sorry

theorem rational_torsion_finite_of_xHeight_two_nsmul_lower
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hdouble :
      ∃ C : ℝ, ∀ P : (E⁄ℚ).Point,
        4 * E.xHeight P - C ≤ E.xHeight (2 • P)) :
    {P : (E⁄ℚ).Point | IsOfFinAddOrder P}.Finite := by
  haveI : Northcott (E.xHeight) := xHeight_northcott E
  exact finite_torsion_of_northcott_double_lower
    (h := E.xHeight) hdouble
```

And the final target becomes:

```lean
theorem rational_torsion_finite
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Finite {P : (E⁄ℚ).Point // IsOfFinAddOrder P} := by
  exact Set.Finite.finite_subtype
    (rational_torsion_finite_of_xHeight_two_nsmul_lower E
      (xHeight_two_nsmul_lower E))
```

The smallest missing elliptic piece is therefore:

```lean
theorem xHeight_two_nsmul_lower
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : ℝ, ∀ P : (E⁄ℚ).Point,
      4 * E.xHeight P - C ≤ E.xHeight (2 • P)
```

This is the right seam to name if you want to remove `mordell_weil_fg` from the torsion-finiteness dependency without taking on full Mordell-Weil.
