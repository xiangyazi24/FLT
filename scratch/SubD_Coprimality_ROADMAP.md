[ask-gpt dm2 tid=a0515e2e +0s] dispatched, waiting for answer
[ask-gpt dm2 tid=a0515e2e +90s] waiting (status=processing)
[ask-gpt dm2 tid=a0515e2e +180s] waiting (status=processing)
[ask-gpt dm2 tid=a0515e2e +270s] waiting (status=processing)
[ask-gpt dm2 tid=a0515e2e +360s] waiting (status=processing)
[ask-gpt dm2 tid=a0515e2e +387s] terminal: status=completed
The shortest robust route is **the direct point argument**, not resultants. Mathlib has `Ψ₂Sq`, `preΨ'`, and documents that `ΨSq n = preΨ n² * Ψ₂Sq` in the even case and `ΨSq n = preΨ n²` in the odd case, but there is no existing closed-form resultant for `resultant (preΨ' n) Ψ₂Sq` that would make the resultant route short. citeturn288366view0

Once you have the two point-level seams:

```lean
preΨ'_eval_eq_zero_iff_exists_non_two_torsion
two_nsmul_eq_zero_iff_Ψ₂Sq_eval_eq_zero
```

the residual is a contradiction in two lines.

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

noncomputable section

open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine
open Polynomial

namespace WeierstrassCurve

universe u

variable {k : Type u} [Field k] [IsSepClosed k] [DecidableEq k]
variable (E : WeierstrassCurve k) [E.IsElliptic]

/-
Expected SEAM2 shape.

Rename this to your actual theorem name if already present.  This is the
forward direction of the root-realization theorem: a root of `preΨ' n` is
realized by a non-2-torsion affine point killed by `n`.
-/
variable
  (preΨ'_root_realizes_non_two_torsion :
    ∀ {n : ℕ} {x : k}, (n : k) ≠ 0 →
      (E.preΨ' n).eval x = 0 →
        ∃ y (hxy : (E⁄k).Nonsingular x y),
          (2 : ℕ) • Affine.Point.some x y hxy ≠ 0 ∧
          n • Affine.Point.some x y hxy = 0)

/-
Expected two-torsion seam.

Rename this to your actual theorem name if already present.
-/
variable
  (two_nsmul_eq_zero_iff_Ψ₂Sq_eval_eq_zero :
    ∀ {x y : k} (hxy : (E⁄k).Nonsingular x y),
      (2 : ℕ) • Affine.Point.some x y hxy = 0 ↔
        (E.Ψ₂Sq).eval x = 0)

/--
The sub-D residual: a root of `preΨ'_n` is not a root of the two-torsion cubic.

This is the preferred proof: use the root-realization seam to get a
non-2-torsion point `P` over `x`; if `Ψ₂Sq(x)=0`, the two-torsion seam says
`2 • P = 0`, contradiction.
-/
theorem preΨ'_root_not_Ψ₂Sq_root
    {n : ℕ} {x : k}
    (hn : (n : k) ≠ 0)
    (hpre : (E.preΨ' n).eval x = 0) :
    (E.Ψ₂Sq).eval x ≠ 0 := by
  intro htwo
  obtain ⟨y, hxy, h2_ne, _hnP⟩ :=
    preΨ'_root_realizes_non_two_torsion (E := E) hn hpre
  exact h2_ne ((two_nsmul_eq_zero_iff_Ψ₂Sq_eval_eq_zero (E := E) hxy).mpr htwo)

end WeierstrassCurve
```

If your SEAM2 theorem is already an iff, use this version instead:

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

noncomputable section

open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine
open Polynomial

namespace WeierstrassCurve

universe u

variable {k : Type u} [Field k] [IsSepClosed k] [DecidableEq k]
variable (E : WeierstrassCurve k) [E.IsElliptic]

variable
  (preΨ'_eval_eq_zero_iff_exists_non_two_torsion :
    ∀ {n : ℕ} {x : k}, (n : k) ≠ 0 →
      ((E.preΨ' n).eval x = 0 ↔
        ∃ y (hxy : (E⁄k).Nonsingular x y),
          (2 : ℕ) • Affine.Point.some x y hxy ≠ 0 ∧
          n • Affine.Point.some x y hxy = 0))

variable
  (two_nsmul_eq_zero_iff_Ψ₂Sq_eval_eq_zero :
    ∀ {x y : k} (hxy : (E⁄k).Nonsingular x y),
      (2 : ℕ) • Affine.Point.some x y hxy = 0 ↔
        (E.Ψ₂Sq).eval x = 0)

theorem preΨ'_root_not_Ψ₂Sq_root
    {n : ℕ} {x : k}
    (hn : (n : k) ≠ 0)
    (hpre : (E.preΨ' n).eval x = 0) :
    (E.Ψ₂Sq).eval x ≠ 0 := by
  intro htwo
  obtain ⟨y, hxy, h2_ne, _hnP⟩ :=
    (preΨ'_eval_eq_zero_iff_exists_non_two_torsion (E := E) hn).mp hpre
  exact h2_ne ((two_nsmul_eq_zero_iff_Ψ₂Sq_eval_eq_zero (E := E) hxy).mpr htwo)

end WeierstrassCurve
```

For the exact “no common root” finite-set form:

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

noncomputable section

open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine
open Polynomial

namespace WeierstrassCurve

universe u

variable {k : Type u} [Field k] [IsSepClosed k] [DecidableEq k]
variable (E : WeierstrassCurve k) [E.IsElliptic]

variable
  (preΨ'_eval_eq_zero_iff_exists_non_two_torsion :
    ∀ {n : ℕ} {x : k}, (n : k) ≠ 0 →
      ((E.preΨ' n).eval x = 0 ↔
        ∃ y (hxy : (E⁄k).Nonsingular x y),
          (2 : ℕ) • Affine.Point.some x y hxy ≠ 0 ∧
          n • Affine.Point.some x y hxy = 0))

variable
  (two_nsmul_eq_zero_iff_Ψ₂Sq_eval_eq_zero :
    ∀ {x y : k} (hxy : (E⁄k).Nonsingular x y),
      (2 : ℕ) • Affine.Point.some x y hxy = 0 ↔
        (E.Ψ₂Sq).eval x = 0)

theorem disjoint_rootSet_preΨ'_Ψ₂Sq
    {n : ℕ} (hn : (n : k) ≠ 0) :
    Disjoint
      ((E.preΨ' n).rootSet k)
      ((E.Ψ₂Sq).rootSet k) := by
  rw [Finset.disjoint_left]
  intro x hxpre hx2
  have hpre : (E.preΨ' n).eval x = 0 := by
    simpa [Polynomial.mem_rootSet] using hxpre
  have htwo : (E.Ψ₂Sq).eval x = 0 := by
    simpa [Polynomial.mem_rootSet] using hx2
  obtain ⟨y, hxy, h2_ne, _hnP⟩ :=
    (preΨ'_eval_eq_zero_iff_exists_non_two_torsion (E := E) hn).mp hpre
  exact h2_ne ((two_nsmul_eq_zero_iff_Ψ₂Sq_eval_eq_zero (E := E) hxy).mpr htwo)

end WeierstrassCurve
```

### Why not the resultant route?

The resultant route would be:

```lean
have hcop : IsCoprime (E.preΨ' n) E.Ψ₂Sq := ...
have hres : (E.preΨ' n).resultant E.Ψ₂Sq ≠ 0 := ...
```

Mathlib’s generic bridge exists: `Polynomial.resultant_eq_zero_iff` and `Polynomial.isUnit_resultant_iff_isCoprime` are in the resultant API. But using them here still requires a new hard theorem proving the specific resultant is nonzero, essentially a normalized division-polynomial resultant formula. citeturn288366view1

So the direct point proof is shorter and more stable. It uses exactly the mathematical reason you want: `preΨ'_n` parametrizes **non-2** `n`-torsion roots, while `Ψ₂Sq` is the two-torsion cubic; Mathlib documents `Ψ₂Sq` as the univariate polynomial congruent to `ψ₂²` and as `twoTorsionPolynomial.toPoly`. citeturn288366view0

The only caveat is that the proof depends on the root-realization seam being stated with the **non-2-torsion conclusion**:

```lean
∃ y hxy,
  (2 : ℕ) • Affine.Point.some x y hxy ≠ 0 ∧
  n • Affine.Point.some x y hxy = 0
```

If SEAM2 only gives `n • P = 0`, strengthen it to include `2 • P ≠ 0`. That is precisely the design invariant of `preΨ'`, including the even case where the two-torsion roots belong to the separate `Ψ₂Sq` factor of `ΨSq`.
