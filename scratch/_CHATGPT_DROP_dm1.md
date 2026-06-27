# Q1219 (dm1): finiteness of elliptic-curve `m`-torsion

## Result

I cannot honestly give a non-`sorry`, import-`Mathlib`-only proof of the requested theorem from the current Mathlib division-polynomial API.

There are two separate blockers.

1. The requested Lean statement as written does not parse as Lean:
   * `N` should be `ℕ` or `Nat`.
   * For an additive group, multiplication by a natural number is written `(m : ℕ) • P`, not `(m : N) * P`.
   * The base-change notation used in the FLT file is `(E⁄k).Point`, not `(E/k).Point`.

2. The current Mathlib division-polynomial files define the relevant polynomials, but do not yet contain the theorem connecting `m • P = 0` to the vanishing of the evaluated division polynomial at the `x`-coordinate of `P`. In particular:
   * `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` defines `preΨ`, `ΨSq`, `Ψ`, `ψ`, and `φ`.
   * `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` proves degree and nonzero results, but the key nonzero result for `ΨSq n` assumes `(n : k) ≠ 0`, so it does not by itself handle the characteristic-dividing-`m` case.
   * The FLT repo file `FLT/EllipticCurve/Torsion.lean` already defines
     ```lean
     abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u :=
       Submodule.torsionBy ℤ (E⁄k).Point n
     ```
     and has
     ```lean
     theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) :
         Finite (E.nTorsion n) := sorry
     ```
     so the desired finiteness is already represented there, but not proved.

The useful piece that *does* compile with import `Mathlib` only is the final reduction from a finite `ℤ`-torsion submodule to the requested `Set.Finite` statement. This is exactly the part that should be used once the division-polynomial theorem supplies the missing `Finite (Submodule.torsionBy ℤ (E⁄k).Point (m : ℤ))` instance.

## Mathlib-only compilable reduction

```lean
import Mathlib

open WeierstrassCurve

theorem mTorsion_finite_from_finite_torsionBy
    (k : Type*) [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    (m : ℕ) (_hm : 0 < m)
    (hfin : Finite (Submodule.torsionBy ℤ (E⁄k).Point (m : ℤ))) :
    Set.Finite {P : (E⁄k).Point | (m : ℕ) • P = 0} := by
  classical
  haveI : Finite (Submodule.torsionBy ℤ (E⁄k).Point (m : ℤ)) := hfin
  let val : Submodule.torsionBy ℤ (E⁄k).Point (m : ℤ) → (E⁄k).Point := fun Q => Q.1
  refine (Set.finite_range val).subset ?_
  intro P hP
  refine ⟨⟨P, ?_⟩, rfl⟩
  rw [Submodule.mem_torsionBy_iff]
  simpa using hP
```

This is the clean endpoint for the division-polynomial proof: prove the finite typeclass for the `Submodule.torsionBy`, then apply this theorem.

## Wrapper that compiles in FLT, but not with import `Mathlib` only

The following theorem is the exact corrected set statement, proved from the existing FLT theorem `WeierstrassCurve.n_torsion_finite`. This does **not** satisfy the requested import restriction, and it relies on the current `sorry` inside `FLT/EllipticCurve/Torsion.lean`; I include it only to show that the final wrapper from the FLT theorem is straightforward.

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

open WeierstrassCurve

theorem mTorsion_finite
    (k : Type*) [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    (m : ℕ) (hm : 0 < m) :
    Set.Finite {P : (E⁄k).Point | (m : ℕ) • P = 0} := by
  classical
  haveI : Finite (Submodule.torsionBy ℤ (E⁄k).Point (m : ℤ)) := by
    simpa [WeierstrassCurve.nTorsion] using (E.n_torsion_finite (n := m) hm)
  let val : Submodule.torsionBy ℤ (E⁄k).Point (m : ℤ) → (E⁄k).Point := fun Q => Q.1
  refine (Set.finite_range val).subset ?_
  intro P hP
  refine ⟨⟨P, ?_⟩, rfl⟩
  rw [Submodule.mem_torsionBy_iff]
  simpa using hP
```

## What is missing for a genuine division-polynomial proof

A complete Mathlib-only proof of the requested theorem should add, at minimum, the following API.

```lean
import Mathlib

open Polynomial
open WeierstrassCurve

/-- Missing API, schematic only: torsion points satisfy a univariate division-polynomial equation. -/
-- theorem torsion_eval_divisionPolynomial_eq_zero
--     (k : Type*) [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
--     (m : ℕ) (hm : 0 < m)
--     {x y : k} (hxy : (E⁄k).Nonsingular x y)
--     (htors : (m : ℕ) • WeierstrassCurve.Affine.Point.some x y hxy = 0) :
--     Polynomial.eval x ((E⁄k).ΨSq (m : ℤ)) = 0 := by
--   ...

/-- Missing API, schematic only: a nonzero polynomial controlling the `x`-coordinates exists
in every characteristic, including the characteristic-dividing-`m` case. -/
-- theorem exists_nonzero_divisionPolynomial_for_torsion
--     (k : Type*) [Field k] (E : WeierstrassCurve k) [E.IsElliptic]
--     (m : ℕ) (hm : 0 < m) :
--     ∃ f : k[X], f ≠ 0 ∧
--       ∀ {x y : k} (hxy : (E⁄k).Nonsingular x y),
--         (m : ℕ) • WeierstrassCurve.Affine.Point.some x y hxy = 0 →
--         Polynomial.eval x f = 0 := by
--   ...
```

Once those are available, the remaining finiteness argument is standard: finitely many roots for the nonzero univariate polynomial, at most two affine points above each `x` by the existing `Y_eq_of_X_eq`/negation API, plus the point at infinity.
