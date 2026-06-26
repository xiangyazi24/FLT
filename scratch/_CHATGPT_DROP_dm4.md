# Q707 (dm4): domain proof for `(X₀ - X₁)^3 ∣ formalAddX`

## Important correction

The `addX_eq'` part of the proof is straightforward and should be done exactly as you described.  It proves the **multiplied** divisibility

```lean
(X₀ - X₁)^3 ∣ formalAddX W * (w₀ * w₁)^2.
```

However, `NoZeroDivisors` alone does **not** justify the last cancellation step

```text
c^3 ∣ f * z  ⇒  c^3 ∣ f.
```

That implication is false in a domain in general; for example, in `ℤ`, `2 ∣ 3 * 2`, but `2 ∤ 3`.  The last step needs the same extra diagonal-vs-axis cancellation lemma used by the existing `formalAddZ_dvd_cube_of_noZeroDivisors` proof: morally, `(X₀ - X₁)` is coprime to `X₀^6 X₁^6` and to the unit part of `(w₀*w₁)^2`.

So the proof should be split into two pieces:

1. a fully algebraic `addX_eq'` proof of
   ```lean
   (X₀ - X₁)^3 ∣ formalAddX W * (w₀*w₁)^2;
   ```
2. reuse the existing diagonal-cancellation lemma from the `formalAddZ` proof to remove `(w₀*w₁)^2`.

The first piece below is the part that directly uses Mathlib’s `Projective.addX_eq'`.  The final theorem is written so the cancellation lemma is a hypothesis; in your file, instantiate that hypothesis with the same lemma/pattern used in `formalAddZ_dvd_cube_of_noZeroDivisors`.

---

## Compilable algebraic core

This block has no `sorry`.  It proves the core `addX_eq'` divisibility under the two diagonal-difference hypotheses.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.Tactic

noncomputable section

namespace Q707

open WeierstrassCurve

local notation "x" => (0 : Fin 3)
local notation "y" => (1 : Fin 3)
local notation "z" => (2 : Fin 3)

namespace Projective

variable {S : Type*} [CommRing S]

/-- The pure algebraic divisibility consequence of Mathlib's projective `addX_eq'`.

If both

```text
Py*Qz - Qy*Pz
Px*Qz - Qx*Pz
```

are divisible by `c`, then `addX P Q * (Pz*Qz)^2` is divisible by `c^3`.
This is the exact formal computation needed before the final cancellation of `(w₀*w₁)^2`.
-/
lemma addX_mul_zsq_dvd_cube_of_slope_delta
    (W : WeierstrassCurve.Projective S) (P Q : Fin 3 → S)
    (c slopeQuot deltaQuot : S)
    (hP : W.Equation P) (hQ : W.Equation Q)
    (hslope : P y * Q z - Q y * P z = c * slopeQuot)
    (hdelta : P x * Q z - Q x * P z = c * deltaQuot) :
    c ^ 3 ∣ W.addX P Q * (P z * Q z) ^ 2 := by
  refine ⟨
    ((slopeQuot ^ 2 * P z * Q z
      + W.a₁ * slopeQuot * P z * Q z * deltaQuot
      - W.a₂ * P z * Q z * deltaQuot ^ 2
      - P x * Q z * deltaQuot ^ 2
      - Q x * P z * deltaQuot ^ 2) * deltaQuot), ?_⟩
  rw [WeierstrassCurve.Projective.addX_eq' (W' := W) (P := P) (Q := Q) hP hQ]
  rw [hslope, hdelta]
  ring

/-- Same result, but with an abstract series/function `A` known to be `W.addX P Q`.

This is the form that plugs into `formalAddX`: first rewrite `formalAddX` to the projective
formula, use `addX_mul_zsq_dvd_cube_of_slope_delta`, then use the caller-provided cancellation
lemma to remove `(Pz*Qz)^2`.
-/
lemma addX_dvd_cube_of_slope_delta_and_cancel
    (W : WeierstrassCurve.Projective S) (P Q : Fin 3 → S)
    (A c slopeQuot deltaQuot : S)
    (hA : A = W.addX P Q)
    (hP : W.Equation P) (hQ : W.Equation Q)
    (hslope : P y * Q z - Q y * P z = c * slopeQuot)
    (hdelta : P x * Q z - Q x * P z = c * deltaQuot)
    (hcancel : c ^ 3 ∣ A * (P z * Q z) ^ 2 → c ^ 3 ∣ A) :
    c ^ 3 ∣ A := by
  apply hcancel
  rw [hA]
  exact addX_mul_zsq_dvd_cube_of_slope_delta
    (W := W) (P := P) (Q := Q)
    (c := c) (slopeQuot := slopeQuot) (deltaQuot := deltaQuot)
    hP hQ hslope hdelta

end Projective

end Q707
```

---

## Drop-in specialization to formal points

Below is the theorem shape I would use in the actual formal group file.  It is written to make the dependency on the existing cancellation lemma explicit.

Rename the local facts to match your file.  The facts needed are exactly the ones already present or used in the `formalAddZ` proof:

```lean
formalPointMv_equation
formalSlope_eq_sub_mul_quot      -- w₀ - w₁ = (X₀ - X₁) * slopeQuot
formalDelta_eq_sub_mul_quot      -- X₀*w₁ - X₁*w₀ = (X₀ - X₁) * deltaQuot
formalAddX_def / rfl             -- formalAddX is projective addX at formal points
formal_cancel_zsq_dvd_cube       -- the cancellation step from formalAddZ_dvd_cube_of_noZeroDivisors
```

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.Tactic
-- import your local FormalGroupW file

noncomputable section

open MvPowerSeries Finsupp
open WeierstrassCurve

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [NoZeroDivisors R]

local notation "X₀" =>
  (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R)
local notation "X₁" =>
  (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R)
local notation "δ" => (X₀ - X₁)

local notation "x" => (0 : Fin 3)
local notation "y" => (1 : Fin 3)
local notation "z" => (2 : Fin 3)

/-- Domain proof for the formal `addX` numerator.

The proof is intentionally the same pattern as `formalAddZ_dvd_cube_of_noZeroDivisors`:
first prove divisibility after multiplying by `(w₀*w₁)^2`, then invoke the existing
formal-point `z`-coordinate cancellation lemma.
-/
lemma formalAddX_dvd_cube_of_noZeroDivisors
    (W : WeierstrassCurve R) :
    δ ^ 3 ∣ formalAddX W := by
  classical
  let Cmv : R →+* MvPowerSeries (Fin 2) R := MvPowerSeries.C
  let Wmv := W.map Cmv
  let P : Fin 3 → MvPowerSeries (Fin 2) R := formalPointMv W 0
  let Q : Fin 3 → MvPowerSeries (Fin 2) R := formalPointMv W 1
  let slopeQuot : MvPowerSeries (Fin 2) R := formalSlopeQuot W
  let deltaQuot : MvPowerSeries (Fin 2) R := formalDeltaQuot W

  have hP : Wmv.Equation P := by
    simpa [Wmv, P, Cmv] using formalPointMv_equation (W := W) (i := 0)

  have hQ : Wmv.Equation Q := by
    simpa [Wmv, Q, Cmv] using formalPointMv_equation (W := W) (i := 1)

  -- `Py = Qy = -1`, so this is exactly `w₀ - w₁`.
  have hslope :
      P y * Q z - Q y * P z = δ * slopeQuot := by
    simpa [P, Q, slopeQuot, δ, formalPointMv, mul_comm, mul_left_comm, mul_assoc] using
      formalSlope_eq_sub_mul_quot (W := W)

  -- This is `X₀*w₁ - X₁*w₀ = (X₀ - X₁) * formalDeltaQuot W`.
  have hdelta :
      P x * Q z - Q x * P z = δ * deltaQuot := by
    simpa [P, Q, deltaQuot, δ, formalPointMv, mul_comm, mul_left_comm, mul_assoc] using
      formalDelta_eq_sub_mul_quot (W := W)

  -- This is the only nontrivial domain/coprimality step.  Reuse the same helper used
  -- in `formalAddZ_dvd_cube_of_noZeroDivisors`.  It should use
  -- `wᵢ = Xᵢ^3 * unit`, plus the fact that `(X₀ - X₁)` is coprime to the axis
  -- monomials `X₀` and `X₁`.
  have hcancel :
      δ ^ 3 ∣ formalAddX W * (P z * Q z) ^ 2 → δ ^ 3 ∣ formalAddX W := by
    intro hmul
    exact formal_cancel_zsq_dvd_cube_of_noZeroDivisors
      (W := W) (F := formalAddX W) hmul

  exact Q707.Projective.addX_dvd_cube_of_slope_delta_and_cancel
    (W := Wmv) (P := P) (Q := Q)
    (A := formalAddX W)
    (c := δ)
    (slopeQuot := slopeQuot)
    (deltaQuot := deltaQuot)
    (hA := by simp [formalAddX, Wmv, P, Q, Cmv])
    hP hQ hslope hdelta hcancel

end WeierstrassCurve
```

---

## If the cancellation lemma is not already factored out

Do **not** try to prove the last step with only `mul_right_cancel₀`; that proves equality cancellation, not ideal/divisibility cancellation.  The lemma you need has this shape:

```lean
lemma formal_cancel_zsq_dvd_cube_of_noZeroDivisors
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (W : WeierstrassCurve R)
    (F : MvPowerSeries (Fin 2) R) :
    (X₀ - X₁) ^ 3 ∣ F *
      (((formalPointMv W 0) (2 : Fin 3) * (formalPointMv W 1) (2 : Fin 3)) ^ 2) →
    (X₀ - X₁) ^ 3 ∣ F := by
  -- exactly the cancellation code already used for `formalAddZ_dvd_cube_of_noZeroDivisors`
  -- using:
  --   (formalPointMv W 0).z = X₀^3 * unit
  --   (formalPointMv W 1).z = X₁^3 * unit
  -- and diagonal/axis coprimality.
  ...
```

If the existing `formalAddZ` proof has this cancellation inline, extract it first.  Then both `formalAddZ` and `formalAddX` become short, and the `addX`-specific proof is just the `addX_eq'` calculation above.
