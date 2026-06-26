# Q663 (dm3): `formalAddY` coefficient and `normalizedAddY_constantCoeff`

## Short answer

Yes: use the universal ring, but only for the **raw numerator** coefficient

```lean
coeff (single 0 3) (formalAddY W) = 1.
```

Do **not** try to compute `normalizedAddY = formalAddY_dvd_cube.choose`.  Once you know

```lean
formalAddY W = (X₀ - X₁) ^ 3 * normalizedAddY W
```

and you already have the extraction lemma

```lean
coeff (single 0 3) ((X₀ - X₁) ^ 3 * q) = constantCoeff q,
```

`normalizedAddY_constantCoeff` is immediate.

The robust architecture is:

1. Prove one closed universal certificate:

```lean
formalAddY_coeff_e30_univ :
  coeff (single 0 3) (formalAddY univWeierstrassCurve) = 1
```

2. Transport it to arbitrary `W` using `formalAddXYZ_map` and `univEval_map`.
3. Apply your degree-3 extraction lemma to the quotient equation.

The important practical point is that `native_decide` should be isolated in the universal certificate, not buried in the final theorem.  If `native_decide` on the full power-series definition does not terminate, replace only that certificate by a generated finite expansion proof.  The transport and quotient proofs below do not change.

---

## Lean code: transport from the universal coefficient

This is the Lean shape I would use.  Replace the import line and local theorem names with the names in your project; the proof structure is the part that matters.

```lean
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic
-- import FLT.YourFile.DefiningFormalAddY

noncomputable section

open Finsupp

namespace WeierstrassCurve

section FormalAddYCoeff

variable {R : Type*} [CommRing R]

local notation "S" => MvPowerSeries (Fin 2) R
local notation "e₀" n => Finsupp.single (0 : Fin 2) n
local notation "X₀" => (MvPowerSeries.X (0 : Fin 2) : S)
local notation "X₁" => (MvPowerSeries.X (1 : Fin 2) : S)
local notation "δ" => (X₀ - X₁)

/--
The single universal finite computation.

This theorem should live near the definitions of the universal Weierstrass curve.
It involves no `choose`, no quotient, and no arbitrary ring `R`.

If this closes quickly, keep it exactly as `native_decide`.
If it does not close, prove this one theorem by unfolding the finite projective
addition formula over the universal coefficient ring and finishing the resulting
polynomial equality by `norm_num`/`ring_nf`/a generated CAS certificate.
-/
private theorem formalAddY_coeff_e30_univ :
    MvPowerSeries.coeff
        (MvPolynomial (Fin 5) ℤ)
        (Finsupp.single (0 : Fin 2) 3)
        (univWeierstrassCurve.formalAddY)
      = (1 : MvPolynomial (Fin 5) ℤ) := by
  -- Best case: the coefficient evaluator reduces the finite jet.
  -- This is deliberately isolated: if it is too slow, replace only this proof.
  native_decide

/--
Transport the universal coefficient computation to any coefficient ring and any
Weierstrass curve.
-/
theorem formalAddY_coeff_e30 (W : WeierstrassCurve R) :
    MvPowerSeries.coeff R (e₀ 3) W.formalAddY = 1 := by
  classical

  -- The universal coefficient ring and specialization map.
  let A := MvPolynomial (Fin 5) ℤ
  let W₀ : WeierstrassCurve A := univWeierstrassCurve
  let φ : A →+* R := univEval W

  -- Naturality of formal addition, specialized to the Y-coordinate.
  -- Your theorem may have the opposite orientation; use `.symm` if needed.
  have hmapXYZ := formalAddXYZ_map φ W₀ (1 : Fin 3)

  have hmap :
      MvPowerSeries.map φ W₀.formalAddY = W.formalAddY := by
    -- `univEval_map` should rewrite `W₀.map φ` to `W`.
    -- The `formalAddY` simp may be unnecessary if `formalAddXYZ_map` is already
    -- stated directly for `formalAddY`.
    simpa [W₀, φ, formalAddY, univEval_map] using hmapXYZ

  -- Apply coefficient to the map identity and commute coefficient with map.
  calc
    MvPowerSeries.coeff R (e₀ 3) W.formalAddY
        = MvPowerSeries.coeff R (e₀ 3)
            (MvPowerSeries.map φ W₀.formalAddY) := by
            rw [hmap]
    _ = φ (MvPowerSeries.coeff A (e₀ 3) W₀.formalAddY) := by
            simpa [A, W₀] using
              (MvPowerSeries.coeff_map
                (f := φ)
                (n := e₀ 3)
                (φ := W₀.formalAddY))
    _ = 1 := by
            simp [A, W₀, formalAddY_coeff_e30_univ]

end FormalAddYCoeff

end WeierstrassCurve
```

### If `formalAddXYZ_map` has the other orientation

If your map theorem says

```lean
W.formalAddY = MvPowerSeries.map φ W₀.formalAddY
```

instead of

```lean
MvPowerSeries.map φ W₀.formalAddY = W.formalAddY,
```

just change the `hmap` proof to:

```lean
  have hmap :
      MvPowerSeries.map φ W₀.formalAddY = W.formalAddY := by
    simpa [W₀, φ, formalAddY, univEval_map] using hmapXYZ.symm
```

Everything else is unchanged.

---

## Making the universal certificate reliable

I would first try this exact theorem:

```lean
private theorem formalAddY_coeff_e30_univ :
    MvPowerSeries.coeff
        (MvPolynomial (Fin 5) ℤ)
        (Finsupp.single (0 : Fin 2) 3)
        (univWeierstrassCurve.formalAddY)
      = (1 : MvPolynomial (Fin 5) ℤ) := by
  native_decide
```

But I would **not** rely on this being fast.  `native_decide` only works well if the coefficient expression reduces to a decidable polynomial equality without unfolding too much recursive power-series infrastructure.

If it is slow or times out, keep the theorem statement and replace the proof by a controlled finite expansion.  The proof should unfold only the Y-coordinate formula and use the already-known low-degree vanishings for `addX` and `addZ`:

```lean
private theorem formalAddY_coeff_e30_univ :
    MvPowerSeries.coeff
        (MvPolynomial (Fin 5) ℤ)
        (Finsupp.single (0 : Fin 2) 3)
        (univWeierstrassCurve.formalAddY)
      = (1 : MvPolynomial (Fin 5) ℤ) := by
  -- Schematic controlled proof:
  --   formalAddY = -negAddY_formal - C(a₁) * addX_formal - C(a₃) * addZ_formal
  --   coeff_e30 negAddY_formal = -1
  --   coeff_e30 addX_formal = 0
  --   coeff_e30 addZ_formal = 0
  -- so the coefficient is -(-1) - a₁*0 - a₃*0 = 1.
  --
  -- In the universal ring this is a finite computation.  Put the generated
  -- coefficient lemmas here or unfold the finite formula and finish by `ring_nf`.
  rw [formalAddY_eq_neg_negAddY_sub_a1_addX_sub_a3_addZ]
  simp [
    MvPowerSeries.coeff_neg,
    MvPowerSeries.coeff_add,
    MvPowerSeries.coeff_sub,
    MvPowerSeries.coeff_C_mul,
    negAddY_formal_coeff_e30_univ,
    addX_formal_coeff_e30_univ,
    addZ_formal_coeff_e30_univ
  ]
```

The names in that controlled proof are placeholders for your local names, but the identity is exactly the one you wrote:

```text
formalAddY = -negAddY_formal - C(a₁) * addX_formal - C(a₃) * addZ_formal.
```

The point is that the entire hard computation remains inside one theorem over

```lean
MvPolynomial (Fin 5) ℤ
```

and the arbitrary-ring theorem never unfolds the addition formula.

---

## Lean code: `normalizedAddY_constantCoeff`

Now use the universal coefficient theorem plus your already-proved extraction lemma.

Assume your degree-3 extraction lemma has the following shape:

```lean
lemma coeff_e30_delta_cube_mul
    {R : Type*} [CommRing R]
    (q : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff R (Finsupp.single (0 : Fin 2) 3)
      (((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R)
        - (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R)) ^ 3 * q)
      = MvPowerSeries.constantCoeff R q := by
  ...
```

Then the final proof is:

```lean
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic
-- import FLT.YourFile.FormalAddYCoeff

noncomputable section

open Finsupp

namespace WeierstrassCurve

section NormalizedAddYConstant

variable {R : Type*} [CommRing R]

local notation "S" => MvPowerSeries (Fin 2) R
local notation "e₀" n => Finsupp.single (0 : Fin 2) n
local notation "X₀" => (MvPowerSeries.X (0 : Fin 2) : S)
local notation "X₁" => (MvPowerSeries.X (1 : Fin 2) : S)
local notation "δ" => (X₀ - X₁)

/-- The constant coefficient of the normalized Y denominator is `1`. -/
theorem normalizedAddY_constantCoeff (W : WeierstrassCurve R) :
    MvPowerSeries.constantCoeff R W.normalizedAddY = 1 := by
  classical

  -- The product equation supplied by `Dvd.dvd.choose`.
  -- If your `choose_spec` is oriented as
  --   W.formalAddY = δ ^ 3 * W.normalizedAddY,
  -- use `.symm` below.
  have hdiv : δ ^ 3 * W.normalizedAddY = W.formalAddY := by
    simpa [δ, normalizedAddY] using
      (W.formalAddY_dvd_cube.choose_spec)

  have hcoeff := congrArg
    (fun f : S => MvPowerSeries.coeff R (e₀ 3) f)
    hdiv

  -- Left side: extraction from `(X₀-X₁)^3 * normalizedAddY`.
  rw [coeff_e30_delta_cube_mul] at hcoeff

  -- Right side: universal-ring computation transported to `W`.
  rw [formalAddY_coeff_e30 W] at hcoeff

  simpa using hcoeff

end NormalizedAddYConstant

end WeierstrassCurve
```

If your `choose_spec` has the opposite orientation, change only this part:

```lean
  have hdiv : δ ^ 3 * W.normalizedAddY = W.formalAddY := by
    simpa [δ, normalizedAddY] using
      (W.formalAddY_dvd_cube.choose_spec).symm
```

---

## Why this is the right split

The universal theorem proves a low-jet fact about the numerator `formalAddY`; it is independent of `Dvd.dvd.choose`.  The final normalized theorem uses only the product equation from `choose_spec`, so it never depends on how Lean chose the quotient.

That separation avoids the two main traps:

1. trying to compute an arbitrary `choose`, and
2. asking `native_decide` to normalize a large arbitrary-ring expression.

The only concrete computation is the closed universal theorem

```lean
formalAddY_coeff_e30_univ
```

and once it exists, both

```lean
formalAddY_coeff_e30 W
normalizedAddY_constantCoeff W
```

are short transport/extraction proofs.
