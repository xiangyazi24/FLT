# Q499 (dm3): `(X₀-X₁)` prime/non-zero-divisor in `MvPowerSeries (Fin 2) K`

## Bottom line

For the immediate `addZ` proof, do **not** make the first target

```lean
Prime (X₀ - X₁ : MvPowerSeries (Fin 2) K)
```

or a UFD instance for `MvPowerSeries (Fin 2) K`.  Mathematically this is true over a field, but it is not the Lean-shortest route.

The useful route is to change coordinates from `(X₀,X₁)` to

```text
S = X₁,
H = X₀ - X₁.
```

Then

```text
K⟦X₀,X₁⟧ ≃ (K⟦S⟧)⟦H⟧,
X₀-X₁ ↦ H.
```

After this coordinate change, the desired statement is only a one-variable power-series statement in the variable `H`.

---

## Mathlib API status

The public `MvPowerSeries.Basic` API has the important coordinate-variable lemmas

```lean
MvPowerSeries.X_pow_dvd_iff
MvPowerSeries.X_dvd_iff
```

with the shape

```lean
X s ^ n ∣ φ ↔ ∀ m, m s < n → coeff m φ = 0
X s ∣ φ     ↔ ∀ m, m s = 0 → coeff m φ = 0
```

I do not see exposed declarations named

```lean
MvPowerSeries.Prime
MvPowerSeries.UniqueFactorizationDomain
PowerSeries.Prime
```

so I would not base the implementation on those names.  `Prime.dvd_mul` is a general algebra lemma once one has a `Prime p` hypothesis, but the hard part here is producing `Prime (X₀-X₁)`.

There is general quotient infrastructure via `Ideal.Quotient`, but I would not expect a ready-made specialized isomorphism

```lean
MvPowerSeries (Fin 2) K ⧸ Ideal.span {X₀-X₁} ≃+* PowerSeries K
```

You can prove it, but it requires defining diagonal evaluation and proving its kernel is exactly `(X₀-X₁)`.  That is heavier than needed for this cancellation.

---

## Non-zero-divisor is not enough

A non-zero-divisor proof gives cancellation from equalities:

```text
δ^3 * A = δ^3 * B  ⇒  A = B.
```

It does **not** give the divisibility transfer

```text
δ^3 ∣ A * B  and  δ ∤ B  ⇒  δ^3 ∣ A.
```

For that you need primality, coprimality, or an order/valuation argument.  The order argument is easiest here.

---

## One-variable cancellation lemma

Work in `PowerSeries R`, where `R` is a domain.

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Order

namespace PowerSeries

variable {R : Type*} [CommRing R] [NoZeroDivisors R]

/-- If `B` has nonzero constant coefficient, then multiplication by `B`
does not create extra `X`-adic divisibility. -/
theorem X_pow_dvd_cancel_right_constCoeff_ne_zero
    {A B : PowerSeries R} {n : ℕ}
    (hB0 : PowerSeries.constantCoeff B ≠ 0)
    (h : PowerSeries.X ^ n ∣ A * B) :
    PowerSeries.X ^ n ∣ A := by
  -- Proof plan:
  --   rw [PowerSeries.X_pow_dvd_iff] at h ⊢
  --   intro m hm
  --   strong induction on m.
  --   Expand coeff m (A*B) using `PowerSeries.coeff_mul`.
  --   Lower coefficients of A vanish by induction.
  --   The remaining term is `(coeff m A) * constantCoeff B = 0`.
  --   Since `constantCoeff B ≠ 0` and `R` is a domain, `coeff m A = 0`.
  sorry

end PowerSeries
```

This lemma is enough.  It does not require `B` to be a unit.  It only requires the constant coefficient of `B` in the distinguished variable to be nonzero.

---

## Difference-coordinate equivalence

Define a reusable equivalence, or reuse the diagonal/Taylor substitution map from Q478.

Schematic API:

```lean
namespace FormalGroupW

open MvPowerSeries PowerSeries

variable {K : Type*} [CommRing K]

abbrev FG2 := MvPowerSeries (Fin 2) K
abbrev Inner := PowerSeries K
abbrev Outer := PowerSeries Inner

noncomputable def diffCoord : FG2 K ≃+* Outer K :=
  -- X₀ ↦ C(S) + H
  -- X₁ ↦ C(S)
  -- inverse: S ↦ X₁, H ↦ X₀ - X₁
  sorry

theorem diffCoord_X0 :
    diffCoord (K := K) (MvPowerSeries.X (0 : Fin 2)) =
      PowerSeries.C (PowerSeries.X : PowerSeries K) + PowerSeries.X := by
  sorry

theorem diffCoord_X1 :
    diffCoord (K := K) (MvPowerSeries.X (1 : Fin 2)) =
      PowerSeries.C (PowerSeries.X : PowerSeries K) := by
  sorry

theorem diffCoord_delta :
    diffCoord (K := K)
      (MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) =
      PowerSeries.X := by
  simp [diffCoord_X0, diffCoord_X1]

end FormalGroupW
```

If there is no substitution API, define `diffCoord` coefficientwise by the finite binomial formula

```text
f(X₀,X₁) = Σ aᵢⱼ X₀^i X₁^j
f(S+H,S) = Σ aᵢⱼ (S+H)^i S^j
          = Σ aᵢⱼ Σ_{r≤i} binom(i,r) H^r S^{i-r+j}.
```

For fixed `H^r S^m`, only finitely many pairs contribute, so this is a legitimate coefficient definition.  The inverse is the substitution

```text
S ↦ X₁,
H ↦ X₀-X₁.
```

---

## Applying it to `w₀w₁`

Let

```text
w₀ = w(X₀),
w₁ = w(X₁),
δ = X₀-X₁.
```

Under `diffCoord`,

```text
w₀ ↦ w(S+H),
w₁ ↦ w(S).
```

Therefore the constant coefficient in the outer `H` variable is

```text
constantCoeff_H (w(S+H) * w(S)) = w(S)^2.
```

This is nonzero in `K⟦S⟧`, because the formal parameter series satisfies

```text
w(T) = T^3 * unit
```

or equivalently has nonzero coefficient at degree `3`.  Since `K` is a field, `K⟦S⟧` is a domain, so `w(S)^2 ≠ 0`.

Important: the ordinary total constant coefficient of `w₀w₁` in `K⟦X₀,X₁⟧` is zero.  The useful nonzero coefficient is the constant coefficient in the **difference variable** `H`, with coefficient ring `K⟦S⟧`.

---

## Final theorem shape

```lean
namespace FormalGroupW

open MvPowerSeries PowerSeries

variable {K : Type*} [Field K]

abbrev FG2 := MvPowerSeries (Fin 2) K

def δ : FG2 K := MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)

noncomputable def w0 : FG2 K := ...
noncomputable def w1 : FG2 K := ...
noncomputable def formalAddZ : FG2 K := ...

theorem diffCoord_w0w1_constCoeff_ne_zero :
    PowerSeries.constantCoeff (diffCoord (K := K) (w0 * w1)) ≠ 0 := by
  -- simplify to `w(S)^2 ≠ 0`
  -- use `w = X^3 * unit` or `coeff 3 w = 1`
  sorry

theorem delta_pow3_dvd_addZ_of_dvd_mul_w0w1
    (h : δ (K := K)^3 ∣ formalAddZ * (w0 * w1)) :
    δ (K := K)^3 ∣ formalAddZ := by
  have hmap :
      PowerSeries.X ^ 3 ∣
        diffCoord (K := K) formalAddZ * diffCoord (K := K) (w0 * w1) := by
    -- apply `diffCoord` to h and simplify using `diffCoord_delta`
    sorry

  have hB0 :
      PowerSeries.constantCoeff (diffCoord (K := K) (w0 * w1)) ≠ 0 :=
    diffCoord_w0w1_constCoeff_ne_zero (K := K)

  have hA : PowerSeries.X ^ 3 ∣ diffCoord (K := K) formalAddZ :=
    PowerSeries.X_pow_dvd_cancel_right_constCoeff_ne_zero hB0 hmap

  rcases hA with ⟨Q, hQ⟩
  refine ⟨diffCoord.symm Q, ?_⟩
  -- Apply `diffCoord.injective`; map both sides and simplify.
  sorry

end FormalGroupW
```

---

## If you still want `Prime δ`

The mathematical proof is:

```text
K⟦X₀,X₁⟧/(X₀-X₁) ≅ K⟦X₁⟧,
```

and the right-hand side is a domain, so `(X₀-X₁)` generates a prime ideal.  From there one can package an element-level `Prime (X₀-X₁)` if the needed principal-ideal API is convenient.

But the quotient proof needs:

```lean
def diagEval : MvPowerSeries (Fin 2) K →+* PowerSeries K
-- X₀ ↦ X, X₁ ↦ X

theorem ker_diagEval :
    RingHom.ker diagEval = Ideal.span {X₀ - X₁}

theorem diagEval_surjective : Function.Surjective diagEval
```

This is clean but heavier than the difference-coordinate cancellation.

---

## Minimal atom list

1. `scratch/FormalGroupW_XCancel.lean` — prove the one-variable cancellation lemma for `PowerSeries.X^n`.  Estimated 80–160 lines.
2. `scratch/FormalGroupW_DiffCoord.lean` — define `diffCoord`, prove images of `X₀`, `X₁`, and `δ`.  Estimated 200–400 lines if coefficient-defined from scratch; much less if Q478's substitution map is reusable.
3. `scratch/FormalGroupW_WDiffOrder.lean` — prove `constantCoeff_H(diffCoord (w0*w1)) ≠ 0`.  Estimated 80–150 lines.
4. `scratch/FormalGroupW_AddZCancel.lean` — combine the pieces to prove `δ^3 ∣ addZ` from `δ^3 ∣ addZ*w0*w1`.  Estimated 50–100 lines.

## Final recommendation

Use the difference-coordinate/order route.  It proves exactly the needed cancellation without waiting on a global `Prime (X₀-X₁)` theorem or a UFD instance for multivariate power series.  Package `Prime δ` later only if it becomes independently useful.
