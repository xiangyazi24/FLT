# Q658 (dm2): low-degree coefficients of `formalGroupLaw`

## Executive answer

Let

```lean
A := normalizedAddX W
B := (↑((normalizedAddY_isUnit W).unit⁻¹) : MvPowerSeries (Fin 2) R)
```

so that

```lean
formalGroupLaw W = -A * B
```

The clean route is to prove one small product-coefficient helper:

```lean
coeff (Finsupp.single i 1) (A * B)
  = coeff (Finsupp.single i 1) A * coeff 0 B
```

under the hypothesis `coeff 0 A = 0`.  This helper is exactly the “only surviving antidiagonal pair is `(single i 1, 0)`” fact.  Then apply it to the left factor `-normalizedAddX W`, not to `normalizedAddX W` itself.  That way the sign is absorbed automatically:

```lean
coeff e (-A * B) = coeff e (-A) * coeff 0 B
                 = - coeff e A * 1
                 = -(-1) * 1
                 = 1
```

For the constant term, use multiplicativity of `constantCoeff`/`coeff 0`:

```lean
coeff 0 (-A * B) = coeff 0 (-A) * coeff 0 B = 0 * 1 = 0
```

Below I write everything with `MvPowerSeries.coeff 0` as the constant coefficient.  If your local file has a notation/definition `constantCoeff`, replace `MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ)` by that notation.

---

## Imports and local notation

```lean
import Mathlib

open scoped BigOperators
open MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

local abbrev Mv2 (R : Type*) [CommRing R] := MvPowerSeries (Fin 2) R

local notation "c₀" P =>
  MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) P

local notation "cX" P =>
  MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) P

local notation "cY" P =>
  MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) P
```

---

## Helper 1: constant coefficient of the inverse unit is `1`

You have already proved:

```lean
normalizedAddY_constantCoeff : c₀ (normalizedAddY W) = 1
normalizedAddY_isUnit       : IsUnit (normalizedAddY W)
```

The inverse unit used in `formalGroupLaw` also has constant coefficient `1`.

```lean
private lemma normalizedAddY_unit_inv_constantCoeff
    (W : WeierstrassCurve R) :
    c₀ (↑((normalizedAddY_isUnit W).unit⁻¹) : MvPowerSeries (Fin 2) R) = 1 := by
  classical
  let U := (normalizedAddY_isUnit W).unit
  let B : MvPowerSeries (Fin 2) R := ↑(U⁻¹)

  have hU : (↑U : MvPowerSeries (Fin 2) R) = normalizedAddY W := by
    exact (normalizedAddY_isUnit W).unit_spec

  -- `normalizedAddY W * B = 1`, because `B` is the inverse of the unit witnessing
  -- that `normalizedAddY W` is a unit.
  have hmul : normalizedAddY W * B = 1 := by
    dsimp [B]
    rw [← hU]
    simp

  -- Take coefficient `0`.  For `0`, the product coefficient is just the product of
  -- constant coefficients.  In many files this is just `simp` via `map_mul` for
  -- `constantCoeff`; otherwise use `MvPowerSeries.coeff_mul` and the fact that the
  -- antidiagonal of `0` only contains `(0, 0)`.
  have hcoeff := congrArg (fun P : MvPowerSeries (Fin 2) R => c₀ P) hmul

  -- Usually one of these two lines works, depending on your local simp set/API:
  --   simpa [B, hU, normalizedAddY_constantCoeff W] using hcoeff
  -- or:
  --   simpa [B, MvPowerSeries.coeff_mul, normalizedAddY_constantCoeff W] using hcoeff
  simpa [B, MvPowerSeries.coeff_mul, normalizedAddY_constantCoeff W] using hcoeff
```

If your local `constantCoeff` is packaged as a ring hom, the same proof can be even shorter:

```lean
private lemma normalizedAddY_unit_inv_constantCoeff'
    (W : WeierstrassCurve R) :
    c₀ (↑((normalizedAddY_isUnit W).unit⁻¹) : MvPowerSeries (Fin 2) R) = 1 := by
  classical
  -- Replace `c₀` below by the ring-hom form of your `constantCoeff`, if you have it.
  -- The idea is just: ring homs send unit inverses to unit inverses, and `1⁻¹ = 1`.
  simpa [normalizedAddY_constantCoeff W]
    using normalizedAddY_unit_inv_constantCoeff (R := R) W
```

---

## Helper 2: linear coefficient of a product when the left constant term is zero

This is the important helper for (b) and (c).  The theorem is useful in exactly this form, because it can be applied to `A := -normalizedAddX W`.

```lean
private lemma coeff_single_one_mul_of_left_constCoeff_zero
    {A B : MvPowerSeries (Fin 2) R} (i : Fin 2)
    (hA0 : c₀ A = 0) :
    MvPowerSeries.coeff (Finsupp.single i 1) (A * B)
      = MvPowerSeries.coeff (Finsupp.single i 1) A * c₀ B := by
  classical
  let e : Fin 2 →₀ ℕ := Finsupp.single i 1

  rw [MvPowerSeries.coeff_mul]

  -- The goal is now a finite sum over `e.antidiagonal`:
  --   ∑ p in e.antidiagonal, coeff p.1 A * coeff p.2 B
  -- For `e = single i 1`, the only possible pairs are `(e, 0)` and `(0, e)`.
  -- The `(0, e)` term dies because `coeff 0 A = 0`.

  refine Finset.sum_eq_single (e, 0) ?main ?other ?not_mem
  · -- Main surviving term: `(e, 0)`.
    simp [e]

  · -- Every other antidiagonal pair has left component `0`, hence the summand is zero.
    intro p hp hp_ne

    have hp_sum : p.1 + p.2 = e := by
      -- Depending on the exact antidiagonal API, this may be one of:
      --   simpa [e] using (Finsupp.mem_antidiagonal.mp hp)
      --   simpa [e] using hp
      simpa [e] using (Finsupp.mem_antidiagonal.mp hp)

    have hp_left_zero : p.1 = 0 := by
      -- Pointwise proof.  At coordinates `j ≠ i`, the sum is `0`, so both sides are `0`.
      -- At coordinate `i`, the equation is `p.1 i + p.2 i = 1`.
      -- If `p.1 i = 1`, then `p = (e, 0)`, contradicting `hp_ne`.
      -- Therefore `p.1 i = 0` too.
      ext j
      by_cases hji : j = i
      · subst hji
        have hcoord : p.1 i + p.2 i = 1 := by
          simpa [e] using congrArg (fun f : Fin 2 →₀ ℕ => f i) hp_sum
        have hp1_le : p.1 i ≤ 1 := by omega
        by_contra hp1_ne_zero
        have hp1_eq_one : p.1 i = 1 := by omega
        have hp2_eq_zero : p.2 i = 0 := by omega
        have hp_left_eq_e : p.1 = e := by
          ext j
          by_cases hji : j = i
          · subst hji
            simp [e, hp1_eq_one]
          · have hcoordj : p.1 j + p.2 j = 0 := by
              simpa [e, hji] using congrArg (fun f : Fin 2 →₀ ℕ => f j) hp_sum
            have : p.1 j = 0 := by omega
            simp [e, hji, this]
        have hp_right_eq_zero : p.2 = 0 := by
          ext j
          by_cases hji : j = i
          · subst hji
            simp [hp2_eq_zero]
          · have hcoordj : p.1 j + p.2 j = 0 := by
              simpa [e, hji] using congrArg (fun f : Fin 2 →₀ ℕ => f j) hp_sum
            have : p.2 j = 0 := by omega
            simp [this]
        exact hp_ne (by cases p; simp [hp_left_eq_e, hp_right_eq_zero])
      · have hcoord : p.1 j + p.2 j = 0 := by
          simpa [e, hji] using congrArg (fun f : Fin 2 →₀ ℕ => f j) hp_sum
        omega

    simp [hp_left_zero, hA0]

  · -- `(e, 0)` really is in `e.antidiagonal`.
    intro hnot
    exact hnot (by simp [e, Finsupp.mem_antidiagonal])
```

Notes about the helper:

* The exact membership lemma may be named slightly differently at your Mathlib pin.  Search for `mem_antidiagonal` near `Finsupp.antidiagonal` if `Finsupp.mem_antidiagonal.mp hp` does not elaborate.
* If your simp set knows the antidiagonal of a single-degree finsupp, this helper compresses to essentially:

```lean
  rw [MvPowerSeries.coeff_mul]
  simp [Finsupp.antidiagonal_single, hA0]
```

but the `sum_eq_single` version above is the stable tactic structure.

---

## Assumed `normalizedAddX` low-degree facts

For the final three theorems, you need these facts about `normalizedAddX`:

```lean
-- You said the constant term is known from the minimum-degree argument.
theorem normalizedAddX_constantCoeff (W : WeierstrassCurve R) :
    c₀ (normalizedAddX W) = 0 := by
  -- from addX min degree 4 / normalizedAddX min degree 1
  sorry

-- CAS/coefficient extraction facts you said are `-1`.
theorem normalizedAddX_lin_coeff_X (W : WeierstrassCurve R) :
    cX (normalizedAddX W) = -1 := by
  -- coefficient extraction from the definition of `normalizedAddX`
  sorry

theorem normalizedAddX_lin_coeff_Y (W : WeierstrassCurve R) :
    cY (normalizedAddX W) = -1 := by
  -- coefficient extraction from the definition of `normalizedAddX`
  sorry
```

Once those exist, the three `formalGroupLaw` lemmas are short.

---

## (a) `formalGroupLaw_constantCoeff = 0`

```lean
theorem formalGroupLaw_constantCoeff
    (W : WeierstrassCurve R) :
    c₀ (formalGroupLaw W) = 0 := by
  classical
  let A : MvPowerSeries (Fin 2) R := normalizedAddX W
  let B : MvPowerSeries (Fin 2) R :=
    (↑((normalizedAddY_isUnit W).unit⁻¹) : MvPowerSeries (Fin 2) R)

  have hA0 : c₀ A = 0 := by
    simpa [A] using normalizedAddX_constantCoeff (R := R) W

  have hB0 : c₀ B = 1 := by
    simpa [B] using normalizedAddY_unit_inv_constantCoeff (R := R) W

  -- If `formalGroupLaw` is definitionally `-normalizedAddX * ↑unit⁻¹`, this `change`
  -- makes the target easy.  If not, replace it by `simp [formalGroupLaw, A, B]`.
  change c₀ ((-A) * B) = 0

  -- For coefficient `0`, use multiplicativity of constant coefficient.  Either `simp`
  -- knows it, or `MvPowerSeries.coeff_mul` reduces to the singleton antidiagonal of `0`.
  -- Try the short line first:
  --   simpa [hA0, hB0] using congrArg ...
  rw [MvPowerSeries.coeff_mul]
  simp [hA0, hB0]
```

In many Mathlib contexts the last three lines can be replaced by:

```lean
  simp [MvPowerSeries.coeff_mul, hA0, hB0]
```

or, if your `constantCoeff` is a ring hom:

```lean
  simp [map_mul, hA0, hB0]
```

---

## (b) coefficient at `single 0 1` is `1`

```lean
theorem formalGroupLaw_lin_coeff_X
    (W : WeierstrassCurve R) :
    cX (formalGroupLaw W) = 1 := by
  classical
  let A : MvPowerSeries (Fin 2) R := normalizedAddX W
  let B : MvPowerSeries (Fin 2) R :=
    (↑((normalizedAddY_isUnit W).unit⁻¹) : MvPowerSeries (Fin 2) R)

  have hA0 : c₀ A = 0 := by
    simpa [A] using normalizedAddX_constantCoeff (R := R) W

  have hnegA0 : c₀ (-A) = 0 := by
    simpa [hA0]

  have hAX : cX A = -1 := by
    simpa [A] using normalizedAddX_lin_coeff_X (R := R) W

  have hB0 : c₀ B = 1 := by
    simpa [B] using normalizedAddY_unit_inv_constantCoeff (R := R) W

  change cX ((-A) * B) = 1

  rw [coeff_single_one_mul_of_left_constCoeff_zero
    (R := R) (A := -A) (B := B) (i := (0 : Fin 2)) hnegA0]

  -- Now the goal is `cX (-A) * c₀ B = 1`.
  -- `cX (-A) = - cX A = -(-1) = 1`, and `c₀ B = 1`.
  simp [hAX, hB0]
```

The important trick is applying the product helper to `A := -normalizedAddX W`.  If you apply it to `normalizedAddX W`, you then need an extra rewrite moving the outer negation across multiplication/coefficient extraction.

---

## (c) coefficient at `single 1 1` is `1`

This is identical to (b), with index `(1 : Fin 2)`.

```lean
theorem formalGroupLaw_lin_coeff_Y
    (W : WeierstrassCurve R) :
    cY (formalGroupLaw W) = 1 := by
  classical
  let A : MvPowerSeries (Fin 2) R := normalizedAddX W
  let B : MvPowerSeries (Fin 2) R :=
    (↑((normalizedAddY_isUnit W).unit⁻¹) : MvPowerSeries (Fin 2) R)

  have hA0 : c₀ A = 0 := by
    simpa [A] using normalizedAddX_constantCoeff (R := R) W

  have hnegA0 : c₀ (-A) = 0 := by
    simpa [hA0]

  have hAY : cY A = -1 := by
    simpa [A] using normalizedAddX_lin_coeff_Y (R := R) W

  have hB0 : c₀ B = 1 := by
    simpa [B] using normalizedAddY_unit_inv_constantCoeff (R := R) W

  change cY ((-A) * B) = 1

  rw [coeff_single_one_mul_of_left_constCoeff_zero
    (R := R) (A := -A) (B := B) (i := (1 : Fin 2)) hnegA0]

  simp [hAY, hB0]
```

---

## If `change` does not see the definition of `formalGroupLaw`

Use a local rewrite instead:

```lean
  simp only [formalGroupLaw]
  -- or
  dsimp [formalGroupLaw]
```

Then introduce `A` and `B` after the definitional unfolding:

```lean
  change MvPowerSeries.coeff e
      ((-(normalizedAddX W)) *
        (↑((normalizedAddY_isUnit W).unit⁻¹) : MvPowerSeries (Fin 2) R)) = 1
```

For the linear proofs, the robust final block is always:

```lean
  rw [coeff_single_one_mul_of_left_constCoeff_zero
    (A := -(normalizedAddX W))
    (B := (↑((normalizedAddY_isUnit W).unit⁻¹) : MvPowerSeries (Fin 2) R))
    (i := targetIndex)
    (by simpa using congrArg Neg.neg (normalizedAddX_constantCoeff W))]
  simp [normalizedAddX_lin_coeff_X, normalizedAddY_unit_inv_constantCoeff]
```

where `targetIndex` is `(0 : Fin 2)` for `X` and `(1 : Fin 2)` for `Y`.

---

## Bottom line

Prove the product helper once from `MvPowerSeries.coeff_mul`.  Then the three target theorems reduce to:

```lean
-- (a)
simp [formalGroupLaw, MvPowerSeries.coeff_mul,
  normalizedAddX_constantCoeff,
  normalizedAddY_unit_inv_constantCoeff]

-- (b)
rw [coeff_single_one_mul_of_left_constCoeff_zero (A := -(normalizedAddX W)) (i := 0)]
simp [normalizedAddX_constantCoeff,
  normalizedAddX_lin_coeff_X,
  normalizedAddY_unit_inv_constantCoeff]

-- (c)
rw [coeff_single_one_mul_of_left_constCoeff_zero (A := -(normalizedAddX W)) (i := 1)]
simp [normalizedAddX_constantCoeff,
  normalizedAddX_lin_coeff_Y,
  normalizedAddY_unit_inv_constantCoeff]
```

That is the cleanest way to avoid manually expanding the inverse unit or proving anything about higher-degree terms of `B`.

end WeierstrassCurve
```