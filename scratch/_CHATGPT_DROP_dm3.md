# Q610 (dm3): coefficient facts for `formalGroupLaw`

## Executive summary

Do **not** try to unfold or compute `Dvd.dvd.choose` directly.  The quotient was chosen only to provide an equation of the form

```lean
δ ^ 3 * W.normalizedAddX = W.formalAddX
δ ^ 3 * W.normalizedAddY = W.formalAddY
```

or the same equations with the multiplication order reversed.  The low coefficients of the quotient are forced by these equations.  Since `δ := X₀ - X₁` has axis terms `X₀^3` and `-X₁^3` in `δ^3`, the axis coefficients of `δ^3 * q` read off the constant and linear axis coefficients of `q` without any cancellation or uniqueness of quotient.

So the clean strategy is:

1. Prove four **raw numerator coefficient facts** for `formalAddY` and `formalAddX`.
2. Prove three generic coefficient lemmas for `δ^3 * q`.
3. Deduce the coefficients of `normalizedAddY` and `normalizedAddX` from `choose_spec`.
4. Use elementary coefficient lemmas for multiplying by a unit with constant coefficient `1` to get the four facts for `formalGroupLaw`.

The universal ring approach is useful only for step 1, namely the raw numerator coefficient computations.  I would not use it to compute the quotient itself unless you also prove uniqueness/functoriality of the quotient.  With arbitrary `Dvd.dvd.choose`, quotient functoriality is exactly the wrong thing to fight.

---

## Notation

Use local notation like this in the coefficient file:

```lean
local notation "X₀" => MvPowerSeries.X (0 : Fin 2)
local notation "X₁" => MvPowerSeries.X (1 : Fin 2)
local notation "δ"  => (X₀ - X₁)

local notation "e₀" n => Finsupp.single (0 : Fin 2) n
local notation "e₁" n => Finsupp.single (1 : Fin 2) n
```

Then the target coefficients are:

```lean
coeff (e₀ 0) W.normalizedAddY = 1
coeff (e₀ 0) W.formalGroupLaw = 0
coeff (e₀ 1) W.formalGroupLaw = 1
coeff (e₁ 1) W.formalGroupLaw = 1
```

Depending on your local API, `constantCoeff f` may already be notation for `coeff 0 f`; if so, prove both statements by `simpa [constantCoeff]` from the `coeff 0` version.

---

## Step 1: prove only raw numerator coefficient facts

The CAS facts you need should be packaged as these Lean lemmas:

```lean
lemma formalAddY_coeff_300 (W : WeierstrassCurve R) :
    coeff (e₀ 3) W.formalAddY = 1 := by
  -- degree-3 part of formalAddY is δ^3
  ...

lemma formalAddX_coeff_300 (W : WeierstrassCurve R) :
    coeff (e₀ 3) W.formalAddX = 0 := by
  -- formalAddX has min total degree 4
  ...

lemma formalAddX_coeff_400 (W : WeierstrassCurve R) :
    coeff (e₀ 4) W.formalAddX = -1 := by
  -- degree-4 part is -δ^3 * (X₀ + X₁)
  ...

lemma formalAddX_coeff_040 (W : WeierstrassCurve R) :
    coeff (e₁ 4) W.formalAddX = 1 := by
  -- degree-4 part is -δ^3 * (X₀ + X₁)
  ...
```

These four facts are enough.  You do **not** need the full degree-3 or degree-4 homogeneous polynomial inside the quotient proof.

Why the signs are right:

```text
δ^3 = X₀^3 - 3 X₀^2X₁ + 3 X₀X₁^2 - X₁^3.

formalAddY degree 3 = δ^3,
so coeff X₀^3 formalAddY = 1.

formalAddX degree 4 = -δ^3 * (X₀ + X₁),
so coeff X₀^4 formalAddX = -1,
and coeff X₁^4 formalAddX = 1.
```

The axis coefficients are deliberately chosen to avoid mixed-term bookkeeping.

---

## Step 2: generic coefficient lemmas for `δ^3 * q`

Prove these once for all `q : MvPowerSeries (Fin 2) R`:

```lean
lemma coeff_e03_delta3_mul (q : MvPowerSeries (Fin 2) R) :
    coeff (e₀ 3) (δ ^ 3 * q) = coeff 0 q := by
  -- only split of e₀ 3 using an axis monomial of δ^3 is e₀ 3 + 0
  ...

lemma coeff_e04_delta3_mul (q : MvPowerSeries (Fin 2) R) :
    coeff (e₀ 4) (δ ^ 3 * q) = coeff (e₀ 1) q := by
  -- only split of e₀ 4 is e₀ 3 + e₀ 1
  ...

lemma coeff_e14_delta3_mul (q : MvPowerSeries (Fin 2) R) :
    coeff (e₁ 4) (δ ^ 3 * q) = - coeff (e₁ 1) q := by
  -- only split of e₁ 4 is e₁ 3 + e₁ 1,
  -- and coeff (e₁ 3) δ^3 = -1
  ...
```

These lemmas are purely coefficient arithmetic.  They should not use any curve data.

A robust way to prove them is by `rw [MvPowerSeries.coeff_mul]` and then `simp` the antidiagonal.  If the antidiagonal simplifier is painful, prove a slightly more general axis lemma:

```lean
lemma coeff_axis0_delta3_mul (q : MvPowerSeries (Fin 2) R) (n : ℕ) :
    coeff (e₀ (3 + n)) (δ ^ 3 * q) = coeff (e₀ n) q := by
  ...

lemma coeff_axis1_delta3_mul (q : MvPowerSeries (Fin 2) R) (n : ℕ) :
    coeff (e₁ (3 + n)) (δ ^ 3 * q) = - coeff (e₁ n) q := by
  ...
```

Then specialize to `n = 0` and `n = 1`.

An alternative is to define an axis restriction homomorphism

```text
MvPowerSeries (Fin 2) R →+* PowerSeries R
X₀ ↦ X,  X₁ ↦ 0
```

and similarly for the `X₁` axis.  Under axis restriction,

```text
δ^3 ↦ X^3          on the X₀-axis,
δ^3 ↦ -X^3         on the X₁-axis.
```

Then the axis coefficient lemmas become one-variable `PowerSeries` coefficient lemmas.  This is conceptually clean, but it requires more API setup.  For only three coefficient facts, direct `coeff_mul` is likely shorter.

---

## Step 3: deduce quotient coefficients from `choose_spec`

Let `qY := W.normalizedAddY` and `qX := W.normalizedAddX`.

You should have equations from the divisibility proofs, something like:

```lean
lemma normalizedAddY_mul_delta3 (W : WeierstrassCurve R) :
    δ ^ 3 * W.normalizedAddY = W.formalAddY := by
  simpa [normalizedAddY] using W.normalizedAddY_dvd.choose_spec

lemma normalizedAddX_mul_delta3 (W : WeierstrassCurve R) :
    δ ^ 3 * W.normalizedAddX = W.formalAddX := by
  simpa [normalizedAddX] using W.normalizedAddX_dvd.choose_spec
```

If the local theorem is oriented as `formalAddY = δ ^ 3 * normalizedAddY`, use `.symm` or rewrite accordingly.  The exact names will differ, but the only thing needed is the multiplication equation.

Then prove:

```lean
lemma normalizedAddY_constantCoeff (W : WeierstrassCurve R) :
    constantCoeff W.normalizedAddY = 1 := by
  -- Better prove coeff 0 first.
  have hmul : δ ^ 3 * W.normalizedAddY = W.formalAddY :=
    normalizedAddY_mul_delta3 W
  have hcoeff := congrArg (fun f => coeff (e₀ 3) f) hmul
  -- left side becomes coeff 0 normalizedAddY
  rw [coeff_e03_delta3_mul] at hcoeff
  -- right side is formalAddY_coeff_300
  rw [formalAddY_coeff_300] at hcoeff
  simpa [constantCoeff] using hcoeff
```

Similarly, add these normalized `X` lemmas:

```lean
lemma normalizedAddX_constantCoeff (W : WeierstrassCurve R) :
    constantCoeff W.normalizedAddX = 0 := by
  have hmul : δ ^ 3 * W.normalizedAddX = W.formalAddX :=
    normalizedAddX_mul_delta3 W
  have hcoeff := congrArg (fun f => coeff (e₀ 3) f) hmul
  rw [coeff_e03_delta3_mul] at hcoeff
  rw [formalAddX_coeff_300] at hcoeff
  simpa [constantCoeff] using hcoeff

lemma normalizedAddX_lin_coeff_X (W : WeierstrassCurve R) :
    coeff (e₀ 1) W.normalizedAddX = -1 := by
  have hmul : δ ^ 3 * W.normalizedAddX = W.formalAddX :=
    normalizedAddX_mul_delta3 W
  have hcoeff := congrArg (fun f => coeff (e₀ 4) f) hmul
  rw [coeff_e04_delta3_mul] at hcoeff
  rw [formalAddX_coeff_400] at hcoeff
  simpa using hcoeff

lemma normalizedAddX_lin_coeff_Y (W : WeierstrassCurve R) :
    coeff (e₁ 1) W.normalizedAddX = -1 := by
  have hmul : δ ^ 3 * W.normalizedAddX = W.formalAddX :=
    normalizedAddX_mul_delta3 W
  have hcoeff := congrArg (fun f => coeff (e₁ 4) f) hmul
  rw [coeff_e14_delta3_mul] at hcoeff
  rw [formalAddX_coeff_040] at hcoeff
  -- hcoeff : - coeff (e₁ 1) normalizedAddX = 1
  -- hence coeff = -1
  linarith
```

If `linarith` does not like the semiring/ring context, replace the last line by a ring manipulation:

```lean
  have h := congrArg Neg.neg hcoeff
  -- h : -(-coeff ...) = -1
  simpa using h
```

or simply:

```lean
  rw [← neg_eq_iff_eq_neg] at hcoeff
  simpa using hcoeff
```

The key point is that the `X₁`-axis lemma has the minus sign.

---

## Step 4: constant coefficient of the inverse unit

From `normalizedAddY_constantCoeff`, prove:

```lean
lemma normalizedAddY_unit_inv_constantCoeff (W : WeierstrassCurve R) :
    constantCoeff (↑(W.normalizedAddY_isUnit.unit⁻¹) : MvPowerSeries (Fin 2) R) = 1 := by
  let u := W.normalizedAddY_isUnit.unit
  have hccu : constantCoeff (↑u : MvPowerSeries (Fin 2) R) = 1 := by
    simpa [u] using W.normalizedAddY_constantCoeff
  have hmul : constantCoeff ((↑u : MvPowerSeries (Fin 2) R) * ↑(u⁻¹)) = 1 := by
    simpa using congrArg constantCoeff (Units.mul_inv u)
  rw [constantCoeff_mul, hccu, one_mul] at hmul
  simpa [u] using hmul
```

If there is already a lemma like

```lean
map_units_inv
constantCoeff_unit_inv
```

use it.  But the above proof is stable: apply the ring hom `constantCoeff` to `u * u⁻¹ = 1`.

---

## Step 5: generic linear coefficient lemma for multiplication by a series with constant coefficient `1`

Prove this reusable lemma:

```lean
lemma coeff_single_one_mul_of_left_constantCoeff_zero
    (f g : MvPowerSeries (Fin 2) R) (i : Fin 2)
    (hf0 : constantCoeff f = 0)
    (hg0 : constantCoeff g = 1) :
    coeff (Finsupp.single i 1) (f * g) = coeff (Finsupp.single i 1) f := by
  -- coefficient of f*g at X_i is
  --   coeff X_i f * coeff 0 g + coeff 0 f * coeff X_i g
  -- and coeff 0 f = 0, coeff 0 g = 1.
  rw [MvPowerSeries.coeff_mul]
  -- simplify the antidiagonal of `single i 1`:
  -- only `(single i 1, 0)` and `(0, single i 1)` occur.
  simp [constantCoeff, hf0, hg0]
```

Depending on orientation of the antidiagonal, the final expression may be

```lean
coeff (single i 1) f * coeff 0 g + coeff 0 f * coeff (single i 1) g
```

or the two terms reversed.  Either way `ring_nf [hf0, hg0]` should finish once the antidiagonal is simplified.

Also prove the constant coefficient product lemma if the API does not already have it:

```lean
lemma constantCoeff_mul' (f g : MvPowerSeries (Fin 2) R) :
    constantCoeff (f * g) = constantCoeff f * constantCoeff g := by
  simpa [constantCoeff] using MvPowerSeries.coeff_zero_mul f g
```

The exact existing name is likely already available because `constantCoeff` is usually a ring hom.

---

## Step 6: prove the four requested facts

### 1. `normalizedAddY_constantCoeff`

As above, prove it from the `X₀^3` coefficient of

```lean
δ ^ 3 * W.normalizedAddY = W.formalAddY.
```

This avoids unfolding `Dvd.dvd.choose`.

### 2. `formalGroupLaw_constantCoeff`

Use

```lean
formalGroupLaw = -W.normalizedAddX * ↑(W.normalizedAddY_isUnit.unit⁻¹)
```

and the facts:

```lean
constantCoeff W.normalizedAddX = 0
constantCoeff ↑(W.normalizedAddY_isUnit.unit⁻¹) = 1.
```

Skeleton:

```lean
lemma formalGroupLaw_constantCoeff (W : WeierstrassCurve R) :
    constantCoeff W.formalGroupLaw = 0 := by
  have hx0 : constantCoeff W.normalizedAddX = 0 :=
    normalizedAddX_constantCoeff W
  have hyinv0 :
      constantCoeff (↑(W.normalizedAddY_isUnit.unit⁻¹) : MvPowerSeries (Fin 2) R) = 1 :=
    normalizedAddY_unit_inv_constantCoeff W
  simp [formalGroupLaw, constantCoeff_mul, hx0, hyinv0]
```

If `simp` leaves `-(0 * 1)`, finish by `ring`.

### 3. `formalGroupLaw_lin_coeff_X`

Let

```lean
h := (↑(W.normalizedAddY_isUnit.unit⁻¹) : MvPowerSeries (Fin 2) R)
```

Then:

```lean
coeff (e₀ 1) (W.normalizedAddX * h)
  = coeff (e₀ 1) W.normalizedAddX
  = -1.
```

Since `formalGroupLaw` has a leading minus sign, the result is `1`.

Skeleton:

```lean
lemma formalGroupLaw_lin_coeff_X (W : WeierstrassCurve R) :
    coeff (e₀ 1) W.formalGroupLaw = 1 := by
  let h : MvPowerSeries (Fin 2) R := ↑(W.normalizedAddY_isUnit.unit⁻¹)
  have hx0 : constantCoeff W.normalizedAddX = 0 :=
    normalizedAddX_constantCoeff W
  have hh0 : constantCoeff h = 1 := by
    simpa [h] using normalizedAddY_unit_inv_constantCoeff W
  have hlinmul :
      coeff (e₀ 1) (W.normalizedAddX * h)
        = coeff (e₀ 1) W.normalizedAddX :=
    coeff_single_one_mul_of_left_constantCoeff_zero
      W.normalizedAddX h (0 : Fin 2) hx0 hh0
  have hxlin : coeff (e₀ 1) W.normalizedAddX = -1 :=
    normalizedAddX_lin_coeff_X W
  simp [formalGroupLaw, h, hlinmul, hxlin]
```

If the definition parses as `-(W.normalizedAddX * h)` rather than `-W.normalizedAddX * h`, normalize it explicitly:

```lean
simp [formalGroupLaw, h, neg_mul, hlinmul, hxlin]
```

### 4. `formalGroupLaw_lin_coeff_Y`

Same proof with `(1 : Fin 2)`:

```lean
lemma formalGroupLaw_lin_coeff_Y (W : WeierstrassCurve R) :
    coeff (e₁ 1) W.formalGroupLaw = 1 := by
  let h : MvPowerSeries (Fin 2) R := ↑(W.normalizedAddY_isUnit.unit⁻¹)
  have hx0 : constantCoeff W.normalizedAddX = 0 :=
    normalizedAddX_constantCoeff W
  have hh0 : constantCoeff h = 1 := by
    simpa [h] using normalizedAddY_unit_inv_constantCoeff W
  have hlinmul :
      coeff (e₁ 1) (W.normalizedAddX * h)
        = coeff (e₁ 1) W.normalizedAddX :=
    coeff_single_one_mul_of_left_constantCoeff_zero
      W.normalizedAddX h (1 : Fin 2) hx0 hh0
  have hxlin : coeff (e₁ 1) W.normalizedAddX = -1 :=
    normalizedAddX_lin_coeff_Y W
  simp [formalGroupLaw, h, hlinmul, hxlin]
```

---

## Should you use the universal ring?

Yes, but only in a controlled way.

The safe universal-ring workflow is:

1. Let

```lean
A := MvPolynomial (Fin 5) ℤ
```

or whatever index set you use for `a₁ a₂ a₃ a₄ a₆`.

2. Define the universal curve `Wuniv : WeierstrassCurve A`.
3. Prove the raw numerator coefficient facts for `Wuniv` by finite expansion/truncation:

```lean
coeff (e₀ 3) Wuniv.formalAddY = 1
coeff (e₀ 3) Wuniv.formalAddX = 0
coeff (e₀ 4) Wuniv.formalAddX = -1
coeff (e₁ 4) Wuniv.formalAddX = 1
```

4. Specialize these facts to any `R` and any `W : WeierstrassCurve R` by the coefficient-commutation lemma for `MvPowerSeries.map`.

But I would **not** define or compute

```lean
Wuniv.normalizedAddY
```

and then try to map it to

```lean
W.normalizedAddY.
```

The reason is that `normalizedAddY` is a `Dvd.dvd.choose`.  Unless you define the quotient canonically or prove quotient uniqueness by regularity of `δ^3`, there is no reason Lean should know that specialization commutes with this arbitrary choice.

The good news is that you do not need that.  Once the raw numerator coefficient facts are known after specialization, the quotient coefficients follow from

```lean
δ ^ 3 * q = numerator
```

inside the target ring `R`.

So the universal ring is best used as a **certificate generator for the raw low jet**, not as the home of the quotient proof.

---

## Even cleaner: make a low-jet certificate theorem

If direct expansion of `formalAddX`/`formalAddY` is annoying, package the CAS result as one theorem about a projection to total degree `≤ 4`.

For example, define a finite truncation map or just state a theorem saying:

```lean
theorem formalAdd_lowJet (W : WeierstrassCurve R) :
  lowJet4 W.formalAddY = lowJet4 (δ ^ 3) ∧
  lowJet4 W.formalAddX = lowJet4 (-(δ ^ 3) * (X₀ + X₁)) := by
  ...
```

Then derive the four raw coefficient facts by applying `coeff` to the relevant axis monomials.

This is more maintainable than scattering four separate `ring_nf` computations through the formal group proof file.  It also documents the mathematics:

```text
formalAddY starts as δ^3,
formalAddX starts as -δ^3(X₀+X₁).
```

---

## Recommended file structure

I would split the proof into three layers:

### Layer A: pure `MvPowerSeries` coefficient lemmas

No curve data.

```lean
coeff_e03_delta3_mul
coeff_e04_delta3_mul
coeff_e14_delta3_mul
coeff_single_one_mul_of_left_constantCoeff_zero
```

### Layer B: raw addition low-jet lemmas

Curve-specific, but no quotients.

```lean
formalAddY_coeff_300
formalAddX_coeff_300
formalAddX_coeff_400
formalAddX_coeff_040
```

These can be direct proofs or universal-ring-specialized proofs.

### Layer C: normalized quotient and formal group law coefficients

Uses `choose_spec`, not `choose` unfolding.

```lean
normalizedAddY_constantCoeff
normalizedAddX_constantCoeff
normalizedAddX_lin_coeff_X
normalizedAddX_lin_coeff_Y
normalizedAddY_unit_inv_constantCoeff
formalGroupLaw_constantCoeff
formalGroupLaw_lin_coeff_X
formalGroupLaw_lin_coeff_Y
```

This makes the final formal group law proof small and insensitive to the messy projective addition formulas.

---

## Main answer to the `Dvd.dvd.choose` concern

For `normalizedAddY_constantCoeff`, do this:

```text
Do not compute `constantCoeff (Dvd.dvd.choose h)`.
Instead apply `coeff X₀^3` to the equation
  δ^3 * Dvd.dvd.choose h = formalAddY.
The left side is exactly `constantCoeff (Dvd.dvd.choose h)`.
The right side is the CAS-certified coefficient `1`.
```

This avoids quotient uniqueness, avoids cancellation by `δ^3`, and works even over rings with zero divisors.

The same trick gives the linear coefficients of `normalizedAddX` using the `X₀^4` and `X₁^4` coefficients.  Then the inverse unit contributes only its constant coefficient `1`, so the formal group law linear coefficients are immediate.
