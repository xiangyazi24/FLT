# Q478 (dm3): order-3 diagonal vanishing for `addXYZ(P(t₀),P(t₁))`

## Short answer

`addXYZ_self` alone gives only

```text
(t₀ - t₁) ∣ formalAddX,
(t₀ - t₁) ∣ formalAddY,
(t₀ - t₁) ∣ formalAddZ.
```

It does **not** imply order `3`.  A function such as `t₀ - t₁` already vanishes on the diagonal but is not divisible by `(t₀ - t₁)^2`, let alone `(t₀ - t₁)^3`.

The order-3 result must come from the **specific shape of Mathlib's projective addition formula**, not from the self-addition lemma by itself.

The right Lean theorem is therefore not merely a diagonal-vanishing theorem:

```lean
theorem formalAddY_diag : diagEval formalAddY = 0
```

but a stronger explicit divisibility theorem:

```lean
theorem formalAddY_diag_order3 :
    ∃ Q : MvPowerSeries (Fin 2) K,
      formalAddY = (T₀ - T₁)^3 * Q
```

or with the sign convention reversed:

```lean
theorem formalAddY_diag_order3 :
    ∃ Q : MvPowerSeries (Fin 2) K,
      formalAddY = (T₁ - T₀)^3 * Q
```

The sign is irrelevant for normalization, since replacing `δ` by `-δ` only changes the quotient by `-1` in odd powers.

---

## Recommended proof: factor through the chord variables `U,V`

The cleanest proof is route (1): show every term of the raw projective addition coordinate contains **three factors** from the diagonal ideal.

For the usual projective chord formula, the auxiliary chord variables have the schematic form

```text
U = Y₂ Z₁ - Y₁ Z₂       -- or the corresponding generalized-Weierstrass variant
V = X₂ Z₁ - X₁ Z₂
```

up to Mathlib's exact naming/sign convention.  On the diagonal `P = Q`, both `U` and `V` vanish.  More importantly, after substituting

```text
P(t) = [t : -1 : w(t)],
```

both substituted variables are divisible by

```text
δ = t₀ - t₁.
```

That is, prove lemmas of the form

```lean
theorem formalU_diag_factor :
    ∃ U₁ : MvPowerSeries (Fin 2) K, formalU = δ * U₁ := by ...

theorem formalV_diag_factor :
    ∃ V₁ : MvPowerSeries (Fin 2) K, formalV = δ * V₁ := by ...
```

Then inspect Mathlib's `addY` formula.  The key structural fact should be:

```text
addY is a polynomial in U,V and the input coordinates,
and every monomial has total U/V-degree at least 3.
```

Schematically, terms look like

```text
U^3 * A + U^2*V * B + U*V^2 * C + V^3 * D
```

where `A,B,C,D` are polynomials in the projective coordinates and curve coefficients.  Therefore, after substituting `U = δ U₁` and `V = δ V₁`, every term contains `δ^3`.

The Lean proof should have this shape:

```lean
noncomputable section

namespace FormalGroupW

variable {K : Type*} [CommRing K]
variable (W : WeierstrassCurve K)

abbrev FG2 := MvPowerSeries (Fin 2) K

-- sign convention can be swapped
def T₀ : FG2 K := MvPowerSeries.X 0
def T₁ : FG2 K := MvPowerSeries.X 1
def δ : FG2 K := T₀ - T₁

-- already existing or easy wrappers around the addXYZ auxiliaries after P(t)-substitution
noncomputable def formalU : FG2 K := ...
noncomputable def formalV : FG2 K := ...
noncomputable def formalAddY : FG2 K := ...

lemma formalU_diag_factor :
    ∃ U₁ : FG2 K, formalU W = δ * U₁ := by
  -- either unfold U and use `f(T₀)-f(T₁)` divisibility,
  -- or use the generic diagonal-division lemma from Q461.
  sorry

lemma formalV_diag_factor :
    ∃ V₁ : FG2 K, formalV W = δ * V₁ := by
  -- same style.
  sorry

lemma formalAddY_cubic_in_UV
    {U₁ V₁ : FG2 K}
    (hU : formalU W = δ * U₁)
    (hV : formalV W = δ * V₁) :
    ∃ Q : FG2 K, formalAddY W = δ^3 * Q := by
  -- unfold `formalAddY`, `Projective.addY`, and the auxiliary definitions.
  -- Rewrite `formalU` and `formalV` using hU/hV.
  -- Then `ring`/`ring_nf` factors δ^3.
  -- The quotient Q need not be named manually at first; use `refine ⟨_, ?_⟩`.
  sorry

theorem formalAddY_diag_order3 :
    ∃ Q : FG2 K, formalAddY W = δ^3 * Q := by
  rcases formalU_diag_factor (W := W) with ⟨U₁, hU⟩
  rcases formalV_diag_factor (W := W) with ⟨V₁, hV⟩
  exact formalAddY_cubic_in_UV (W := W) hU hV

end FormalGroupW
```

This is better than a derivative/Taylor proof because it actually constructs the quotient `Q`, works in all characteristics, and explains why the order is `3` rather than `1`.

---

## Why this is stronger than `addXYZ_self`

`addXYZ_self` proves that the raw formula lands in the diagonal ideal `I_Δ`:

```text
addX, addY, addZ ∈ I_Δ.
```

But the needed theorem is:

```text
addY ∈ I_Δ^3.
```

The implication

```text
addY ∈ I_Δ  ⇒  addY ∈ I_Δ^3
```

is false.  The missing information is exactly that Mathlib's `addY` is cubic in the chord variables `U,V`, and each of `U,V` is already in `I_Δ`.

Conceptually:

```text
U,V ∈ I_Δ
addY ∈ (U,V)^3
----------------
addY ∈ I_Δ^3
```

After pulling back along the one-parameter formal point `P(t)`, the diagonal ideal becomes the principal ideal `(t₀ - t₁)`, hence

```text
formalAddY ∈ (t₀ - t₁)^3.
```

This is the algebraic reason for order `3`.

---

## How to prove `formalU` and `formalV` are divisible by `δ`

There are two practical options.

### Option A: use the generic diagonal-divisibility lemma

From Q461, isolate a lemma:

```lean
noncomputable def diagEval : FG2 K →+* PowerSeries K := ...

theorem diagonalSub_dvd_of_diagEval_eq_zero
    (f : FG2 K) (hf : diagEval f = 0) :
    ∃ q : FG2 K, f = δ * q := by
  ...
```

Then prove

```lean
lemma formalU_diagEval : diagEval (formalU W) = 0 := by
  simp [formalU, formalP]

lemma formalV_diagEval : diagEval (formalV W) = 0 := by
  simp [formalV, formalP]
```

and apply the generic lemma.

This is robust, but it hides the quotient.

### Option B: explicit `f(T₀)-f(T₁)` quotient

If `formalU` and `formalV` unfold to combinations like

```text
w(T₀) - w(T₁),
T₀*w(T₁) - T₁*w(T₀),
```

then prove direct lemmas:

```lean
theorem subst_sub_subst_dvd
    (f : PowerSeries K) :
    ∃ q : FG2 K,
      substT₀ f - substT₁ f = (T₀ - T₁) * q := by
  -- coefficient formula:
  -- f = Σ aₙ Tⁿ
  -- T₀ⁿ - T₁ⁿ = (T₀ - T₁) * Σ_{i=0}^{n-1} T₀^{n-1-i} T₁^i
  sorry
```

This is often better for later coefficient calculations, but it costs more lines up front.

For the immediate order-3 theorem, Option A is likely enough.

---

## Taylor/finite-jet route

Route (2) also works, but formulate it as a finite-jet statement, not as analytic derivatives.

Define a change of variables

```text
σ : K⟦t₀,t₁⟧ → K⟦s,h⟧
σ(t₀) = s + h,
σ(t₁) = s.
```

Then

```text
σ(t₀ - t₁) = h.
```

So

```text
(t₀ - t₁)^3 ∣ f
```

is equivalent to

```text
h^3 ∣ σ(f).
```

Equivalently, the first three coefficients in the `h` direction vanish:

```text
[h^0] σ(f) = 0,
[h^1] σ(f) = 0,
[h^2] σ(f) = 0.
```

This gives a Lean predicate:

```lean
noncomputable def diffSubst : FG2 K →+* FG2 K :=
  -- old t₀ ↦ s + h, old t₁ ↦ s
  -- e.g. variables new 0=s, new 1=h
  sorry

noncomputable def hCoeff (n : ℕ) (f : FG2 K) : PowerSeries K :=
  -- coefficient of h^n in diffSubst f, as a power series in s
  sorry

def vanishesToOrderAtLeast3OnDiagonal (f : FG2 K) : Prop :=
  hCoeff 0 f = 0 ∧ hCoeff 1 f = 0 ∧ hCoeff 2 f = 0
```

Then prove a generic theorem:

```lean
theorem diagPow3_dvd_of_hCoeff012_eq_zero
    {f : FG2 K}
    (h0 : hCoeff 0 f = 0)
    (h1 : hCoeff 1 f = 0)
    (h2 : hCoeff 2 f = 0) :
    ∃ q : FG2 K, f = δ^3 * q := by
  -- use that diffSubst is an automorphism and that h^3 divides a power series
  -- iff coefficients of h^0,h^1,h^2 vanish.
  sorry
```

For `formalAddY`, the proof would be:

```lean
theorem formalAddY_hCoeff0 : hCoeff 0 (formalAddY W) = 0 := by
  -- this is essentially addXYZ_self
  sorry

theorem formalAddY_hCoeff1 : hCoeff 1 (formalAddY W) = 0 := by
  -- must unfold the formula; not a consequence of addXYZ_self
  sorry

theorem formalAddY_hCoeff2 : hCoeff 2 (formalAddY W) = 0 := by
  -- must unfold the formula; not a consequence of addXYZ_self
  sorry

theorem formalAddY_diag_order3' :
    ∃ Q : FG2 K, formalAddY W = δ^3 * Q := by
  exact diagPow3_dvd_of_hCoeff012_eq_zero
    (formalAddY_hCoeff0 (W := W))
    (formalAddY_hCoeff1 (W := W))
    (formalAddY_hCoeff2 (W := W))
```

This is a valid plan, but the `hCoeff1` and `hCoeff2` proofs will still require expanding the projective formula.  In practice this is usually more work than the `U,V` factorization proof.

Also, avoid a derivative statement such as

```text
f(s+h,s) = f(s,s) + h f'(s,s) + h²/2 f''(s,s) + ...
```

because that introduces factorial denominators and will cause characteristic `2`/`3` trouble.  Use coefficient extraction in `h`, not derivatives divided by factorials.

---

## Best Lean implementation plan

### File 1: `scratch/FormalGroupW_DiagonalIdeal.lean`

Define two-variable notation and the diagonal factor.

```lean
abbrev FG2 (K : Type*) [CommRing K] := MvPowerSeries (Fin 2) K

def T₀ : FG2 K := MvPowerSeries.X 0
def T₁ : FG2 K := MvPowerSeries.X 1
def δ : FG2 K := T₀ - T₁
```

Add generic one-factor diagonal divisibility if not already available from Q461:

```lean
theorem diag_dvd_of_diagEval_eq_zero
    (f : FG2 K) (hf : diagEval f = 0) :
    ∃ q : FG2 K, f = δ * q := by
  sorry
```

Expected size: 100–200 lines if the coefficient construction is needed; much shorter if a previous lemma already exists.

### File 2: `scratch/FormalGroupW_AddXYZUV.lean`

Expose the chord variables after substituting `P(t)`:

```lean
noncomputable def formalU (W : WeierstrassCurve K) : FG2 K := ...
noncomputable def formalV (W : WeierstrassCurve K) : FG2 K := ...
```

Prove one-factor divisibility:

```lean
theorem formalU_diag_factor :
    ∃ U₁ : FG2 K, formalU W = δ * U₁ := by ...

theorem formalV_diag_factor :
    ∃ V₁ : FG2 K, formalV W = δ * V₁ := by ...
```

Expected size: 50–120 lines.

### File 3: `scratch/FormalGroupW_AddXYZOrder3.lean`

Prove the structural cubic-in-`U,V` lemma for each coordinate needed.

```lean
theorem formalAddY_cubic_in_UV
    {U₁ V₁ : FG2 K}
    (hU : formalU W = δ * U₁)
    (hV : formalV W = δ * V₁) :
    ∃ Q : FG2 K, formalAddY W = δ^3 * Q := by
  unfold formalAddY formalU formalV
  unfold Projective.addY -- exact namespace/name may differ
  rw [hU, hV]
  refine ⟨_, ?_⟩
  ring
```

Then package:

```lean
theorem formalAddY_diag_order3 :
    ∃ Q : FG2 K, formalAddY W = δ^3 * Q := by
  rcases formalU_diag_factor (W := W) with ⟨U₁, hU⟩
  rcases formalV_diag_factor (W := W) with ⟨V₁, hV⟩
  exact formalAddY_cubic_in_UV (W := W) hU hV
```

Expected size: 80–180 lines if Mathlib's formula is reasonably unfoldable.  If `ring` explodes, split by the four `U,V` degree buckets:

```text
U^3 terms,
U^2 V terms,
U V^2 terms,
V^3 terms.
```

### File 4: optional `scratch/FormalGroupW_DiffJet.lean`

Only build this if the `U,V` factorization is blocked.

Define `diffSubst`, `hCoeff`, and prove:

```lean
theorem diagPow3_dvd_iff_hCoeff012_eq_zero :
    (∃ q, f = δ^3 * q) ↔
      hCoeff 0 f = 0 ∧ hCoeff 1 f = 0 ∧ hCoeff 2 f = 0 := by
  sorry
```

This is reusable but heavier.  Expected size: 200–350 lines.

---

## Practical recommendation

Use route (1), not route (2), for the first implementation.

The theorem to exploit is:

```text
formalU, formalV are each divisible by δ,
and formalAddY is cubic in formalU/formalV.
```

This proves `(t₀-t₁)^3 ∣ formalAddY` without derivatives, without factorials, and without relying on a fragile global Taylor setup.

The Taylor/finite-jet route is still a good independent checker: after `formalAddY_diag_order3` is proved, `diffSubst formalAddY` should have zero `h^0`, `h^1`, and `h^2` coefficients.  But as a proof strategy, the `U,V` factorization is more Lean-friendly because it gives the quotient needed for normalization.

---

## Final answer

Yes, you can prove `(t₀-t₁)^3 ∣ formalAddY`, but **not** from `addXYZ_self` alone.  `addXYZ_self` gives only order `1`.  The order `3` must be proved from the formula structure: the projective addition coordinates are cubic in the chord variables `U,V`, and `U,V` each vanish to order `1` on the diagonal after substituting `P(t)`.  In Lean, expose `formalU` and `formalV`, prove `δ ∣ formalU` and `δ ∣ formalV`, then unfold `Projective.addY` and factor `δ^3` by `ring`/`ring_nf`.  Use the Taylor/finite-jet method only as a fallback or as a verification layer; avoid derivative/factorial Taylor formulas because they are characteristic-sensitive.
