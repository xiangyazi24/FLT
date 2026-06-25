# Q592 (dm2): naturality of `formalU`, `formalW`, and `formalAddXYZ`

## Executive answer

Yes, this transport should be straightforward, and Mathlib already has the key projective-coordinate naturality lemma you want:

```lean
@[simp]
lemma WeierstrassCurve.Projective.map_addXYZ :
    (W'.map f).addXYZ (f ∘ P) (f ∘ Q) = f ∘ addXYZ W' P Q
```

In the pinned FLT Mathlib revision, the surrounding API also includes

```lean
map_addX
map_addY
map_addZ
map_negAddY
```

so Goal 4 should not require unfolding `addXYZ` manually.

The clean proof route is:

1. prove `formalUCoeff_map` by strong induction using your recurrence equation lemmas, not by fighting `WellFounded.fix` directly;
2. prove `formalU_map` by `ext n; simp [formalU, formalUCoeff_map]` using `PowerSeries.coeff_map`;
3. prove `formalW_map` by `simp [formalW, formalU_map]` using `PowerSeries.map_X`;
4. prove `formalPointMv_map`; then Goal 4 is essentially `Projective.map_addXYZ` plus curve-coefficient-map compatibility.

---

## Mathlib API facts checked

### Power series coefficient map

Mathlib has:

```lean
/-- The map between formal power series induced by a map on the coefficients. -/
def PowerSeries.map : R⟦X⟧ →+* S⟦X⟧ :=
  MvPowerSeries.map f

@[simp]
theorem PowerSeries.coeff_map (n : ℕ) (φ : R⟦X⟧) :
    coeff n (map f φ) = f (coeff n φ) :=
  rfl

@[simp]
theorem PowerSeries.map_X : map f X = X := ...
```

So Goals 2 and 3 should be coefficient-extensional and short.

### Multivariate power series coefficient map

Mathlib has:

```lean
@[simp]
theorem MvPowerSeries.coeff_map (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    coeff n (map f φ) = f (coeff n φ) :=
  rfl

@[simp]
theorem MvPowerSeries.map_C (a : R) : map f (C a) = C (f a)

@[simp]
theorem MvPowerSeries.map_X (s : σ) : map f (X s) = X s
```

### Rename / one-variable-to-two-variable transport

If `formalPointMv` embeds `formalW` by renaming the single variable into coordinate `i : Fin 2`, Mathlib has exactly the commutation lemma:

```lean
theorem MvPowerSeries.rename_map (φ : R →+* S) (p : MvPowerSeries σ R) :
    rename f (map φ p) = map φ (rename f p)
```

This is the right replacement for a heavier `subst_map` argument when the substitution is just variable inclusion/renaming.

### Projective naturality

Mathlib has:

```lean
@[simp]
lemma map_addZ :
    (W'.map f).addZ (f ∘ P) (f ∘ Q) = f (W'.addZ P Q) := by
  simp only [addZ]
  map_simp

@[simp]
lemma map_addX :
    (W'.map f).addX (f ∘ P) (f ∘ Q) = f (W'.addX P Q) := by
  simp only [addX]
  map_simp

@[simp]
lemma map_negAddY :
    (W'.map f).negAddY (f ∘ P) (f ∘ Q) = f (W'.negAddY P Q) := by
  simp only [negAddY]
  map_simp

@[simp]
lemma map_addY :
    (W'.map f).addY (f ∘ P) (f ∘ Q) = f (W'.addY P Q) := by
  simp only [addY, negY_eq, map_negAddY, map_addX, map_addZ]
  map_simp

@[simp]
lemma map_addXYZ :
    (W'.map f).addXYZ (f ∘ P) (f ∘ Q) = f ∘ addXYZ W' P Q := by
  simp only [addXYZ, map_addX, map_addY, map_addZ, comp_fin3]
```

So Goal 4 has a named lemma: use `Projective.map_addXYZ`.

---

## Goal 1: `formalUCoeff_map`

### Do not prove against `WellFounded.fix` directly

The cleanest route is to isolate equation lemmas first:

```lean
@[simp] theorem formalUCoeff_zero (W : WeierstrassCurve R) :
    formalUCoeff W 0 = 1 := ...

theorem formalUCoeff_succ (W : WeierstrassCurve R) (n : ℕ) :
    formalUCoeff W (n+1) =
      W.a₁ * formalUCoeff W n
      + (if hn1 : 1 ≤ n then W.a₂ * formalUCoeff W (n-1) else 0)
      + (if hn2 : 2 ≤ n then W.a₃ * ∑ i in Finset.range (n-1),
            formalUCoeff W i * formalUCoeff W (n-2-i) else 0)
      + ... := ...
```

If `formalUCoeff` is literally defined by `WellFounded.fix`, prove these equation lemmas once with

```lean
unfold formalUCoeff
rw [WellFounded.fix_eq]
```

or whatever local wrapper unfolds the fixpoint.  After those equation lemmas exist, the map proof should never mention `WellFounded.fix` again.

### Strong induction skeleton

Use `Nat.strong_induction_on` on the target coefficient index.  The successor case uses `formalUCoeff_succ`; every recursive coefficient index is smaller, so `omega` closes the side conditions.

```lean
theorem formalUCoeff_map
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (W : WeierstrassCurve R) :
    ∀ n : ℕ,
      formalUCoeff (W.map φ) n = φ (formalUCoeff W n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [formalUCoeff_zero]
      | succ n =>
          rw [formalUCoeff_succ, formalUCoeff_succ]
          -- expose mapped coefficients and ring-hom action on sums/conditionals
          simp only [
            WeierstrassCurve.map,
            RingHom.map_one, RingHom.map_zero,
            RingHom.map_add, RingHom.map_mul,
            map_sum, apply_ite
          ]
          -- Then each branch is a recurrence-index rewrite.
          -- Typical coefficient rewrites:
          have hn_lt : n < n + 1 := by omega
          -- exact ih n hn_lt
          -- For n-1, n-2-i, etc. use `omega`.
          -- For sums:
          --   apply Finset.sum_congr rfl
          --   intro i hi
          --   rw [ih i (by omega), ih (n-2-i) (by omega)]
          -- and similarly for nested sums.
          sorry
```

In practice, I would not put all sum work inline.  Make local helper lemmas inside the successor case, e.g.

```lean
have hquad (k : ℕ) (hk : k + 2 ≤ n) :
    (∑ i in Finset.range (k+1),
        formalUCoeff (W.map φ) i * formalUCoeff (W.map φ) (k-i))
      = φ (∑ i in Finset.range (k+1),
        formalUCoeff W i * formalUCoeff W (k-i)) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [RingHom.map_mul]
  rw [ih i (by omega), ih (k-i) (by omega)]
```

and a nested/cubic helper:

```lean
have hcubic (k : ℕ) (hk : k + 5 ≤ n) :
    (∑ i in Finset.range (k+1),
      formalUCoeff (W.map φ) i *
        ∑ j in Finset.range (k-i+1),
          formalUCoeff (W.map φ) j * formalUCoeff (W.map φ) (k-i-j))
      = φ (∑ i in Finset.range (k+1),
      formalUCoeff W i *
        ∑ j in Finset.range (k-i+1),
          formalUCoeff W j * formalUCoeff W (k-i-j)) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [RingHom.map_mul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [RingHom.map_mul]
  rw [ih i (by omega), ih j (by omega), ih (k-i-j) (by omega)]
```

The exact `range` bounds depend on how your recurrence is encoded.  The important pattern is:

```lean
rw [map_sum]
apply Finset.sum_congr rfl
intro i hi
rw [ih i (by omega)]
```

For `if` branches, include `apply_ite` in the `simp` set or split explicitly:

```lean
split_ifs with h₁ h₂ h₃ h₄ h₆ <;> simp [*, hquad, hcubic]
```

### Even cleaner: define a step functional

If the recurrence is still malleable, define the right-hand side as a separate functional:

```lean
def formalUStep (W : WeierstrassCurve R) (u : ℕ → R) (n : ℕ) : R :=
  ...
```

Then prove:

```lean
theorem formalUCoeff_succ :
    formalUCoeff W (n+1) = formalUStep W (formalUCoeff W) n := ...

lemma formalUStep_map
    (h : ∀ m ≤ n, uS m = φ (uR m)) :
    formalUStep (W.map φ) uS n = φ (formalUStep W uR n) := by
  simp [formalUStep, WeierstrassCurve.map, map_sum, apply_ite]
  -- `Finset.sum_congr` + `h _ (by omega)`
```

Then `formalUCoeff_map` is short:

```lean
rw [formalUCoeff_succ, formalUCoeff_succ, formalUStep_map]
```

This is the most maintainable Lean structure.

---

## Goal 2: `formalU_map`

Assuming

```lean
formalU W = PowerSeries.mk (formalUCoeff W)
```

the proof should be:

```lean
theorem formalU_map
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (W : WeierstrassCurve R) :
    PowerSeries.map φ (formalU W) = formalU (W.map φ) := by
  ext n
  simp [formalU, formalUCoeff_map φ W]
```

If the direction of `formalUCoeff_map` is opposite of the current goal, use `rw [formalUCoeff_map]` or `simpa [formalU] using (formalUCoeff_map φ W n).symm`.

---

## Goal 3: `formalW_map`

If

```lean
formalW W = PowerSeries.X ^ 3 * formalU W
```

then:

```lean
theorem formalW_map
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (W : WeierstrassCurve R) :
    PowerSeries.map φ (formalW W) = formalW (W.map φ) := by
  simp [formalW, formalU_map φ W]
```

`PowerSeries.map_X` and the ring-hom map rules should handle the rest.

---

## Goal 4: `formalAddXYZ_map`

The key Mathlib lemma is already present:

```lean
WeierstrassCurve.Projective.map_addXYZ
```

Use it with

```lean
f := MvPowerSeries.map (σ := Fin 2) φ
```

and

```lean
W' := (W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)).toProjective
```

or whatever your exact projective wrapper is.

You need two small compatibility lemmas.

### 4a. The coefficient curve commutes with map

The curve coefficients should commute by `MvPowerSeries.map_C`:

```lean
lemma formalCoeffCurve_map
    (φ : R →+* S) (W : WeierstrassCurve R) :
    ((W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)).toProjective.map
        (MvPowerSeries.map (σ := Fin 2) φ))
      = ((W.map φ).map (MvPowerSeries.C : S →+* MvPowerSeries (Fin 2) S)).toProjective := by
  ext <;> simp [WeierstrassCurve.map]
```

The exact theorem statement may need adjustment depending on whether your `toProjective` is a field projection or a coercion, but the proof should be just `ext <;> simp [WeierstrassCurve.map]`.

### 4b. The formal point commutes with map

For each `i : Fin 2`:

```lean
lemma formalPointMv_map
    (φ : R →+* S) (W : WeierstrassCurve R) (i : Fin 2) :
    formalPointMv (W.map φ) i
      = (MvPowerSeries.map (σ := Fin 2) φ) ∘ formalPointMv W i := by
  funext k
  fin_cases k
  · simp [formalPointMv, MvPowerSeries.map_X]
  · simp [formalPointMv, MvPowerSeries.map_C]
  · -- `Z = formalW` embedded into coordinate `i`
    -- If implemented by `rename`, this is exactly `MvPowerSeries.rename_map` + `formalW_map`.
    simp [formalPointMv, formalW_map, MvPowerSeries.rename_map]
```

Depending on your orientation, you may need `.symm` on `MvPowerSeries.rename_map`, because Mathlib states

```lean
rename f (map φ p) = map φ (rename f p)
```

### 4c. Main proof using `map_addXYZ`

The final proof should look like:

```lean
theorem formalAddXYZ_map
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (W : WeierstrassCurve R) :
    (fun i => MvPowerSeries.map (σ := Fin 2) φ (formalAddXYZ W i))
      = formalAddXYZ (W.map φ) := by
  unfold formalAddXYZ
  -- normalize the mapped coefficient curve
  rw [← formalCoeffCurve_map φ W]
  -- normalize the two formal points
  rw [formalPointMv_map φ W 0, formalPointMv_map φ W 1]
  -- now this is exactly Mathlib's `map_addXYZ`, up to orientation
  simpa [Function.comp_def] using
    (WeierstrassCurve.Projective.map_addXYZ
      (W' := (W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)).toProjective)
      (f := MvPowerSeries.map (σ := Fin 2) φ)
      (P := formalPointMv W 0)
      (Q := formalPointMv W 1)).symm
```

The direction may flip depending on your definition of `formalAddXYZ`.  The essential point is that the theorem already exists; do not unfold `addXYZ` unless typeclass/coercion issues make the named lemma hard to apply.

---

## Question 3: coordinate-specific shortcut

Yes.  If you only need one coordinate, use the coordinate-specific map lemmas and skip the full `addXYZ` bundle:

```lean
Projective.map_addZ
Projective.map_addX
Projective.map_addY
```

For example, a direct `formalAddZ_map` should be:

```lean
theorem formalAddZ_map
    (φ : R →+* S) (W : WeierstrassCurve R) :
    MvPowerSeries.map (σ := Fin 2) φ (formalAddZ W)
      = formalAddZ (W.map φ) := by
  unfold formalAddZ
  rw [← formalCoeffCurve_map φ W]
  rw [formalPointMv_map φ W 0, formalPointMv_map φ W 1]
  simpa [Function.comp_def] using
    (WeierstrassCurve.Projective.map_addZ
      (W' := (W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)).toProjective)
      (f := MvPowerSeries.map (σ := Fin 2) φ)
      (P := formalPointMv W 0)
      (Q := formalPointMv W 1)).symm
```

For `formalAddX`/`formalAddY`, use `map_addX`/`map_addY` similarly.  This can be less fragile than proving the whole `Fin 3` vector equality if your later theorem is coordinate-specific.

---

## Practical recommendation

Implement in this order:

```text
formalUCoeff_zero / formalUCoeff_succ       -- equation lemmas for the fix
formalUStep_map                             -- optional but highly recommended
formalUCoeff_map                            -- strong induction
formalU_map                                 -- ext + coeff_map
formalW_map                                 -- simp [formalW]
formalPointMv_map                           -- map_X, map_C, rename_map, formalW_map
formalCoeffCurve_map                        -- ext + map_C
formalAddZ_map/addX_map/addY_map or addXYZ_map -- Projective.map_* lemmas
```

The only genuinely nontrivial proof is `formalUCoeff_map`; everything after that should be a short naturality argument using existing Mathlib map lemmas.
