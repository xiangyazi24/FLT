# Q595 (dm2): `formalUCoeff_map` for `WellFounded.fix`

## Executive answer

Use `Nat.strongRecOn`, not `Nat.rec_aux`, and do not try to reason about `WellFounded.fix` directly inside every recursive term.  The clean pattern is:

1. strong-induct on the coefficient index `n`;
2. unfold both recursive definitions once with `formalUCoeff_eq`;
3. in the successor case, prove termwise map-compatibility for each conditional summand;
4. prove the quadratic/cubic sum terms by `rw [map_sum]` + `Finset.sum_congr` + recursive IH + `omega`.

The most robust handling of the `dite`/`if h : ... then ... else ...` terms is **not** to hope that one giant `simp` handles everything.  Prove a local lemma for each conditional term using `by_cases h : ...`, and inside the true branch use the corresponding sum-map helper.

---

## Recommended theorem shape

I would state the theorem as the recursive/`∀ n` form first, then derive the pointwise form if desired:

```lean
theorem formalUCoeff_map
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (W : WeierstrassCurve R) :
    ∀ n : ℕ,
      formalUCoeff (W.map φ) n = φ (formalUCoeff W n) := by
  classical
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih
  rw [formalUCoeff_eq (W.map φ) n, formalUCoeff_eq W n]
  cases n with
  | zero =>
      simp [formalUCoeffBody, WeierstrassCurve.map]
  | succ n =>
      -- `ih : ∀ m, m < n + 1 →
      --     formalUCoeff (W.map φ) m = φ (formalUCoeff W m)`
      -- The body-map proof goes here.
      exact formalUCoeffBody_map_succ φ W n ih
```

Here `formalUCoeffBody_map_succ` can be either a separate private lemma or just an inline block.  I recommend first proving it inline; once it works, move it out if the file gets noisy.

The key is that after the two `rw [formalUCoeff_eq]`, the goal is exactly:

```lean
formalUCoeffBody (W.map φ) (n + 1)
    (fun m _ => formalUCoeff (W.map φ) m)
  =
φ (formalUCoeffBody W (n + 1)
    (fun m _ => formalUCoeff W m))
```

so every recursive call has index `< n + 1`, which is precisely what `ih` provides.

---

## Inline successor-case skeleton

Below is the practical structure I would use.  The a₆ inner range below is written in the common shape
`Finset.range (n - 4 - x.1)`.  Replace that line with the exact inner finset from your local `formalUCoeffBody` if it differs.

```lean
  | succ n =>
      -- Main a₁ term.
      have h₁ :
          formalUCoeff (W.map φ) n = φ (formalUCoeff W n) :=
        ih n (by omega)

      -- Quadratic sum for the a₃ term.
      have hΣ₃ (hn : n ≥ 2) :
          (∑ x in (Finset.range (n - 1)).attach,
              formalUCoeff (W.map φ) x.1 *
                formalUCoeff (W.map φ) (n - 2 - x.1))
            =
          φ (∑ x in (Finset.range (n - 1)).attach,
              formalUCoeff W x.1 *
                formalUCoeff W (n - 2 - x.1)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hx
        have hxlt : x.1 < n - 1 := by
          simpa [Finset.mem_range] using x.2
        simp only [RingHom.map_mul]
        rw [ih x.1 (by omega)]
        rw [ih (n - 2 - x.1) (by omega)]

      -- Quadratic sum for the a₄ term.
      have hΣ₄ (hn : n ≥ 3) :
          (∑ x in (Finset.range (n - 2)).attach,
              formalUCoeff (W.map φ) x.1 *
                formalUCoeff (W.map φ) (n - 3 - x.1))
            =
          φ (∑ x in (Finset.range (n - 2)).attach,
              formalUCoeff W x.1 *
                formalUCoeff W (n - 3 - x.1)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hx
        have hxlt : x.1 < n - 2 := by
          simpa [Finset.mem_range] using x.2
        simp only [RingHom.map_mul]
        rw [ih x.1 (by omega)]
        rw [ih (n - 3 - x.1) (by omega)]

      -- Cubic/nested sum for the a₆ term.
      -- Adjust the inner finset to match your actual definition.
      have hΣ₆ (hn : n ≥ 5) :
          (∑ x in (Finset.range (n - 4)).attach,
              formalUCoeff (W.map φ) x.1 *
                ∑ y in (Finset.range (n - 4 - x.1)).attach,
                  formalUCoeff (W.map φ) y.1 *
                    formalUCoeff (W.map φ) (n - 5 - x.1 - y.1))
            =
          φ (∑ x in (Finset.range (n - 4)).attach,
              formalUCoeff W x.1 *
                ∑ y in (Finset.range (n - 4 - x.1)).attach,
                  formalUCoeff W y.1 *
                    formalUCoeff W (n - 5 - x.1 - y.1)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hx
        have hxlt : x.1 < n - 4 := by
          simpa [Finset.mem_range] using x.2
        simp only [RingHom.map_mul]
        rw [ih x.1 (by omega)]
        -- Now the remaining goal is the inner sum map statement.
        congr 1
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro y hy
        have hylt : y.1 < n - 4 - x.1 := by
          simpa [Finset.mem_range] using y.2
        simp only [RingHom.map_mul]
        rw [ih y.1 (by omega)]
        rw [ih (n - 5 - x.1 - y.1) (by omega)]

      -- a₂ conditional term.
      have hT₂ :
          (if h : n ≥ 1 then
              (W.map φ).a₂ * formalUCoeff (W.map φ) (n - 1)
            else 0)
            =
          φ (if h : n ≥ 1 then
              W.a₂ * formalUCoeff W (n - 1)
            else 0) := by
        by_cases h : n ≥ 1
        · simp [h, WeierstrassCurve.map, ih (n - 1) (by omega)]
        · simp [h]

      -- a₃ conditional term.
      have hT₃ :
          (if h : n ≥ 2 then
              (W.map φ).a₃ *
                ∑ x in (Finset.range (n - 1)).attach,
                  formalUCoeff (W.map φ) x.1 *
                    formalUCoeff (W.map φ) (n - 2 - x.1)
            else 0)
            =
          φ (if h : n ≥ 2 then
              W.a₃ *
                ∑ x in (Finset.range (n - 1)).attach,
                  formalUCoeff W x.1 *
                    formalUCoeff W (n - 2 - x.1)
            else 0) := by
        by_cases h : n ≥ 2
        · simp [h, WeierstrassCurve.map, hΣ₃ h]
        · simp [h]

      -- a₄ conditional term.
      have hT₄ :
          (if h : n ≥ 3 then
              (W.map φ).a₄ *
                ∑ x in (Finset.range (n - 2)).attach,
                  formalUCoeff (W.map φ) x.1 *
                    formalUCoeff (W.map φ) (n - 3 - x.1)
            else 0)
            =
          φ (if h : n ≥ 3 then
              W.a₄ *
                ∑ x in (Finset.range (n - 2)).attach,
                  formalUCoeff W x.1 *
                    formalUCoeff W (n - 3 - x.1)
            else 0) := by
        by_cases h : n ≥ 3
        · simp [h, WeierstrassCurve.map, hΣ₄ h]
        · simp [h]

      -- a₆ conditional term.
      -- Again, adjust the inner finset if your body uses a slightly different one.
      have hT₆ :
          (if h : n ≥ 5 then
              (W.map φ).a₆ *
                ∑ x in (Finset.range (n - 4)).attach,
                  formalUCoeff (W.map φ) x.1 *
                    ∑ y in (Finset.range (n - 4 - x.1)).attach,
                      formalUCoeff (W.map φ) y.1 *
                        formalUCoeff (W.map φ) (n - 5 - x.1 - y.1)
            else 0)
            =
          φ (if h : n ≥ 5 then
              W.a₆ *
                ∑ x in (Finset.range (n - 4)).attach,
                  formalUCoeff W x.1 *
                    ∑ y in (Finset.range (n - 4 - x.1)).attach,
                      formalUCoeff W y.1 *
                        formalUCoeff W (n - 5 - x.1 - y.1)
            else 0) := by
        by_cases h : n ≥ 5
        · simp [h, WeierstrassCurve.map, hΣ₆ h]
        · simp [h]

      -- Final assembly: unfold the body, push `φ` through `+` and `*`,
      -- and use the five termwise equalities above.
      simp [formalUCoeffBody, WeierstrassCurve.map,
        RingHom.map_add, RingHom.map_mul,
        h₁, hT₂, hT₃, hT₄, hT₆]
```

This is the structure I would actually try first.  It is longer than a one-line `simp`, but it is robust because each `if` branch carries the right arithmetic hypothesis (`h : n ≥ k`) into the recursive-index `omega` calls.

---

## If you prefer `split_ifs`

A more compact variant is possible, but it is usually less stable when the branch proof is used to build recursive-call proofs:

```lean
      simp only [formalUCoeffBody, WeierstrassCurve.map,
        RingHom.map_one, RingHom.map_zero,
        RingHom.map_add, RingHom.map_mul,
        map_sum, apply_ite, apply_dite]
      split_ifs with h₂ h₃ h₄ h₆ <;>
        simp [h₁, hΣ₃, hΣ₄, hΣ₆]
```

I would only use this after the termwise version builds.  The `by_cases` version is easier to debug because failures occur in the specific `a₂`, `a₃`, `a₄`, or `a₆` local lemma.

---

## Practical notes for `.attach`

For a binder like

```lean
∑ x in (Finset.range (n - 1)).attach, ... x.1 ...
```

you can usually recover the range bound by:

```lean
have hxlt : x.1 < n - 1 := by
  simpa [Finset.mem_range] using x.2
```

Then `omega` closes the recursive side conditions:

```lean
rw [ih x.1 (by omega)]
rw [ih (n - 2 - x.1) (by omega)]
```

For the nested a₆ sum, do the same twice:

```lean
have hxlt : x.1 < n - 4 := by
  simpa [Finset.mem_range] using x.2
have hylt : y.1 < n - 4 - x.1 := by
  simpa [Finset.mem_range] using y.2
rw [ih x.1 (by omega)]
rw [ih y.1 (by omega)]
rw [ih (n - 5 - x.1 - y.1) (by omega)]
```

The important point is that you should not need to mention the subtype membership proof `hx : x ∈ ...attach` from `sum_congr`; the useful proof is usually `x.2`.

---

## Why this avoids proof-witness pain

A fully general lemma

```lean
formalUCoeffBody (W.map φ) n uS = φ (formalUCoeffBody W n uR)
```

for arbitrary dependent `uR : (m : ℕ) → m < n → R` is slightly annoying, because `uR` could in principle depend on the proof witness `m < n`.  Your actual recursive functions are proof-irrelevant in the second argument:

```lean
fun m _ => formalUCoeff W m
fun m _ => formalUCoeff (W.map φ) m
```

So the cleanest proof is the specialized one above: unfold `formalUCoeffBody` only after substituting those proof-irrelevant recursive functions.  Then all recursive calls are ordinary terms `formalUCoeff W k`, and the IH rewrites them directly.

---

## Optional refactor that makes this much shorter

If you are willing to add one abstraction, define a non-dependent step functional:

```lean
noncomputable def formalUStep (W : WeierstrassCurve R) (u : ℕ → R) (n : ℕ) : R :=
  W.a₁ * u n
  + (if h : n ≥ 1 then W.a₂ * u (n - 1) else 0)
  + ...
```

Then prove once:

```lean
theorem formalUCoeff_succ (W : WeierstrassCurve R) (n : ℕ) :
    formalUCoeff W (n + 1) = formalUStep W (formalUCoeff W) n := by
  rw [formalUCoeff_eq]
  simp [formalUCoeffBody, formalUStep]
```

and the real naturality lemma becomes:

```lean
lemma formalUStep_map
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (W : WeierstrassCurve R) (n : ℕ)
    {uR : ℕ → R} {uS : ℕ → S}
    (hu : ∀ m, m ≤ n → uS m = φ (uR m)) :
    formalUStep (W.map φ) uS n = φ (formalUStep W uR n) := by
  classical
  -- same `hΣ₃`, `hΣ₄`, `hΣ₆`, `hT₂`, ... pattern,
  -- but now no dependent proof arguments occur anywhere.
  ...
```

Then `formalUCoeff_map` is just:

```lean
theorem formalUCoeff_map
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (W : WeierstrassCurve R) :
    ∀ n : ℕ,
      formalUCoeff (W.map φ) n = φ (formalUCoeff W n) := by
  classical
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih
  cases n with
  | zero =>
      simp [formalUCoeff_eq, formalUCoeffBody, formalUStep]
  | succ n =>
      rw [formalUCoeff_succ, formalUCoeff_succ]
      exact formalUStep_map φ W n (by
        intro m hm
        exact ih m (by omega))
```

This refactor is the most maintainable version if `formalUCoeffBody` will be reused later.  If you only need `formalUCoeff_map`, the inline successor-case proof above is perfectly acceptable.

## Bottom line

Use `Nat.strongRecOn`; unfold the `WellFounded.fix` only through `formalUCoeff_eq`; push `φ` through sums with `rw [map_sum]`; handle `.attach` by extracting `x.2`; and handle the conditional terms with local `by_cases` lemmas.  That combination avoids both the `WellFounded.fix` noise and the dependent-proof-witness noise from the recursive body.
