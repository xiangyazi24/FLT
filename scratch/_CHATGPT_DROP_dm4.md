# Q45 (dm4): Keystone avenue (d) — core assembly discharge

## Investigation result

I attempted to inspect the requested source locations before writing the patch:

```text
scratch/KeystoneLadder.lean   L960–1090 and L1160–1200
```

on `xiangyazi24/FLT@scratch`.  The GitHub contents API still returns `404` for that path.  Code search for the concrete names

```text
KeystoneLadder.lean
xPair_double_and_diffAddOrInf_EDS_core
xPair_double_sameP1
xPair_diffAdd_sameP1_core_order
```

returns no hits in the accessible repository index, and `main...scratch` lists only the four `scratch/_CHATGPT_DROP_*.md` files as changed.  A local clone was also not possible here because DNS resolution for `github.com` fails in the execution container.

So the code below is the exact avenue-(d) assembly patch for the theorem shape in the prompt, but I could not verify local line numbers or compile against the unavailable `KeystoneLadder.lean` file.

## Decision on the core signature

The original core signature

```lean
private theorem xPair_double_and_diffAddOrInf_EDS_core
    (W : WeierstrassCurve k) [W.IsElliptic] (m : ℕ) (x : k) : ...
```

is not strong enough to call the two proven `SameP1Vec` lemmas.  The core must carry the hypotheses required by those lemmas:

```lean
(h4 : (4 : k) ≠ 0)
(hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
(hc3 : W.Ψ₃ ≠ 0)
```

`[W.IsElliptic]` alone does **not** provide these.  In particular, nonsingular Weierstrass curves exist in characteristic `2`, so `h4` cannot follow from ellipticity.  The global nonvanishing of all `W.ψ n` is also stronger than nonsingularity in positive characteristic.  Therefore the clean correct interface is to add these three hypotheses to the private core and propagate them to the surrounding theorem, unless the surrounding theorem is already in a stronger context that explicitly proves them, such as a characteristic-zero/division-polynomial-nonzero section.

The `[W.IsElliptic]` instance is still needed for the avenue-(c) coprimality lemmas proving the nonzero vector conjuncts non-circularly.

## Required avenue-(c) no-common-root inputs

Do **not** use the repo's `xPair_ne_zero_of_isElliptic` if, as reported, it is proved through this core.  The nonzero conjuncts must come directly from the avenue-(c) no-common-root facts:

```lean
Φ_ΨSq_no_common_eval_zero_odd
    (W : WeierstrassCurve k) (x : k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0) (m : ℕ) :
    ¬ ((W.Φ (((2*m+1 : ℕ) : ℤ))).eval x = 0 ∧
       (W.ΨSq (((2*m+1 : ℕ) : ℤ))).eval x = 0)
```

and the analogous even statement, which should be exported from the same avenue-(c) machinery:

```lean
Φ_ΨSq_no_common_eval_zero_even
    (W : WeierstrassCurve k) (x : k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0) (m : ℕ) :
    ¬ ((W.Φ (((2*m : ℕ) : ℤ))).eval x = 0 ∧
       (W.ΨSq (((2*m : ℕ) : ℤ))).eval x = 0)
```

The even proof is mathematically the same no-adjacent-`preΨ` argument: `ΨSq (2*m)` expands as a square of the relevant `preΨ` factor times `Ψ₂Sq`, and common vanishing with `Φ (2*m)` would force the forbidden adjacent/preΨ vanishing plus the `2`-torsion factor ruled out by ellipticity and `h4`.

## Lean patch

Paste this in `namespace KeystoneLadder` / `namespace XOnly`, near `xPair` and before the core theorem.  It assumes `xPair` is the integer-indexed definition from the prompt:

```lean
private lemma xPair_ne_zero_of_Φ_ΨSq_no_common
    (W : WeierstrassCurve k) (n : ℤ) (x : k)
    (h : ¬ ((W.Φ n).eval x = 0 ∧
            (W.ΨSq n).eval x = 0)) :
    xPair W n x ≠ 0 := by
  intro hv
  apply h
  constructor
  · have h0 := congrFun hv (0 : Fin 2)
    simpa [xPair] using h0
  · have h1 := congrFun hv (1 : Fin 2)
    simpa [xPair] using h1

private lemma xPair_even_ne_zero_of_avenueC
    (W : WeierstrassCurve k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0) (m : ℕ) (x : k) :
    xPair W (((2*m : ℕ) : ℤ)) x ≠ 0 := by
  exact
    xPair_ne_zero_of_Φ_ΨSq_no_common
      (W := W) (n := (((2*m : ℕ) : ℤ))) (x := x)
      (Φ_ΨSq_no_common_eval_zero_even
        (W := W) (x := x) (h4 := h4) (m := m))

private lemma xPair_odd_ne_zero_of_avenueC
    (W : WeierstrassCurve k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0) (m : ℕ) (x : k) :
    xPair W (((2*m+1 : ℕ) : ℤ)) x ≠ 0 := by
  exact
    xPair_ne_zero_of_Φ_ΨSq_no_common
      (W := W) (n := (((2*m+1 : ℕ) : ℤ))) (x := x)
      (Φ_ΨSq_no_common_eval_zero_odd
        (W := W) (x := x) (h4 := h4) (m := m))
```

Now replace the core theorem by this strengthened version:

```lean
private theorem xPair_double_and_diffAddOrInf_EDS_core
    (W : WeierstrassCurve k) [W.IsElliptic] (m : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    xPair W (((2*m : ℕ) : ℤ)) x ≠ 0 ∧
    SameP1Vec
      (XOnly.doubleVec (E := W⁄k) (xPair W (m : ℤ) x))
      (xPair W (((2*m : ℕ) : ℤ)) x) ∧
    xPair W (((2*m+1 : ℕ) : ℤ)) x ≠ 0 ∧
    SameP1Vec
      (XOnly.diffAddOrInfVec (E := W⁄k)
        (xPair W (m : ℤ) x)
        (xPair W (((m+1 : ℕ) : ℤ)) x)
        (xPair W (1 : ℤ) x))
      (xPair W (((2*m+1 : ℕ) : ℤ)) x) := by
  have h2m_ne : xPair W (((2*m : ℕ) : ℤ)) x ≠ 0 :=
    xPair_even_ne_zero_of_avenueC
      (W := W) (h4 := h4) (m := m) (x := x)

  have h2m1_ne : xPair W (((2*m+1 : ℕ) : ℤ)) x ≠ 0 :=
    xPair_odd_ne_zero_of_avenueC
      (W := W) (h4 := h4) (m := m) (x := x)

  have hdouble_int :
      SameP1Vec
        (XOnly.doubleVec (E := W⁄k) (xPair W (m : ℤ) x))
        (xPair W (2 * (m : ℤ)) x) := by
    exact
      xPair_double_sameP1
        (W := W) (m := (m : ℤ)) (x := x)
        (h4 := h4) (hψ_ne := hψ_ne) (hc3 := hc3)

  have hdouble :
      SameP1Vec
        (XOnly.doubleVec (E := W⁄k) (xPair W (m : ℤ) x))
        (xPair W (((2*m : ℕ) : ℤ)) x) := by
    simpa using hdouble_int

  have hdiff_int :
      SameP1Vec
        (XOnly.diffAddOrInfVec (E := W⁄k)
          (xPair W (m : ℤ) x)
          (xPair W ((m : ℤ) + 1) x)
          (xPair W (1 : ℤ) x))
        (xPair W (2 * (m : ℤ) + 1) x) := by
    exact
      xPair_diffAdd_sameP1_core_order
        (W := W) (m := (m : ℤ)) (x := x)
        (h4 := h4) (hψ_ne := hψ_ne) (hc3 := hc3)

  have hdiff :
      SameP1Vec
        (XOnly.diffAddOrInfVec (E := W⁄k)
          (xPair W (m : ℤ) x)
          (xPair W (((m+1 : ℕ) : ℤ)) x)
          (xPair W (1 : ℤ) x))
        (xPair W (((2*m+1 : ℕ) : ℤ)) x) := by
    simpa using hdiff_int

  exact ⟨h2m_ne, hdouble, h2m1_ne, hdiff⟩
```

The `simpa` steps are the cast reconciliation.  They use the standard simp lemmas

```lean
Nat.cast_mul
Nat.cast_add
Nat.cast_one
Nat.cast_ofNat
```

to identify

```lean
(((2*m : ℕ) : ℤ))     = 2 * (m : ℤ)
(((2*m+1 : ℕ) : ℤ))   = 2 * (m : ℤ) + 1
(((m+1 : ℕ) : ℤ))     = (m : ℤ) + 1
```

If the local simplifier does not close one of these cast goals, make the casts explicit:

```lean
  have h2m_cast : (((2*m : ℕ) : ℤ)) = 2 * (m : ℤ) := by
    simp
  have h2m1_cast : (((2*m+1 : ℕ) : ℤ)) = 2 * (m : ℤ) + 1 := by
    simp [Nat.cast_add, Nat.cast_mul]
  have hm1_cast : (((m+1 : ℕ) : ℤ)) = (m : ℤ) + 1 := by
    simp
```

and then use `simpa [h2m_cast, h2m1_cast, hm1_cast] using ...`.

## If the local diff-add goal has the opposite input order

The theorem statement in this Q45 prompt already has the same order as `xPair_diffAdd_sameP1_core_order`:

```lean
(xPair W (m : ℤ) x), (xPair W (((m+1 : ℕ) : ℤ)) x)
```

so `diffAddOrInfVec_comm` is not needed.  If the actual local file still has the older order `(m+1), m`, replace the `hdiff` proof with:

```lean
  have hdiff :
      SameP1Vec
        (XOnly.diffAddOrInfVec (E := W⁄k)
          (xPair W (((m+1 : ℕ) : ℤ)) x)
          (xPair W (m : ℤ) x)
          (xPair W (1 : ℤ) x))
        (xPair W (((2*m+1 : ℕ) : ℤ)) x) := by
    simpa [XOnly.diffAddOrInfVec_comm] using hdiff_int
```

If `diffAddOrInfVec_comm` is in the current `XOnly` namespace, the unqualified name also works:

```lean
    simpa [diffAddOrInfVec_comm] using hdiff_int
```

## Propagating the new hypotheses

Every call of the old core must now pass the three extra hypotheses:

```lean
  exact xPair_double_and_diffAddOrInf_EDS_core
    (W := W) (m := m) (x := x)
    (h4 := h4) (hψ_ne := hψ_ne) (hc3 := hc3)
```

If the surrounding theorem currently has only `[W.IsElliptic]`, its signature must be strengthened as well.  The correct propagation is either explicit:

```lean
(h4 : (4 : k) ≠ 0)
(hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
(hc3 : W.Ψ₃ ≠ 0)
```

or through a stronger section assumption plus lemmas that genuinely provide them.  For a characteristic-zero field, `h4` is immediate:

```lean
  have h4 : (4 : k) ≠ 0 := by norm_num
```

but `hψ_ne` should still come from an actual division-polynomial nonvanishing theorem in the file/Mathlib, not from ellipticity alone.  If that theorem is present, the call-site shape is:

```lean
  have hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0 := by
    intro n hn
    exact WeierstrassCurve.ψ_ne_zero (W := W) hn
```

adjusting the theorem name/arguments to the local API.  Then `hc3` can either be passed separately or derived from `hψ_ne`:

```lean
  have hc3 : W.Ψ₃ ≠ 0 := by
    intro hzero
    have hψ3 : W.ψ (3 : ℤ) ≠ 0 := hψ_ne 3 (by norm_num)
    apply hψ3
    simpa [WeierstrassCurve.ψ, hzero]
```

If this last `simpa` does not unfold `W.ψ 3` far enough in the local Mathlib version, keep `hc3` explicit; the core proof above does not depend on how `hc3` is obtained.

## Summary of the non-circularity

The core proof uses only:

1. `Φ_ΨSq_no_common_eval_zero_even` for the `2*m` vector nonzero conjunct;
2. `Φ_ΨSq_no_common_eval_zero_odd` for the `2*m+1` vector nonzero conjunct;
3. `xPair_double_sameP1` for the doubling projective equality;
4. `xPair_diffAdd_sameP1_core_order` for the differential-addition projective equality;
5. `simpa` to reconcile the `ℕ → ℤ` casts.

It does **not** use `xPair_ne_zero_of_isElliptic`, so it avoids the circular dependency through the ladder theorem.
