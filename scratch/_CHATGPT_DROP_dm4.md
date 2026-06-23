# Q15 (dm4): Keystone final assembly — nonzero facts and core assembly

## Repository check

I attempted to inspect the requested source path on `xiangyazi24/FLT@scratch` before writing this note.  The GitHub contents API returned `404` for

```text
scratch/KeystoneLadder.lean
```

on branch `scratch`, and the short commit `c83f6c6` mentioned in the prompt was not resolvable in this repository.  The branch head before this update was `a3191d161f94bd246992d13757f4ee372b808dde`, and `main...scratch` only listed the scratch drop-note files as changed.  So I could not verify the real line numbers or compile this inside the repository checkout.

What follows is therefore the exact Lean patch shape I would use in the described file.  The only identifier that may need adjustment is the existing no-common-vanishing lemma name from around L1180.

## Hypotheses the core should carry

The assembly lemma has two logically separate jobs.

1. The two `SameP1Vec` conjuncts need exactly the hypotheses already required by the proved/projected projective lemmas:

```lean
h4     : (4 : k) ≠ 0
hψ_ne  : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0
hc3    : W.Ψ₃ ≠ 0
```

2. The two vector nonzero conjuncts need the no-common-vanishing statement at the evaluation point `x`:

```lean
hNoCommon : ∀ n : ℤ,
  ¬ ((W.Φ n).eval x = 0 ∧ (W.ΨSq n).eval x = 0)
```

This is the cleanest core interface.  It does not force `IsElliptic W` into the core; the surrounding theorem can derive `hNoCommon` from `IsElliptic W` using the already-existing L1180/preΨ' argument.

I would **not** assume that `IsElliptic W` alone supplies `h4`, `hψ_ne`, or `hc3` in the file's apparent generality.  Elliptic curves exist in characteristic `2`, so `h4 : (4 : k) ≠ 0` cannot follow from `IsElliptic W` alone.  The division-polynomial nonvanishing hypothesis `hψ_ne` is also stronger than nonsingularity in positive characteristic.  Therefore either the caller must already have these hypotheses, or the caller must be in a stronger context such as a characteristic-zero/nondegenerate-division-polynomial section that proves them separately.

## Fin 2 vector helper

For a Nat-indexed `xPair`, paste this helper before the core lemma.  It is deliberately independent of elliptic-curve facts; it only converts the no-common-zero statement into vector nonzero.

```lean
private lemma xPair_ne_zero_of_noCommon
    (W : WeierstrassCurve k) (n : ℕ) (x : k)
    (h : ¬ ((W.Φ (n : ℤ)).eval x = 0 ∧
            (W.ΨSq (n : ℤ)).eval x = 0)) :
    xPair W n x ≠ 0 := by
  intro hv
  apply h
  constructor
  · have h0 := congrFun hv (0 : Fin 2)
    simpa [xPair] using h0
  · have h1 := congrFun hv (1 : Fin 2)
    simpa [xPair] using h1
```

If the file's `xPair` is integer-indexed instead, use this version instead:

```lean
private lemma xPair_ne_zero_of_noCommon
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
```

The proof is just the contrapositive of `![a,b] ≠ 0`: if `xPair W n x = 0`, evaluating the function equality at `(0 : Fin 2)` and `(1 : Fin 2)` gives the two coordinate equalities.

## Finished core lemma, Nat-indexed `xPair` version

This is the version I expect from the statement in the prompt, where the core lemma has `m : ℕ` and the division-polynomial indices in the no-common lemma are reached by casting to `ℤ`.

```lean
theorem xPair_double_and_diffAddOrInf_EDS_core
    (W : WeierstrassCurve k) (m : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0)
    (hNoCommon : ∀ n : ℤ,
      ¬ ((W.Φ n).eval x = 0 ∧ (W.ΨSq n).eval x = 0)) :
      xPair W (2*m) x ≠ 0
    ∧ SameP1Vec (XOnly.doubleVec (E:=W⁄k) (xPair W m x))
        (xPair W (2*m) x)
    ∧ xPair W (2*m+1) x ≠ 0
    ∧ SameP1Vec
        (XOnly.diffAddOrInfVec (E:=W⁄k)
          (xPair W (m+1) x) (xPair W m x) (xPair W 1 x))
        (xPair W (2*m+1) x) := by
  have h2m_ne : xPair W (2*m) x ≠ 0 :=
    xPair_ne_zero_of_noCommon (W := W) (n := 2*m) (x := x) <| by
      simpa using hNoCommon (((2*m : ℕ) : ℤ))

  have h2m1_ne : xPair W (2*m+1) x ≠ 0 :=
    xPair_ne_zero_of_noCommon (W := W) (n := 2*m+1) (x := x) <| by
      simpa using hNoCommon (((2*m+1 : ℕ) : ℤ))

  exact ⟨
    h2m_ne,
    xPair_double_sameP1
      (W := W) (m := m) (x := x)
      (h4 := h4) (hψ_ne := hψ_ne) (hc3 := hc3),
    h2m1_ne,
    xPair_diffAdd_sameP1
      (W := W) (m := m) (x := x)
      (h4 := h4) (hψ_ne := hψ_ne) (hc3 := hc3)
  ⟩
```

Two minor style variants may be needed depending on local declarations.

First, if Lean does not like the compact arithmetic/cast term in the two `hNoCommon` calls, split it out:

```lean
  have hNoCommon_2m := hNoCommon (((2*m : ℕ) : ℤ))
  have hNoCommon_2m1 := hNoCommon (((2*m+1 : ℕ) : ℤ))
```

and then pass `by simpa using hNoCommon_2m` / `by simpa using hNoCommon_2m1`.

Second, if the two projective lemmas have positional rather than named hypotheses, the four-conjunct `exact` can be written as:

```lean
  exact ⟨
    h2m_ne,
    xPair_double_sameP1 W m x h4 hψ_ne hc3,
    h2m1_ne,
    xPair_diffAdd_sameP1 W m x h4 hψ_ne hc3
  ⟩
```

## Integer-indexed `xPair` version

If the actual `xPair` declaration is `(n : ℤ)` rather than `(n : ℕ)`, use the integer helper above and change the core proof to this.  The theorem statement can remain visually the same if Lean elaborates `2*m` and `2*m+1` in the expected integer argument type.

```lean
theorem xPair_double_and_diffAddOrInf_EDS_core
    (W : WeierstrassCurve k) (m : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0)
    (hNoCommon : ∀ n : ℤ,
      ¬ ((W.Φ n).eval x = 0 ∧ (W.ΨSq n).eval x = 0)) :
      xPair W (2*m) x ≠ 0
    ∧ SameP1Vec (XOnly.doubleVec (E:=W⁄k) (xPair W m x))
        (xPair W (2*m) x)
    ∧ xPair W (2*m+1) x ≠ 0
    ∧ SameP1Vec
        (XOnly.diffAddOrInfVec (E:=W⁄k)
          (xPair W (m+1) x) (xPair W m x) (xPair W 1 x))
        (xPair W (2*m+1) x) := by
  have h2m_ne : xPair W (2*m) x ≠ 0 :=
    xPair_ne_zero_of_noCommon
      (W := W) (n := (2 : ℤ) * (m : ℤ)) (x := x) <| by
        simpa using hNoCommon ((2 : ℤ) * (m : ℤ))

  have h2m1_ne : xPair W (2*m+1) x ≠ 0 :=
    xPair_ne_zero_of_noCommon
      (W := W) (n := (2 : ℤ) * (m : ℤ) + 1) (x := x) <| by
        simpa using hNoCommon ((2 : ℤ) * (m : ℤ) + 1)

  exact ⟨
    h2m_ne,
    xPair_double_sameP1
      (W := W) (m := m) (x := x)
      (h4 := h4) (hψ_ne := hψ_ne) (hc3 := hc3),
    h2m1_ne,
    xPair_diffAdd_sameP1
      (W := W) (m := m) (x := x)
      (h4 := h4) (hψ_ne := hψ_ne) (hc3 := hc3)
  ⟩
```

## How to wire the surrounding theorem

At the call site, derive `hNoCommon` once from the existing no-common-root lemma around L1180, then pass it to the core.  The shape should be:

```lean
  have hNoCommon : ∀ n : ℤ,
      ¬ ((W.Φ n).eval x = 0 ∧ (W.ΨSq n).eval x = 0) := by
    intro n
    -- Replace this identifier with the actual L1180 theorem/lemma name.
    exact xPair_no_common_vanishing_of_isElliptic
      (W := W) (hW := hW) (n := n) (x := x)

  exact xPair_double_and_diffAddOrInf_EDS_core
    (W := W) (m := m) (x := x)
    (h4 := h4) (hψ_ne := hψ_ne) (hc3 := hc3)
    (hNoCommon := hNoCommon)
```

If the only existing L1180 theorem is already the vector nonzero statement

```lean
xPair_ne_zero_of_isElliptic ... : xPair W n x ≠ 0
```

then you can skip `hNoCommon` entirely and make the core carry the two nonzero facts directly:

```lean
(h2m_ne  : xPair W (2*m) x ≠ 0)
(h2m1_ne : xPair W (2*m+1) x ≠ 0)
```

but that is less aligned with the prompt's request to discharge the nonzero conjuncts from the no-common-vanishing statement.

## Minimal alternative: carry only the two no-common instances

If you want the smallest possible core signature, replace the universal `hNoCommon` with only the two instances used by this `m`:

```lean
(hNoCommon_2m :
  ¬ ((W.Φ (((2*m : ℕ) : ℤ))).eval x = 0 ∧
     (W.ΨSq (((2*m : ℕ) : ℤ))).eval x = 0))
(hNoCommon_2m1 :
  ¬ ((W.Φ (((2*m+1 : ℕ) : ℤ))).eval x = 0 ∧
     (W.ΨSq (((2*m+1 : ℕ) : ℤ))).eval x = 0))
```

Then the two nonzero proofs are simply:

```lean
  have h2m_ne : xPair W (2*m) x ≠ 0 :=
    xPair_ne_zero_of_noCommon (W := W) (n := 2*m) (x := x) hNoCommon_2m

  have h2m1_ne : xPair W (2*m+1) x ≠ 0 :=
    xPair_ne_zero_of_noCommon (W := W) (n := 2*m+1) (x := x) hNoCommon_2m1
```

I prefer the universal `hNoCommon` core parameter because it matches the surrounding `IsElliptic`/preΨ' theorem shape and keeps the call site less noisy.
