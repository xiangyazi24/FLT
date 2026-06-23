# Q20 (dm4): Keystone final assembly — nonzero facts and core assembly

## What I could and could not inspect

I re-checked the requested repository/branch before writing this answer.  The connector still returns `404` for

```text
scratch/KeystoneLadder.lean
```

on `xiangyazi24/FLT@scratch`.  Code search for the concrete names

```text
KeystoneLadder.lean
xPair_double_and_diffAddOrInf_EDS_core
xPair_double_sameP1
```

also returned no results, and PR search for those names returned no results.  A local `git clone` was not possible from this environment because DNS resolution for `github.com` failed.  So I could not literally read L960–1060 or L1160–1200, nor compile this patch in the branch.

The Lean below is therefore written in the exact shape needed by the prompt, but with one expected local adjustment: replace the placeholder no-common-root lemma at the call site by the actual theorem name already present around L1180.

## Hypotheses the core lemma should carry

The core assembly itself should carry these hypotheses:

```lean
(h4 : (4 : k) ≠ 0)
(hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
(hc3 : W.Ψ₃ ≠ 0)
(hNoCommon : ∀ n : ℤ,
  ¬ ((W.Φ n).eval x = 0 ∧ (W.ΨSq n).eval x = 0))
```

Reason:

* `h4`, `hψ_ne`, and `hc3` are exactly the hypotheses requested by the two projective lemmas `xPair_double_sameP1` and `xPair_diffAdd_sameP1`.
* `hNoCommon` is exactly what proves the two vector nonzero facts.
* Do **not** silently derive `h4 : (4 : k) ≠ 0` from `IsElliptic W`.  Nonsingularity alone does not exclude characteristic `2`.
* `hc3` may be derivable from `hψ_ne` by specializing `hψ_ne 3`, if the local simplifier unfolds `W.ψ 3` to `Polynomial.C W.Ψ₃`.  Since the two SameP1 lemmas currently ask for `hc3`, the safest core interface keeps it explicit and lets the call site derive it if desired.

The surrounding theorem should derive `hNoCommon` from the existing L1180/preΨ'-based no-common-root lemma, likely using its `IsElliptic W` hypothesis.  That keeps this core lemma purely an assembly lemma.

## Helper: no common vanishing implies the `Fin 2` vector is nonzero

Paste this inside `namespace KeystoneLadder` / `namespace XOnly`, near `xPair` and before the core lemma.  This version assumes `xPair` is integer-indexed, which is the most likely local declaration because Mathlib's `Φ` and `ΨSq` are integer-indexed.

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

If the actual file declares `xPair` with `n : ℕ`, use this Nat-indexed helper instead:

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

The proof is just coordinate extraction from the function equality `xPair W n x = 0`: evaluating at `(0 : Fin 2)` gives `(W.Φ n).eval x = 0`, and evaluating at `(1 : Fin 2)` gives `(W.ΨSq n).eval x = 0`.

## Finished core lemma: integer-indexed `xPair` version

Use this if the local `xPair` has second argument `n : ℤ`.

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
  have h2m_ne' : xPair W ((2 : ℤ) * (m : ℤ)) x ≠ 0 :=
    xPair_ne_zero_of_noCommon
      (W := W) (n := (2 : ℤ) * (m : ℤ)) (x := x)
      (hNoCommon ((2 : ℤ) * (m : ℤ)))
  have h2m_ne : xPair W (2*m) x ≠ 0 := by
    simpa using h2m_ne'

  have h2m1_ne' : xPair W ((2 : ℤ) * (m : ℤ) + 1) x ≠ 0 :=
    xPair_ne_zero_of_noCommon
      (W := W) (n := (2 : ℤ) * (m : ℤ) + 1) (x := x)
      (hNoCommon ((2 : ℤ) * (m : ℤ) + 1))
  have h2m1_ne : xPair W (2*m+1) x ≠ 0 := by
    simpa using h2m1_ne'

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

If the SameP1 lemmas live in namespace `XOnly`, qualify them as `XOnly.xPair_double_sameP1` and `XOnly.xPair_diffAdd_sameP1`.  If their hypotheses are positional rather than named, the last two fields become:

```lean
    xPair_double_sameP1 W m x h4 hψ_ne hc3,
    h2m1_ne,
    xPair_diffAdd_sameP1 W m x h4 hψ_ne hc3
```

## Finished core lemma: Nat-indexed `xPair` version

Use this only if the local declaration is `xPair W (n : ℕ) x`.

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

## Call-site wiring from the no-common-root lemma

At the theorem around L1160–1200, derive the no-common statement once and pass it into the core.  The placeholder below is the only expected local-name substitution.

```lean
  have hNoCommon : ∀ n : ℤ,
      ¬ ((W.Φ n).eval x = 0 ∧ (W.ΨSq n).eval x = 0) := by
    intro n
    -- Replace this with the actual theorem already present around L1180.
    -- It is the preΨ'-based / `xPair_ne_zero_of_isElliptic` no-common-root fact.
    exact xPair_no_common_vanishing_of_isElliptic
      (W := W) (hW := hW) (n := n) (x := x)

  exact xPair_double_and_diffAddOrInf_EDS_core
    (W := W) (m := m) (x := x)
    (h4 := h4) (hψ_ne := hψ_ne) (hc3 := hc3)
    (hNoCommon := hNoCommon)
```

If the existing L1180 result is named `xPair_ne_zero_of_isElliptic` and returns vector nonzero rather than the raw pair of equations, then it is better to leave this core lemma with explicit nonzero parameters instead:

```lean
(h2m_ne  : xPair W (2*m) x ≠ 0)
(h2m1_ne : xPair W (2*m+1) x ≠ 0)
```

But if the file truly already contains the raw no-common-vanishing statement described in the prompt, the `hNoCommon` version above is the direct implementation requested.

## Optional: derive `hc3` from `hψ_ne`

If the call site has `hψ_ne` but not `hc3`, this is the expected local proof shape:

```lean
  have hc3 : W.Ψ₃ ≠ 0 := by
    intro hzero
    have hψ3 : W.ψ (3 : ℤ) ≠ 0 := hψ_ne 3 (by norm_num)
    apply hψ3
    -- Depending on local simp lemmas, this may be just `simpa [WeierstrassCurve.ψ, hzero]`.
    simpa [WeierstrassCurve.ψ, hzero]
```

If that `simpa` is too weak, keep `hc3` explicit.  The core lemma above does not need to know how `hc3` was obtained.
