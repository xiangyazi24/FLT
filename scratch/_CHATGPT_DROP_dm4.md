# Q55 (dm4): Keystone avenue (d) — core sorry discharge

This answer works from the pasted `KeystoneLadder.lean` / `KeystoneSameP1.lean` source, treating it as authoritative.

## Q1. How to supply `h4`, `hψ_ne`, and `hc3`

The cleanest interface is **not** to put only `[CharZero k]` on the private core.  The correct core should carry the hypotheses actually consumed by the SameP1 lemmas:

```lean
(h4 : (4 : k) ≠ 0)
(hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
(hc3 : W.Ψ₃ ≠ 0)
```

Reason:

* `[W.IsElliptic]` does not imply `h4`; elliptic curves exist in characteristic `2`.
* `[W.IsElliptic]` does not imply `hc3`; in characteristic `3`, the leading coefficient obstruction for `Ψ₃` can disappear.
* `[CharZero k]` gives `h4` immediately, and it should give `hc3` either by a degree/leading-coefficient lemma for `Ψ₃` or from `hψ_ne` at `3`, but `[CharZero k]` by itself still does not give the exact `hψ_ne` hypothesis unless you have a non-circular division-polynomial nonvanishing theorem available.

So the robust design is:

1. strengthen the private core with `h4`, `hψ_ne`, `hc3`;
2. strengthen `xLadderPair_same_xPair_EDS` with the same three hypotheses;
3. propagate the same three hypotheses through any intermediate wrappers until the first theorem that is genuinely specialized to a characteristic-zero context such as `ℚ`;
4. at the `ℚ` caller, set `h4` by `norm_num`, set `hψ_ne` using a non-circular division-polynomial nonzero theorem if available, and derive/pass `hc3`.

A `[CharZero k]` convenience wrapper is fine later, but the theorem that actually discharges the sorry should remain hypothesis-explicit.  This keeps the mathematical assumptions visible and avoids hiding the real dependency on `hψ_ne`.

## Q2. Is `hψ_ne` derivable from `[W.IsElliptic] + [CharZero k]`?

Mathematically, over a characteristic-zero field, division polynomials are nonzero for every nonzero index.  For this patch, however, do **not** assume that Lean can synthesize

```lean
∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0
```

from `[W.IsElliptic] [CharZero k]` unless you have an explicit, non-circular theorem for it in Mathlib or your scratch development.  The avenue-(d) core should therefore thread `hψ_ne` explicitly.

If your local API contains a theorem like one of the following, use it only at the first characteristic-zero/Q caller, not inside the core:

```lean
-- schematic only: adjust to the actual local theorem name/signature
have hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0 := by
  intro n hn
  exact WeierstrassCurve.ψ_ne_zero (W := W) n hn
```

or, if the theorem is stated using the cast condition:

```lean
-- schematic only
have hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0 := by
  intro n hn
  exact WeierstrassCurve.ψ_ne_zero (W := W) (n := n) (by exact_mod_cast hn)
```

Do **not** use `xPair_ne_zero_of_isElliptic` for this.  Per the pasted dependency note, that theorem is downstream of the keystone and would be circular.

## Q3. Is `hc3 : W.Ψ₃ ≠ 0` derivable in characteristic zero?

Yes, mathematically.  `Ψ₃` has leading coefficient `3`, so over a characteristic-zero domain it is nonzero.  In Lean, use whichever of these is available locally:

1. a direct degree/leading-coefficient theorem for `W.Ψ₃` or for `W.ΨSq 3`/`W.preΨ 3`;
2. a simplification of `W.ψ 3` from `hψ_ne`:

```lean
-- Use this if local simp unfolds `W.ψ 3` to `Polynomial.C W.Ψ₃`.
private lemma Ψ₃_ne_zero_of_ψ_ne
    (W : WeierstrassCurve k)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) :
    W.Ψ₃ ≠ 0 := by
  intro h3
  have hψ3 : W.ψ (3 : ℤ) ≠ 0 := hψ_ne 3 (by norm_num)
  apply hψ3
  simpa [WeierstrassCurve.ψ, h3]
```

If that `simpa` is brittle in your local Mathlib version, keep `hc3` explicit all the way to the caller and discharge it there with the local degree theorem.  The core proof below only needs `hc3` as an input.

## Avenue-(c) consumer patch in `KeystoneSameP1.lean`

Because `Φ_ΨSq_no_common_eval_zero_odd` requires `[W.IsElliptic]`, the consumer lemma and the two diff-add SameP1 lemmas that call it should gain `[W.IsElliptic]`.

```lean
namespace KeystoneLadder
namespace XOnly

/-- If differential-addition hits the infinity branch, the target odd `Φ` coordinate is
nonzero.  The final step is now the avenue-(c) no-common-root theorem, not the keystone
ladder theorem, so this is non-circular. -/
theorem xPair_odd_phi_eval_ne_zero_of_delta_zero
    (W : WeierstrassCurve k) [W.IsElliptic] (m : ℤ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0)
    (hδ : deltaVec (xPair W (m + 1) x) (xPair W m x) = 0) :
    (W.Φ (2 * m + 1)).eval x ≠ 0 := by
  have hΨzero : (W.ΨSq (2 * m + 1)).eval x = 0 := by
    calc
      (W.ΨSq (2 * m + 1)).eval x
          = (deltaVec (xPair W (m + 1) x) (xPair W m x)) ^ 2 :=
            ΨSq_two_mul_add_one_eval_deltaVec_sq
              (W := W) (m := m) (x := x) h4 hψ_ne hc3
      _ = 0 := by simp [hδ]
  intro hΦzero
  exact
    (Φ_ΨSq_no_common_eval_zero_odd
      (W := W) (x := x) (h4 := h4) (m := m))
      ⟨hΦzero, hΨzero⟩

/-- Keystone x-only differential-addition wiring lemma. -/
theorem xPair_diffAdd_sameP1
    (W : WeierstrassCurve k) [W.IsElliptic] (m : ℤ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    SameP1Vec
      (diffAddOrInfVec (E := W⁄k)
        (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x))
      (xPair W (2 * m + 1) x) := by
  refine xPair_diffAdd_sameP1_of_inf_phi_ne
    (W := W) (m := m) (x := x) h4 hψ_ne hc3 ?_
  intro hδ
  exact xPair_odd_phi_eval_ne_zero_of_delta_zero
    (W := W) (m := m) (x := x) h4 hψ_ne hc3 hδ

/-- Core-order (A = xPair m, B = xPair (m+1)) differential-addition wiring, obtained from
`xPair_diffAdd_sameP1` by the symmetry above. -/
theorem xPair_diffAdd_sameP1_core_order
    (W : WeierstrassCurve k) [W.IsElliptic] (m : ℤ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    SameP1Vec
      (diffAddOrInfVec (E := W⁄k)
        (xPair W m x) (xPair W (m + 1) x) (xPair W 1 x))
      (xPair W (2 * m + 1) x) := by
  rw [diffAddOrInfVec_comm]
  exact xPair_diffAdd_sameP1 (W := W) (m := m) (x := x) h4 hψ_ne hc3

end XOnly
end KeystoneLadder
```

## Even no-common-root theorem shape needed from `KeystoneCoprimality.lean`

For the avenue-(d) core, do not expose any internal even-index formula.  Export the same no-common-root shape as the odd theorem:

```lean
theorem Φ_ΨSq_no_common_eval_zero_even
    (W : WeierstrassCurve k) [W.IsElliptic] (x : k)
    (h4 : (4 : k) ≠ 0) (m : ℤ) :
    ¬ ((W.Φ (2 * m)).eval x = 0 ∧
       (W.ΨSq (2 * m)).eval x = 0)
```

Internally this is the even branch of the same no-adjacent-`preΨ` argument.  The only fact the ladder core needs is the exported theorem above.

## Avenue-(d) patch in `KeystoneLadder.lean`

Add the imports for the two split files if they are not already imported by the scratch file.  The exact import prefix may differ depending on how the scratch directory is exposed to Lake; the important dependencies are `KeystoneSameP1` and `KeystoneCoprimality`.

```lean
import Mathlib.Tactic
-- import scratch.KeystoneSameP1
-- import scratch.KeystoneCoprimality
```

Paste the following helper near `xPair` and before `xPair_double_and_diffAddOrInf_EDS_core`.

```lean
namespace KeystoneLadder
namespace XOnly

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
```

Replace the core theorem by this strengthened version.

```lean
private theorem xPair_double_and_diffAddOrInf_EDS_core
    (W : WeierstrassCurve k) [W.IsElliptic] (m : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    xPair W ((2 * m : ℕ) : ℤ) x ≠ 0 ∧
    SameP1Vec
      (XOnly.doubleVec (E := W⁄k) (xPair W (m : ℤ) x))
      (xPair W ((2 * m : ℕ) : ℤ) x) ∧
    xPair W ((2 * m + 1 : ℕ) : ℤ) x ≠ 0 ∧
    SameP1Vec
      (XOnly.diffAddOrInfVec (E := W⁄k)
        (xPair W (m : ℤ) x)
        (xPair W ((m + 1 : ℕ) : ℤ) x)
        (xPair W (1 : ℤ) x))
      (xPair W ((2 * m + 1 : ℕ) : ℤ) x) := by
  have h2m_no_common :
      ¬ ((W.Φ (2 * (m : ℤ))).eval x = 0 ∧
         (W.ΨSq (2 * (m : ℤ))).eval x = 0) := by
    simpa using
      (Φ_ΨSq_no_common_eval_zero_even
        (W := W) (x := x) (h4 := h4) (m := (m : ℤ)))

  have h2m_ne : xPair W ((2 * m : ℕ) : ℤ) x ≠ 0 := by
    refine xPair_ne_zero_of_Φ_ΨSq_no_common
      (W := W) (n := ((2 * m : ℕ) : ℤ)) (x := x) ?_
    simpa using h2m_no_common

  have h2m1_no_common :
      ¬ ((W.Φ (2 * (m : ℤ) + 1)).eval x = 0 ∧
         (W.ΨSq (2 * (m : ℤ) + 1)).eval x = 0) := by
    simpa using
      (Φ_ΨSq_no_common_eval_zero_odd
        (W := W) (x := x) (h4 := h4) (m := (m : ℤ)))

  have h2m1_ne : xPair W ((2 * m + 1 : ℕ) : ℤ) x ≠ 0 := by
    refine xPair_ne_zero_of_Φ_ΨSq_no_common
      (W := W) (n := ((2 * m + 1 : ℕ) : ℤ)) (x := x) ?_
    simpa using h2m1_no_common

  have hdouble_int :
      SameP1Vec
        (XOnly.doubleVec (E := W⁄k) (xPair W (m : ℤ) x))
        (xPair W (2 * (m : ℤ)) x) := by
    exact
      xPair_double_sameP1
        (W := W) (m := (m : ℤ)) (x := x)
        h4 hψ_ne hc3

  have hdouble :
      SameP1Vec
        (XOnly.doubleVec (E := W⁄k) (xPair W (m : ℤ) x))
        (xPair W ((2 * m : ℕ) : ℤ) x) := by
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
        h4 hψ_ne hc3

  have hdiff :
      SameP1Vec
        (XOnly.diffAddOrInfVec (E := W⁄k)
          (xPair W (m : ℤ) x)
          (xPair W ((m + 1 : ℕ) : ℤ) x)
          (xPair W (1 : ℤ) x))
        (xPair W ((2 * m + 1 : ℕ) : ℤ) x) := by
    simpa using hdiff_int

  exact ⟨h2m_ne, hdouble, h2m1_ne, hdiff⟩
```

The three `simpa` casts use the standard simp normal forms:

```lean
((2 * m : ℕ) : ℤ)     = 2 * (m : ℤ)
((2 * m + 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 1
((m + 1 : ℕ) : ℤ)     = (m : ℤ) + 1
```

If a local simp set is too weak, insert these before the relevant `simpa` calls:

```lean
  have h2m_cast : ((2 * m : ℕ) : ℤ) = 2 * (m : ℤ) := by
    norm_num
  have h2m1_cast : ((2 * m + 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 1 := by
    norm_num
  have hm1_cast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by
    norm_num
```

and then use `simpa [h2m_cast, h2m1_cast, hm1_cast] using ...`.

## Signature change for the immediate caller

Change `xLadderPair_same_xPair_EDS` to thread the same three hypotheses.

```lean
private theorem xLadderPair_same_xPair_EDS
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    xPair W (n : ℤ) x ≠ 0 ∧
    xPair W ((n + 1 : ℕ) : ℤ) x ≠ 0 ∧
    SameP1Vec
      (XOnly.xLadderPair (E := W⁄k) x n).1
      (xPair W (n : ℤ) x) ∧
    SameP1Vec
      (XOnly.xLadderPair (E := W⁄k) x n).2
      (xPair W ((n + 1 : ℕ) : ℤ) x) := by
    classical
    have hD :
        SameP1Vec (XOnly.xAffVec x) (xPair W (1 : ℤ) x) := by
      simpa [xPair, XOnly.xAffVec] using SameP1Vec.refl (![x, 1] : Fin 2 → k)
    induction n using Nat.strong_induction_on with
    | h n IH =>
        rcases n with _ | n
        · constructor
          · simp [xPair]
          · constructor
            · simp [xPair]
            · constructor
              · simpa [XOnly.xLadderPair, xPair, XOnly.xInfVec] using
                  SameP1Vec.refl (![1, 0] : Fin 2 → k)
              · simpa [XOnly.xLadderPair] using hD
        · rcases n with _ | n
          · have hcore :=
              xPair_double_and_diffAddOrInf_EDS_core
                (W := W) (m := 1) (x := x) h4 hψ_ne hc3
            have hdouble :
                SameP1Vec
                  (XOnly.doubleVec (E := W⁄k) (XOnly.xAffVec x))
                  (xPair W (2 : ℤ) x) := by
              exact SameP1Vec.trans (XOnly.doubleVec_congr (E := W⁄k) hD) hcore.2.1
            constructor
            · simp [xPair]
            · constructor
              · simpa using hcore.1
              · constructor
                · simpa [XOnly.xLadderPair] using hD
                · simpa [XOnly.xLadderPair] using hdouble
          · let N : ℕ := n + 2
            let m : ℕ := N / 2
            change
              xPair W (N : ℤ) x ≠ 0 ∧
              xPair W ((N + 1 : ℕ) : ℤ) x ≠ 0 ∧
              SameP1Vec
                (XOnly.xLadderPair (E := W⁄k) x N).1
                (xPair W (N : ℤ) x) ∧
              SameP1Vec
                (XOnly.xLadderPair (E := W⁄k) x N).2
                (xPair W ((N + 1 : ℕ) : ℤ) x)
            -- keep the existing proof, but update every core call as follows:
            --
            --   have hcore :=
            --     xPair_double_and_diffAddOrInf_EDS_core
            --       (W := W) (m := m) (x := x) h4 hψ_ne hc3
            --
            -- and keep recursive `IH` calls unchanged; `h4`, `hψ_ne`, and `hc3`
            -- are fixed parameters of this theorem and remain in scope.
            all_goals sorry
```

The final `all_goals sorry` is not part of the patch; it marks where the pasted source cuts off.  In the real file, keep the existing proof after `have hm_lt : m < N := ...` and only change calls of

```lean
xPair_double_and_diffAddOrInf_EDS_core (W := W) ...
```

to

```lean
xPair_double_and_diffAddOrInf_EDS_core (W := W) ... h4 hψ_ne hc3
```

## Propagation to the first `ℚ` caller

Every theorem that calls `xLadderPair_same_xPair_EDS` must either gain the same three explicit hypotheses or be specialized enough to prove them internally.  The mechanical generic propagation is:

```lean
(h4 : (4 : k) ≠ 0)
(hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
(hc3 : W.Ψ₃ ≠ 0)
```

At the first rational caller, discharge as follows:

```lean
  have h4 : (4 : ℚ) ≠ 0 := by norm_num

  -- Use your non-circular division-polynomial nonvanishing theorem here.
  have hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0 := by
    intro n hn
    -- Replace with the actual local/Mathlib theorem.
    exact WeierstrassCurve.ψ_ne_zero (W := W) n hn

  have hc3 : W.Ψ₃ ≠ 0 := by
    -- Prefer deriving this from a local degree/leading-coefficient theorem.
    -- If `W.ψ 3` unfolds to `Polynomial.C W.Ψ₃`, this also works:
    intro h3
    have hψ3 : W.ψ (3 : ℤ) ≠ 0 := hψ_ne 3 (by norm_num)
    apply hψ3
    simpa [WeierstrassCurve.ψ, h3]

  have hladder :=
    xLadderPair_same_xPair_EDS
      (W := W) (n := n) (x := x) h4 hψ_ne hc3
```

If `WeierstrassCurve.ψ_ne_zero` is not present under that name/signature, keep `hψ_ne` as an explicit top-level hypothesis until you add the non-circular theorem.  The avenue-(d) proof does not depend on how `hψ_ne` is proved.

## Minimal call-site summary

The actual sorry at `xPair_double_and_diffAddOrInf_EDS_core` is discharged by exactly these four ingredients:

```lean
xPair_ne_zero_of_Φ_ΨSq_no_common ... (Φ_ΨSq_no_common_eval_zero_even ...)
xPair_double_sameP1 ... h4 hψ_ne hc3
xPair_ne_zero_of_Φ_ΨSq_no_common ... (Φ_ΨSq_no_common_eval_zero_odd ...)
xPair_diffAdd_sameP1_core_order ... h4 hψ_ne hc3
```

This avoids the circular theorem `xPair_ne_zero_of_isElliptic` entirely.
