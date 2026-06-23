# Q14 (dm3): Keystone x-only differential-addition wiring lemma

## Bottom line

The `deltaVec ≠ 0` branch should use scalar `c = 1`.  After evaluating

```lean
WeierstrassCurve.diffAdd_projective_two_mul_add_one
WeierstrassCurve.ΨSq_two_mul_add_one
```

at `x`, the second identity identifies the evaluated denominator with
`(deltaVec (xPair W (m+1) x) (xPair W m x))^2`.  The nonzero branch makes this
square nonzero, so the projective identity cancels the denominator and gives
componentwise equality with `diffAddVec`.

The `deltaVec = 0` branch has one extra mathematical obligation.  From
`ΨSq_two_mul_add_one` it gives

```lean
(W.ΨSq (2*m+1)).eval x = 0
```

so `xPair W (2*m+1) x` has zero `Z`-coordinate.  But to prove

```lean
SameP1Vec xInfVec (xPair W (2*m+1) x)
```

with `SameP1Vec u v := ∃ c, c ≠ 0 ∧ v = c • u`, the witness must be

```lean
c = (W.Φ (2*m+1)).eval x
```

and therefore one also needs

```lean
(W.Φ (2*m+1)).eval x ≠ 0.
```

This nonzero fact is not a consequence of the projective diff-add identity
alone: if both evaluated components were zero, the goal would become
`∃ c ≠ 0, ![0, 0] = c • ![1, 0]`, which is impossible.  Thus the exact requested
lemma is obtained from the wiring proof below plus a local no-common-root / valid
projective-pair lemma for `(Φ n, ΨSq n)`.

The code below is the drop-in wiring proof.  It isolates the only non-wiring fact
as the hypothesis `hΦinf`; once you have the no-common-root lemma, the final
wrapper has exactly the requested statement.

---

## 1. Eval bridge lemmas

Put these near the existing `dupNumP_eval`-style lemmas.  The argument order is
chosen to match the ladder call

```lean
A = xPair W (m+1) x
B = xPair W m x
D = xPair W 1 x
```

whereas the projective certificate is stated in the polynomial order
`m, m+1`.  This is why `deltaP` evaluates to `-deltaVec`; the denominator uses a
square, so the sign disappears.

```lean
namespace KeystoneLadder
namespace XOnly

open Polynomial

variable {k : Type*} [Field k]

@[simp] theorem xPair_one_X (W : WeierstrassCurve k) (x : k) :
    X (xPair W 1 x) = x := by
  simp [xPair, X]

@[simp] theorem xPair_one_Z (W : WeierstrassCurve k) (x : k) :
    Z (xPair W 1 x) = 1 := by
  simp [xPair, Z]

/--
The projective `deltaP` is in the order `(m, m+1)`, while the ladder step below
passes vectors in the order `(m+1, m)`.  Hence the minus sign.
-/
theorem deltaP_eval_xPair_succ_left
    (W : WeierstrassCurve k) (m : ℤ) (x : k) :
    ((WeierstrassCurve.deltaP W
        (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
      = - deltaVec (xPair W (m + 1) x) (xPair W m x) := by
  simp [WeierstrassCurve.deltaP, deltaVec, xPair, X, Z]
  ring

/-- Evaluated projective denominator equals the ladder delta square. -/
theorem diffAddDenP_eval_xPair_succ_left
    (W : WeierstrassCurve k) (m : ℤ) (x : k) :
    ((WeierstrassCurve.diffAddDenP W
        (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
      = (deltaVec (xPair W (m + 1) x) (xPair W m x)) ^ 2 := by
  simp [WeierstrassCurve.diffAddDenP, deltaP_eval_xPair_succ_left]

/--
Evaluated projective numerator without the `- delta^2 * X` correction.
The `ring` call absorbs both the swap symmetry in `A,B` and the base-change
coefficient reductions.
-/
theorem sumNumP_eval_xPair_succ_left
    (W : WeierstrassCurve k) (m : ℤ) (x : k) :
    ((WeierstrassCurve.sumNumP W
        (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
      = sumNumVec (E := W⁄k) (xPair W (m + 1) x) (xPair W m x) := by
  simp [WeierstrassCurve.sumNumP, sumNumVec, xPair, X, Z,
    WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
    Algebra.algebraMap_self_apply]
  ring

/-- Evaluated projective diff-add numerator is the `X`-coordinate of `diffAddVec`. -/
theorem diffAddNumP_eval_xPair_succ_left
    (W : WeierstrassCurve k) (m : ℤ) (x : k) :
    ((WeierstrassCurve.diffAddNumP W
        (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
      = X (diffAddVec (E := W⁄k)
          (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x)) := by
  simp [WeierstrassCurve.diffAddNumP, WeierstrassCurve.sumNumP,
    WeierstrassCurve.deltaP, diffAddVec, sumNumVec, deltaVec, xPair, X, Z,
    WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
    Algebra.algebraMap_self_apply]
  ring

/-- Evaluated projective diff-add denominator is the `Z`-coordinate of `diffAddVec`. -/
theorem diffAddVec_Z_xPair_succ_left
    (W : WeierstrassCurve k) (m : ℤ) (x : k) :
    Z (diffAddVec (E := W⁄k)
        (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x))
      = ((WeierstrassCurve.diffAddDenP W
          (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
  simp [WeierstrassCurve.diffAddDenP, WeierstrassCurve.deltaP,
    diffAddVec, deltaVec, xPair, X, Z]
  ring
```

If `simp` does not unfold your local `W⁄k` notation far enough in the two
numerator bridge lemmas, add the exact base-change simp lemmas already used by
`xPair_double_sameP1`; the intended normalization is the same:

```lean
simp [WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
  Algebra.algebraMap_self_apply]
```

---

## 2. The wiring theorem with the infinity-branch nonzero fact isolated

This theorem is the complete branch split and all x-only wiring.  It needs only
one non-wiring input, `hΦinf`, precisely for the `xInfVec` branch.

```lean
/--
Differential-addition wiring for x-only ladder pairs, with the only required
infinity-branch nondegeneracy isolated as `hΦinf`.

The nonzero-delta branch uses scalar `1`.  The zero-delta branch uses scalar
`(W.Φ (2*m+1)).eval x`, so `hΦinf` is exactly the fact needed to rule out the
all-zero projective pair.
-/
theorem xPair_diffAdd_sameP1_of_inf_phi_ne
    (W : WeierstrassCurve k) (m : ℤ) (x : k)
    (h4) (hψ_ne) (hc3)
    (hΦinf :
      deltaVec (xPair W (m + 1) x) (xPair W m x) = 0 →
        (W.Φ (2 * m + 1)).eval x ≠ 0) :
    SameP1Vec
      (diffAddOrInfVec (E := W⁄k)
        (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x))
      (xPair W (2 * m + 1) x) := by
  by_cases hδ : deltaVec (xPair W (m + 1) x) (xPair W m x) = 0
  · rw [diffAddOrInfVec, if_pos hδ]

    have hΨzero : (W.ΨSq (2 * m + 1)).eval x = 0 := by
      have hDenPoly :=
        WeierstrassCurve.ΨSq_two_mul_add_one W h4 hψ_ne hc3 m
      have hDenEval :
          (W.ΨSq (2 * m + 1)).eval x
            = ((WeierstrassCurve.diffAddDenP W
                (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
        simpa using congrArg (fun p : Polynomial k => p.eval x) hDenPoly
      calc
        (W.ΨSq (2 * m + 1)).eval x
            = ((WeierstrassCurve.diffAddDenP W
                (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := hDenEval
        _ = (deltaVec (xPair W (m + 1) x) (xPair W m x)) ^ 2 := by
              rw [diffAddDenP_eval_xPair_succ_left]
        _ = 0 := by simp [hδ]

    refine ⟨(W.Φ (2 * m + 1)).eval x, hΦinf hδ, ?_⟩
    funext i
    fin_cases i <;> simp [xPair, xInfVec, hΨzero]

  · rw [diffAddOrInfVec, if_neg hδ]

    have hΨDen :
        (W.ΨSq (2 * m + 1)).eval x
          = ((WeierstrassCurve.diffAddDenP W
              (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
      have hDenPoly :=
        WeierstrassCurve.ΨSq_two_mul_add_one W h4 hψ_ne hc3 m
      simpa using congrArg (fun p : Polynomial k => p.eval x) hDenPoly

    have hDenNe :
        ((WeierstrassCurve.diffAddDenP W
          (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) ≠ 0 := by
      rw [diffAddDenP_eval_xPair_succ_left]
      exact pow_ne_zero 2 hδ

    have hProjEval :
        (W.Φ (2 * m + 1)).eval x *
            ((WeierstrassCurve.diffAddDenP W
              (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
          = (W.ΨSq (2 * m + 1)).eval x *
            ((WeierstrassCurve.diffAddNumP W
              (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
      have hProjPoly :=
        WeierstrassCurve.diffAdd_projective_two_mul_add_one W h4 hψ_ne hc3 m
      simpa using congrArg (fun p : Polynomial k => p.eval x) hProjPoly

    have hΦNum :
        (W.Φ (2 * m + 1)).eval x
          = ((WeierstrassCurve.diffAddNumP W
              (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
      exact mul_right_cancel₀ hDenNe <| by
        calc
          (W.Φ (2 * m + 1)).eval x *
              ((WeierstrassCurve.diffAddDenP W
                (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
              = (W.ΨSq (2 * m + 1)).eval x *
                ((WeierstrassCurve.diffAddNumP W
                  (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := hProjEval
          _ = ((WeierstrassCurve.diffAddDenP W
                (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) *
                ((WeierstrassCurve.diffAddNumP W
                  (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
                rw [hΨDen]
          _ = ((WeierstrassCurve.diffAddNumP W
                (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) *
                ((WeierstrassCurve.diffAddDenP W
                  (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
                ring

    have hXcoord :
        (W.Φ (2 * m + 1)).eval x
          = X (diffAddVec (E := W⁄k)
              (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x)) := by
      exact hΦNum.trans
        (diffAddNumP_eval_xPair_succ_left (W := W) (m := m) (x := x))

    have hZcoord :
        (W.ΨSq (2 * m + 1)).eval x
          = Z (diffAddVec (E := W⁄k)
              (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x)) := by
      exact hΨDen.trans
        (diffAddVec_Z_xPair_succ_left (W := W) (m := m) (x := x)).symm

    refine ⟨1, one_ne_zero, ?_⟩
    funext i
    fin_cases i
    · simpa [xPair, X, one_smul] using hXcoord
    · simpa [xPair, Z, one_smul] using hZcoord
```

---

## 3. Exact requested wrapper

Once the local no-common-root / valid-pair theorem is available, use this wrapper
for the exact statement requested in the task.

The cleanest root-separation theorem to prove separately is either the direct
`deltaVec` version

```lean
theorem xPair_odd_phi_eval_ne_zero_of_delta_zero
    (W : WeierstrassCurve k) (m : ℤ) (x : k)
    (h4) (hψ_ne) (hc3)
    (hδ : deltaVec (xPair W (m + 1) x) (xPair W m x) = 0) :
    (W.Φ (2 * m + 1)).eval x ≠ 0
```

or the more reusable denominator-root version

```lean
theorem Φ_eval_ne_zero_of_ΨSq_eval_eq_zero
    (W : WeierstrassCurve k) (n : ℤ) (x : k)
    (h4) (hψ_ne) (hc3)
    (hΨ : (W.ΨSq n).eval x = 0) :
    (W.Φ n).eval x ≠ 0
```

With the direct `deltaVec` theorem, the requested lemma is exactly:

```lean
/-- Keystone x-only differential-addition wiring lemma. -/
theorem xPair_diffAdd_sameP1
    (W : WeierstrassCurve k) (m : ℤ) (x : k)
    (h4) (hψ_ne) (hc3) :
    SameP1Vec
      (diffAddOrInfVec (E := W⁄k)
        (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x))
      (xPair W (2 * m + 1) x) := by
  refine xPair_diffAdd_sameP1_of_inf_phi_ne
    (W := W) (m := m) (x := x) h4 hψ_ne hc3 ?_
  intro hδ
  exact xPair_odd_phi_eval_ne_zero_of_delta_zero
    (W := W) (m := m) (x := x) h4 hψ_ne hc3 hδ

end XOnly
end KeystoneLadder
```

If you prove the reusable `ΨSq`-root version instead, the wrapper’s final block is:

```lean
  intro hδ
  have hΨzero : (W.ΨSq (2 * m + 1)).eval x = 0 := by
    have hDenPoly :=
      WeierstrassCurve.ΨSq_two_mul_add_one W h4 hψ_ne hc3 m
    have hDenEval :
        (W.ΨSq (2 * m + 1)).eval x
          = ((WeierstrassCurve.diffAddDenP W
              (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
      simpa using congrArg (fun p : Polynomial k => p.eval x) hDenPoly
    calc
      (W.ΨSq (2 * m + 1)).eval x
          = ((WeierstrassCurve.diffAddDenP W
              (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := hDenEval
      _ = (deltaVec (xPair W (m + 1) x) (xPair W m x)) ^ 2 := by
            rw [diffAddDenP_eval_xPair_succ_left]
      _ = 0 := by simp [hδ]
  exact Φ_eval_ne_zero_of_ΨSq_eval_eq_zero
    (W := W) (n := 2 * m + 1) (x := x) h4 hψ_ne hc3 hΨzero
```

---

## 4. Why the extra no-common-root fact is necessary

The infinity branch rewrites the left side to `xInfVec = ![1,0]`.  The goal is

```lean
∃ c, c ≠ 0 ∧ xPair W (2*m+1) x = c • ![1,0].
```

The `Z` component follows from

```lean
ΨSq(2*m+1) = diffAddDenP = deltaP^2
```

and `deltaVec = 0`.  The `X` component then forces `c = Φ(2*m+1).eval x`, so the
nonzero proof for this exact scalar is unavoidable.  The all-zero projective pair
cannot be made equivalent to `xInfVec` under this definition of `SameP1Vec`.
