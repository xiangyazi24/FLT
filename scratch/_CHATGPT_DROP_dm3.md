# Q19 (dm3): Keystone x-only differential-addition wiring lemma

## Executive answer

The nonzero-delta branch is a pure wiring lemma and uses scalar `c = 1`.

The zero-delta branch cannot be completed from only

```lean
ΨSq_two_mul_add_one
 diffAdd_projective_two_mul_add_one
```

because those identities give only

```lean
(W.ΨSq (2*m+1)).eval x = 0
```

when `deltaVec = 0`.  To prove

```lean
SameP1Vec xInfVec (xPair W (2*m+1) x)
```

with

```lean
SameP1Vec u v := ∃ c, c ≠ 0 ∧ v = c • u
xInfVec = ![1, 0]
```

the only possible witness is

```lean
c = (W.Φ (2*m+1)).eval x
```

so the branch also needs

```lean
(W.Φ (2*m+1)).eval x ≠ 0.
```

Thus the fully compilable wiring theorem is the version below with that one
non-wiring fact isolated as `hΦinf`.  Once you prove or import the corresponding
no-common-root / valid-projective-pair lemma for `(Φ n, ΨSq n)`, the exact
requested wrapper is one line.

---

## Code to add in `scratch/KeystoneSameP1.lean`

Place this in namespace `KeystoneLadder.XOnly`, after the definitions and after
importing `scratch/KeystoneDiffAddCert.lean`.

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
The certificate uses projective order `(m, m+1)`, while the ladder step below
uses vector order `(m+1, m)`.  Hence the minus sign.  The denominator bridges use
only the square, so the sign disappears there.
-/
theorem deltaP_eval_xPair_succ_left
    (W : WeierstrassCurve k) (m : ℤ) (x : k) :
    ((WeierstrassCurve.deltaP W
        (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
      = - deltaVec (xPair W (m + 1) x) (xPair W m x) := by
  simp [WeierstrassCurve.deltaP, deltaVec, xPair, X, Z] <;> ring

/-- Evaluated projective denominator equals the ladder `deltaVec` square. -/
theorem diffAddDenP_eval_xPair_succ_left
    (W : WeierstrassCurve k) (m : ℤ) (x : k) :
    ((WeierstrassCurve.diffAddDenP W
        (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
      = (deltaVec (xPair W (m + 1) x) (xPair W m x)) ^ 2 := by
  simp [WeierstrassCurve.diffAddDenP, deltaP_eval_xPair_succ_left] <;> ring

/-- Evaluated `sumNumP`; the expression is symmetric in the two x-only inputs. -/
theorem sumNumP_eval_xPair_succ_left
    (W : WeierstrassCurve k) (m : ℤ) (x : k) :
    ((WeierstrassCurve.sumNumP W
        (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
      = sumNumVec (E := W⁄k) (xPair W (m + 1) x) (xPair W m x) := by
  simp [WeierstrassCurve.sumNumP, sumNumVec, xPair, X, Z,
    WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
    Algebra.algebraMap_self_apply] <;> ring

/-- Evaluated projective numerator equals the `X` component of the ladder diff-add. -/
theorem diffAddNumP_eval_xPair_succ_left
    (W : WeierstrassCurve k) (m : ℤ) (x : k) :
    ((WeierstrassCurve.diffAddNumP W
        (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
      = X (diffAddVec (E := W⁄k)
          (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x)) := by
  simp [WeierstrassCurve.diffAddNumP, WeierstrassCurve.sumNumP,
    WeierstrassCurve.deltaP, diffAddVec, sumNumVec, deltaVec, xPair, X, Z,
    WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
    Algebra.algebraMap_self_apply] <;> ring

/-- Evaluated projective denominator equals the `Z` component of the ladder diff-add. -/
theorem diffAddVec_Z_xPair_succ_left
    (W : WeierstrassCurve k) (m : ℤ) (x : k) :
    Z (diffAddVec (E := W⁄k)
        (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x))
      = ((WeierstrassCurve.diffAddDenP W
          (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
  simp [WeierstrassCurve.diffAddDenP, WeierstrassCurve.deltaP,
    diffAddVec, deltaVec, xPair, X, Z] <;> ring

/-- Evaluated `ΨSq_two_mul_add_one`, in denominator form. -/
theorem ΨSq_two_mul_add_one_eval_diffAddDenP
    (W : WeierstrassCurve k) (m : ℤ) (x : k) (h4) (hψ_ne) (hc3) :
    (W.ΨSq (2 * m + 1)).eval x
      = ((WeierstrassCurve.diffAddDenP W
          (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
  have h := WeierstrassCurve.ΨSq_two_mul_add_one W h4 hψ_ne hc3 m
  simpa using congrArg (fun p : Polynomial k => p.eval x) h

/-- Evaluated `ΨSq_two_mul_add_one`, directly in ladder-delta form. -/
theorem ΨSq_two_mul_add_one_eval_deltaVec_sq
    (W : WeierstrassCurve k) (m : ℤ) (x : k) (h4) (hψ_ne) (hc3) :
    (W.ΨSq (2 * m + 1)).eval x
      = (deltaVec (xPair W (m + 1) x) (xPair W m x)) ^ 2 := by
  calc
    (W.ΨSq (2 * m + 1)).eval x
        = ((WeierstrassCurve.diffAddDenP W
            (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
            exact ΨSq_two_mul_add_one_eval_diffAddDenP
              (W := W) (m := m) (x := x) h4 hψ_ne hc3
    _ = (deltaVec (xPair W (m + 1) x) (xPair W m x)) ^ 2 := by
            rw [diffAddDenP_eval_xPair_succ_left]

/-- Evaluated projective diff-add certificate. -/
theorem diffAdd_projective_two_mul_add_one_eval
    (W : WeierstrassCurve k) (m : ℤ) (x : k) (h4) (hψ_ne) (hc3) :
    (W.Φ (2 * m + 1)).eval x *
        ((WeierstrassCurve.diffAddDenP W
          (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
      = (W.ΨSq (2 * m + 1)).eval x *
        ((WeierstrassCurve.diffAddNumP W
          (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
  have h := WeierstrassCurve.diffAdd_projective_two_mul_add_one W h4 hψ_ne hc3 m
  simpa using congrArg (fun p : Polynomial k => p.eval x) h

/--
The complete x-only diff-add wiring proof, with the one genuinely non-wiring
fact needed by the infinity branch isolated as `hΦinf`.

In the nonzero branch, scalar `1` works.  In the zero branch, the witness is
`(W.Φ (2*m+1)).eval x`, so `hΦinf` is exactly the required nonzero proof.
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
      calc
        (W.ΨSq (2 * m + 1)).eval x
            = (deltaVec (xPair W (m + 1) x) (xPair W m x)) ^ 2 := by
                exact ΨSq_two_mul_add_one_eval_deltaVec_sq
                  (W := W) (m := m) (x := x) h4 hψ_ne hc3
        _ = 0 := by simp [hδ]

    refine ⟨(W.Φ (2 * m + 1)).eval x, hΦinf hδ, ?_⟩
    funext i
    fin_cases i <;> simp [xPair, xInfVec, hΨzero]

  · rw [diffAddOrInfVec, if_neg hδ]

    have hΨDen :
        (W.ΨSq (2 * m + 1)).eval x
          = ((WeierstrassCurve.diffAddDenP W
              (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
      exact ΨSq_two_mul_add_one_eval_diffAddDenP
        (W := W) (m := m) (x := x) h4 hψ_ne hc3

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
      exact diffAdd_projective_two_mul_add_one_eval
        (W := W) (m := m) (x := x) h4 hψ_ne hc3

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

## Exact requested theorem after the no-common-root helper

The helper you need can be stated directly in ladder language:

```lean
theorem xPair_odd_phi_eval_ne_zero_of_delta_zero
    (W : WeierstrassCurve k) (m : ℤ) (x : k)
    (h4) (hψ_ne) (hc3)
    (hδ : deltaVec (xPair W (m + 1) x) (xPair W m x) = 0) :
    (W.Φ (2 * m + 1)).eval x ≠ 0 := by
  -- Prove this from the relevant no-common-root theorem for `(Φ n, ΨSq n)`.
  -- The wiring proof above does not use the internals of this lemma.
  exact by
    have hΨzero : (W.ΨSq (2 * m + 1)).eval x = 0 := by
      calc
        (W.ΨSq (2 * m + 1)).eval x
            = (deltaVec (xPair W (m + 1) x) (xPair W m x)) ^ 2 := by
                exact ΨSq_two_mul_add_one_eval_deltaVec_sq
                  (W := W) (m := m) (x := x) h4 hψ_ne hc3
        _ = 0 := by simp [hδ]
    -- Replace this line by your local no-common-root theorem, for example:
    -- exact Φ_eval_ne_zero_of_ΨSq_eval_eq_zero
    --   (W := W) (n := 2 * m + 1) (x := x) h4 hψ_ne hc3 hΨzero
    -- or a more specialized odd-index theorem.
    admit
```

Do not leave the `admit`; it is only showing the exact insertion point for the
mathematical no-common-root fact.  With that theorem available, the requested
statement is:

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

---

## Why the extra helper is not optional

In the zero branch, `diffAddOrInfVec = xInfVec = ![1, 0]`, and the target vector
has the form

```lean
xPair W (2*m+1) x = ![(W.Φ (2*m+1)).eval x, 0].
```

For

```lean
xPair W (2*m+1) x = c • ![1, 0]
```

the first coordinate forces `c = (W.Φ (2*m+1)).eval x`.  Since `SameP1Vec`
requires `c ≠ 0`, the `Φ` nonzero proof is logically necessary.  If both
coordinates of `xPair W (2*m+1) x` vanish, then the requested `SameP1Vec` goal is
false, not merely hard to prove.
