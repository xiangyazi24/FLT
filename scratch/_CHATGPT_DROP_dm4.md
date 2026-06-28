# Q2120 (dm4): `weilPairing_self` proof for the Miller-function Weil pairing

Date: 2026-06-28.

Repository: `xiangyazi24/FLT`.

## Executive answer

The cancellation idea is mathematically correct **provided the two evaluations are nonzero**:

```text
a := evalAtPoint W (millerLoop W P m) (P + S)
b := evalAtPoint W (millerLoop W P m) S

weilPairing W m P P S = (a / b) * (b / a) = 1.
```

However, the current theorem statement in `FLT/Assumptions/MazurProof/MillerFunction.lean` is too strong as written:

```lean
theorem weilPairing_self (m : ℕ) (P S : Point W) :
    weilPairing W m P P S = 1 := by
  sorry
```

In Lean, division in a field is total.  If either `a` or `b` is zero, then `(a / b) * (b / a)` is not definitionally or theoremically equal to `1`; for example the zero case reduces to `0`, not `1`.  So the short proof needs the support-avoidance/nonvanishing hypotheses that are mathematically implicit in the choice of the auxiliary point `S`.

Thus the honest theorem is one of these two forms:

1. replace `weilPairing_self` by a version with explicit nonzero hypotheses; or
2. keep the external theorem name/signature only after the definition of admissible `S` packages these nonzero hypotheses.

The deep divisor theory is **not** needed for the algebraic cancellation step, but it is needed upstream to prove that the relevant evaluations are defined and nonzero for admissible `S`.

## Drop-in Lean code

This is the minimal replacement I would put in `MillerFunction.lean` inside the existing namespace/section.  No extra import is needed beyond the file's existing `import Mathlib`.

```lean
/-- Algebra lemma for the self-pairing cancellation.

This is the whole algebraic content of `e_m(P,P)=1`: the two Miller-ratio
factors are reciprocals, provided the two evaluations are nonzero. -/
private lemma div_swap_mul_cancel {K : Type*} [Field K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (a / b) * (b / a) = 1 := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    (a * b⁻¹) * (b * a⁻¹) = (a * a⁻¹) * (b * b⁻¹) := by
      ring
    _ = 1 := by
      simp [ha, hb]

/-- The alternating self-pairing property, in the Miller-function formula,
under the nonvanishing hypotheses supplied by the admissibility/support
condition on the auxiliary point `S`.

For `Q = P`, the two factors in the definition are

`a / b` and `b / a`,

where

`a = evalAtPoint W (millerLoop W P m) (P + S)` and
`b = evalAtPoint W (millerLoop W P m) S`.

So the result is pure field cancellation once `a ≠ 0` and `b ≠ 0`. -/
theorem weilPairing_self (m : ℕ) (P S : Point W)
    (hPS : evalAtPoint W (millerLoop W P m) (P + S) ≠ 0)
    (hS : evalAtPoint W (millerLoop W P m) S ≠ 0) :
    weilPairing W m P P S = 1 := by
  dsimp [weilPairing]
  exact div_swap_mul_cancel
    (a := evalAtPoint W (millerLoop W P m) (P + S))
    (b := evalAtPoint W (millerLoop W P m) S)
    hPS hS
```

## If you do not want to change the old theorem name yet

If downstream code expects the old no-hypothesis theorem, do **not** pretend it is provable directly.  Instead add the proved lemma with a new name:

```lean
theorem weilPairing_self_of_eval_ne_zero (m : ℕ) (P S : Point W)
    (hPS : evalAtPoint W (millerLoop W P m) (P + S) ≠ 0)
    (hS : evalAtPoint W (millerLoop W P m) S ≠ 0) :
    weilPairing W m P P S = 1 := by
  dsimp [weilPairing]
  exact div_swap_mul_cancel
    (a := evalAtPoint W (millerLoop W P m) (P + S))
    (b := evalAtPoint W (millerLoop W P m) S)
    hPS hS
```

Then later the final external theorem should be a wrapper that extracts `hPS` and `hS` from an admissibility predicate for `S`, for example schematically:

```lean
-- schematic only: names depend on the eventual support-avoidance API
structure WeilPairingAuxOK (W : Affine K) (m : ℕ) (P Q S : Point W) : Prop where
  left_num_ne_zero  : evalAtPoint W (millerLoop W P m) (Q + S) ≠ 0
  left_den_ne_zero  : evalAtPoint W (millerLoop W P m) S ≠ 0
  right_num_ne_zero : evalAtPoint W (millerLoop W Q m) S ≠ 0
  right_den_ne_zero : evalAtPoint W (millerLoop W Q m) (P + S) ≠ 0

theorem weilPairing_self_admissible (m : ℕ) (P S : Point W)
    (hSok : WeilPairingAuxOK W m P P S) :
    weilPairing W m P P S = 1 := by
  exact weilPairing_self_of_eval_ne_zero W m P S
    hSok.left_num_ne_zero
    hSok.left_den_ne_zero
```

The exact field names of `WeilPairingAuxOK` can be adjusted later.  The key point is that the proof of `weilPairing_self` should consume nonvanishing facts; it should not be responsible for proving divisor support avoidance.

## Why the original no-hypothesis theorem is not right

With `Q = P`, the current definition unfolds to

```lean
(evalAtPoint W (millerLoop W P m) (P + S) /
 evalAtPoint W (millerLoop W P m) S) *
(evalAtPoint W (millerLoop W P m) S /
 evalAtPoint W (millerLoop W P m) (P + S))
```

This is `(a / b) * (b / a)`.  In an ordinary mathematical derivation, one silently assumes `a,b ≠ 0`; in Lean's `Field K`, the expression is total even when `a=0` or `b=0`, and the cancellation theorem requires hypotheses.

So the correct verification is:

```text
Correct algebra:       yes.
Needs divisor theory:  not for cancellation, yes for nonvanishing/admissible S.
Current theorem type:  too strong unless evalAtPoint is redesigned to return units/defined values.
Lean proof:            the code above closes the cancellation theorem with hPS/hS.
```

## Recommended implementation path

For the current skeleton, I recommend replacing the existing `sorry` theorem by the explicit-hypothesis version:

```lean
theorem weilPairing_self (m : ℕ) (P S : Point W)
    (hPS : evalAtPoint W (millerLoop W P m) (P + S) ≠ 0)
    (hS : evalAtPoint W (millerLoop W P m) S ≠ 0) :
    weilPairing W m P P S = 1 := by
  dsimp [weilPairing]
  exact div_swap_mul_cancel
    (a := evalAtPoint W (millerLoop W P m) (P + S))
    (b := evalAtPoint W (millerLoop W P m) S)
    hPS hS
```

Later, when the divisor/evaluation layer exists, introduce an admissibility predicate for `S` and derive the no-clutter user-facing theorem from it.