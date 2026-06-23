# Q56 (dm3): Even-index `Φ`/`ΨSq` no-common-root capstone

This is the even-index analogue of the integrated odd theorem

```lean
Φ_ΨSq_no_common_eval_zero_odd
```

It belongs in `scratch/KeystoneCoprimality.lean`, in namespace
`WeierstrassCurve`, after the already-integrated odd theorem and after the local
abbreviations

```lean
pe W x i := (W.preΨ i).eval x
sx W x := W.Ψ₂Sq.eval x
c3x W x := W.Ψ₃.eval x
```

The proof follows the requested split exactly:

* `ΨSq(2*m).eval = pe(2*m)^2 * sx`;
* `Φ(2*m).eval = x * ΨSq(2*m).eval - pe(2*m+1) * pe(2*m-1)`;
* if `sx = 0`, both odd factors are nonzero by the 2-torsion lemma;
* if `sx ≠ 0`, then `pe(2*m)=0`, and either odd factor zero gives an adjacent
  vanishing pair, contradicting `no_adjacent_preΨ_zero`.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

namespace WeierstrassCurve

open Polynomial

variable {k : Type*} [Field k]

/--
Even `ΨSq` evaluation in the `pe/sx` notation used by the Keystone coprimality
file.

This is just `ΨSq_even` evaluated at `x`, with the large even-recursion factor
identified with `preΨ (2*m)` by `preΨ_even`.
-/
theorem ΨSq_eval_even
    (W : WeierstrassCurve k) (x : k) (m : ℤ) :
    (W.ΨSq (2 * m)).eval x = (pe W x (2 * m)) ^ 2 * sx W x := by
  have hpre :
      ((W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2)
          - W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2).eval x)
        = pe W x (2 * m) := by
    have h := congrArg (fun p : Polynomial k => p.eval x) (W.preΨ_even m)
    simpa [pe] using h.symm

  have hΨ := congrArg (fun p : Polynomial k => p.eval x) (W.ΨSq_even m)
  calc
    (W.ΨSq (2 * m)).eval x
        = (((W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2)
              - W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2) ^ 2
              * W.Ψ₂Sq).eval x) := by
            simpa using hΨ
    _ = ((W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2)
              - W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2).eval x) ^ 2
            * sx W x := by
            simp [sx]
    _ = (pe W x (2 * m)) ^ 2 * sx W x := by
            rw [hpre]

/--
Even `Φ` evaluation in the `pe/sx` notation.

For `n = 2*m`, the trailing factor in the general definition of `Φ` is `1`, not
`Ψ₂Sq`.
-/
theorem Φ_eval_even
    (W : WeierstrassCurve k) (x : k) (m : ℤ) :
    (W.Φ (2 * m)).eval x
      = x * (W.ΨSq (2 * m)).eval x
          - pe W x (2 * m + 1) * pe W x (2 * m - 1) := by
  have hEven : Even (2 * m) := ⟨m, by ring⟩
  simp [WeierstrassCurve.Φ, pe, hEven] <;> ring

/--
Even-index no-common-root theorem for `Φ` and `ΨSq`.

This is the exact even analogue of `Φ_ΨSq_no_common_eval_zero_odd`.
-/
theorem Φ_ΨSq_no_common_eval_zero_even
    (W : WeierstrassCurve k) [W.IsElliptic] (x : k)
    (h4 : (4 : k) ≠ 0) (m : ℤ) :
    ¬ ((W.Φ (2 * m)).eval x = 0 ∧ (W.ΨSq (2 * m)).eval x = 0) := by
  rintro ⟨hΦ, hΨ⟩

  have hpe_sx : (pe W x (2 * m)) ^ 2 * sx W x = 0 := by
    have h := hΨ
    rw [ΨSq_eval_even (W := W) (x := x) (m := m)] at h
    exact h

  have hprod : pe W x (2 * m + 1) * pe W x (2 * m - 1) = 0 := by
    have hΦformula := Φ_eval_even (W := W) (x := x) (m := m)
    have hzero :
        (0 : k) = - (pe W x (2 * m + 1) * pe W x (2 * m - 1)) := by
      simpa [hΦ, hΨ] using hΦformula
    exact neg_eq_zero.mp hzero.symm

  by_cases hs : sx W x = 0
  · have hodd_next : ¬ Even (2 * m + 1) := by
      simpa using Int.not_even_two_mul_add_one m
    have hodd_prev : ¬ Even (2 * m - 1) := by
      simpa [show 2 * (m - 1) + 1 = 2 * m - 1 by ring] using
        (Int.not_even_two_mul_add_one (m - 1))

    have hnext_ne : pe W x (2 * m + 1) ≠ 0 :=
      preΨ_odd_eval_ne_of_Ψ₂Sq_eval_zero
        (W := W) (x := x) (h4 := h4) (hs := hs)
        (n := 2 * m + 1) hodd_next
    have hprev_ne : pe W x (2 * m - 1) ≠ 0 :=
      preΨ_odd_eval_ne_of_Ψ₂Sq_eval_zero
        (W := W) (x := x) (h4 := h4) (hs := hs)
        (n := 2 * m - 1) hodd_prev

    exact (mul_ne_zero hnext_ne hprev_ne) hprod

  · have hsq : (pe W x (2 * m)) ^ 2 = 0 :=
      (mul_eq_zero.mp hpe_sx).resolve_right hs
    have hpe_even : pe W x (2 * m) = 0 := sq_eq_zero_iff.mp hsq

    rcases mul_eq_zero.mp hprod with hnext | hprev
    · exact (no_adjacent_preΨ_zero
          (W := W) (x := x) (h4 := h4) (r := 2 * m))
        ⟨hpe_even, hnext⟩
    · exact (no_adjacent_preΨ_zero
          (W := W) (x := x) (h4 := h4) (r := 2 * m - 1))
        ⟨hprev, by
          simpa [show (2 * m - 1) + 1 = 2 * m by ring] using hpe_even⟩

end WeierstrassCurve
```

## If local theorem names differ slightly

The proof uses these already-integrated local lemmas exactly as stated in the
prompt:

```lean
no_adjacent_preΨ_zero
preΨ_odd_eval_ne_of_Ψ₂Sq_eval_zero
```

and the Mathlib division-polynomial identities

```lean
W.preΨ_even m
W.ΨSq_even m
```

If your local names are non-dot theorem names, the two eval helper proofs only
need the following mechanical replacements:

```lean
(W.preΨ_even m)  ↦  (preΨ_even W m)
(W.ΨSq_even m)  ↦  (ΨSq_even W m)
```

The mathematical proof and the branch structure are unchanged.
