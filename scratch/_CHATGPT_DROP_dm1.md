# Drop for `zphi_descent_step_even_core`

I could not honestly produce the requested zero-hole, zero-postulate Lean proof.

The easy branch is clear: if `q = 2*s` with `s` odd, then `p` is odd from
`Int.gcd p q = 1`, and the equation gives
`t² ≡ 1 + 4 ≡ 5 (mod 16)`, impossible for an integer square.

The remaining branch `4 ∣ q` is not a small modular contradiction. It requires a
substantial descent package. The clean paper proof starts from

\[
(2p^2+q^2-2t)(2p^2+q^2+2t)=5q^4.
\]

Writing `q = 2*s`, both factors are divisible by `4`, so

\[
A B = 5s^4,\qquad A+B=p^2+2s^2,\qquad B-A=t.
\]

One then needs to prove, in Lean, all of the following without any hidden
unproved assumption:

1. the normalized factors `A` and `B` are positive and coprime;
2. from `A*B = 5*s^4` and coprimality, one factor is a fourth power and the
   other is `5` times a fourth power;
3. the resulting identity
   `p² = (u²-v²)² + (2*v²)²` is a primitive Pythagorean triple;
4. the primitive triple parametrization forces `v² = a*b` with `a,b` coprime,
   hence `a` and `b` are squares;
5. coefficient comparison produces a smaller quartic solution
   `u² = c⁴ + c²*d² - d⁴`;
6. the terminal `d = 1` subcase is excluded, otherwise the requested conclusion
   `2 ≤ q'` does not follow.

Those are exactly the missing hard lemmas; replacing them by declarations would
violate the request. The Lean block below is therefore not presented as a
solution to the theorem. It is only a self-contained marker file documenting the
blocked proof state without adding declarations that pretend to prove the goal.

```lean
import Mathlib

set_option maxHeartbeats 400000

/-!
This file is intentionally not a claimed proof of

```
theorem zphi_descent_step_even_core
    (p q t : ℤ) (hq : 2 ≤ q) (hqeven : (2 : ℤ) ∣ q)
    (hcop : Int.gcd p q = 1)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
    ∃ p' q' t' : ℤ, 2 ≤ q' ∧ Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧ q'.natAbs < q.natAbs
```

The `q ≡ 2 (mod 4)` contradiction is elementary, but the `4 ∣ q`
case needs the full Pell-factor split and primitive Pythagorean descent package.
Adding those results as unproved declarations would be unsound for this task.

This marker theorem keeps the file valid Lean while making no false claim.
-/

theorem zphi_descent_step_even_core_drop_status : True := by
  trivial
```
