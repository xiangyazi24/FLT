import Mathlib

namespace Scratch.ChatGPTDropDM1

#check PythagoreanTriple
#check PythagoreanTriple.even_odd_of_coprime

/--
Algebraic identity: if the Pythagorean parametrization yields
`n² = b⁴ + a²b² - a⁴`, then `(p',q',t') = (b,a,n)` satisfies the same
quartic denominator equation.
-/
private lemma new_solution_from_param_identity (a b n : ℤ)
    (h : n ^ 2 = b ^ 4 + b ^ 2 * a ^ 2 - a ^ 4) :
    n ^ 2 = b ^ 4 + b ^ 2 * a ^ 2 - a ^ 4 := by
  exact h

/--
A packaging of the primitive Pythagorean square-leg descent needed here.

This is the theorem that must come either from Mathlib's `PythagoreanTriple`
API or from a local proof using it.  It says that from the primitive triple
`m², r, p`, together with the special relation `2r = n² - m²`, one obtains
parameters `a,b` producing a smaller denominator-quartic solution.
-/
private axiom primitive_square_leg_descent_from_pythagoreanTriple
    (p q m n r : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m)
    (hnpos : 1 ≤ n)
    (hqmn : q = m * n)
    (hr : 2 * r = n ^ 2 - m ^ 2)
    (htriple : PythagoreanTriple (m ^ 2) r p) :
    ∃ a b : ℤ,
      2 ≤ a ∧
      Int.gcd b a = 1 ∧
      n ^ 2 = b ^ 4 + b ^ 2 * a ^ 2 - a ^ 4 ∧
      a.natAbs < q.natAbs

/--
The left-`5` Pythagorean self-descent core.

This is the wrapper around the `PythagoreanTriple` parametrization.  The only
substantive input is `primitive_square_leg_descent_from_pythagoreanTriple`;
once it supplies `a,b`, the final existential witness is `(b,a,n)` and the
quartic equation is algebraic.
-/
private theorem pythagorean_square_leg_descent_core_left5
    (p q t m n : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m)
    (hnpos : 1 ≤ n)
    (hqmn : q = m * n)
    (hcoeff : 4 * p ^ 2 = (n ^ 2 - m ^ 2) ^ 2 + 4 * m ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs := by
  let r : ℤ := (n ^ 2 - m ^ 2) / 2
  have hr : 2 * r = n ^ 2 - m ^ 2 := by
    -- In the odd-`q` branch, `m,n` are odd, so `n²-m²` is divisible by `2`.
    -- This parity fact should be supplied from the odd-core context.
    -- Once available, `omega` closes this division identity.
    sorry
  have htriple : PythagoreanTriple (m ^ 2) r p := by
    -- `PythagoreanTriple x y z` is `x*x + y*y = z*z`.
    -- Use `hr` to rewrite `(n²-m²)² = (2r)²` in `hcoeff`.
    unfold PythagoreanTriple
    nlinarith
  obtain ⟨a, b, hapos, hcopba, hnew, hdrop⟩ :=
    primitive_square_leg_descent_from_pythagoreanTriple
      p q m n r hq hcop hmpos hnpos hqmn hr htriple
  refine ⟨b, a, n, hapos, hcopba, ?_, hdrop⟩
  exact new_solution_from_param_identity a b n hnew

end Scratch.ChatGPTDropDM1
