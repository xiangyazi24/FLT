# Q1294 (dm1): Lean status for the Ljunggren/Fermat descent

I cannot honestly provide a closed Lean proof of the full theorem as a single finished code block from existing Mathlib facts. The part that is missing is not the final induction on `B`; it is the arithmetic descent step that turns a non-base solution of

```text
s^2 + B^4 = r^4 + r^2 * B^2
```

into a strictly smaller non-base solution. Mathlib has `Mathlib.NumberTheory.FLT.Four`, including `Fermat42` and `not_fermat_42`, but this theorem is not a direct consequence of `not_fermat_42`: after the `U,V` split one gets a square-leg equation `h^2 + y^4 = z^2`, not an equation `h^4 + y^4 = z^2`.

The important correction to the earlier skeleton is that the descent lemma must preserve **non-baseness**. A statement returning only a smaller solution is not enough for strong induction.

## No-sorry Lean wrapper once the descent step is proved

```lean
import Mathlib

noncomputable section

namespace DM1

/-- Primitive positive natural-number solutions, written without natural subtraction. -/
def IsSolution (r B s : ℕ) : Prop :=
  0 < r ∧ 0 < B ∧ Nat.Coprime r B ∧
    s ^ 2 + B ^ 4 = r ^ 4 + r ^ 2 * B ^ 2

/-- The base solution. -/
def IsBase (r B : ℕ) : Prop :=
  r = 1 ∧ B = 1

/--
Minimal-counterexample wrapper. If every non-base solution descends to a smaller
non-base solution, then every solution is base.
-/
theorem solution_eq_base_from_descent
    (descent :
      ∀ {r B s : ℕ}, IsSolution r B s → ¬ IsBase r B →
        ∃ r' B' s' : ℕ,
          IsSolution r' B' s' ∧ ¬ IsBase r' B' ∧ B' < B)
    {r B s : ℕ} (hsol : IsSolution r B s) :
    IsBase r B := by
  classical
  by_contra hnot
  let Bad : ℕ → Prop :=
    fun B0 ↦ ∃ r0 s0 : ℕ, IsSolution r0 B0 s0 ∧ ¬ IsBase r0 B0
  have hbad : Bad B := ⟨r, s, hsol, hnot⟩
  let hex : ∃ B0 : ℕ, Bad B0 := ⟨B, hbad⟩
  let B0 : ℕ := Nat.find hex
  have hB0 : Bad B0 := Nat.find_spec hex
  rcases hB0 with ⟨r0, s0, hsol0, hnot0⟩
  rcases descent hsol0 hnot0 with ⟨r1, B1, s1, hsol1, hnot1, hlt⟩
  have hB1 : Bad B1 := ⟨r1, s1, hsol1, hnot1⟩
  have hmin : B0 ≤ B1 := Nat.find_min' hex hB1
  exact (not_le_of_gt hlt) hmin

/-- Final user-facing theorem, parameterized by the real descent step. -/
theorem target_from_descent
    (descent :
      ∀ {r B s : ℕ}, IsSolution r B s → ¬ IsBase r B →
        ∃ r' B' s' : ℕ,
          IsSolution r' B' s' ∧ ¬ IsBase r' B' ∧ B' < B)
    {r B s : ℕ}
    (hr : 0 < r) (hB : 0 < B) (hcop : Nat.Coprime r B)
    (heq : s ^ 2 + B ^ 4 = r ^ 4 + r ^ 2 * B ^ 2) :
    r = 1 ∧ B = 1 := by
  simpa [IsBase] using
    solution_eq_base_from_descent
      (descent := descent)
      (hsol := ⟨hr, hB, hcop, heq⟩)

end DM1
```

## Exact missing theorem

The theorem that must be proved to close Q1294 is:

```lean
namespace DM1

theorem dm1_descent_step_nonbase
    {r B s : ℕ}
    (hsol : IsSolution r B s)
    (hnot : ¬ IsBase r B) :
    ∃ r' B' s' : ℕ,
      IsSolution r' B' s' ∧ ¬ IsBase r' B' ∧ B' < B := by
  -- real proof goes here
  -- no axiom/admit/sorry if this is meant to be a theorem
  -- main work: factor split plus Pythagorean square-leg descent
  fail_if_success exact False.elim (by contradiction)
  -- placeholder line above intentionally does not prove the theorem
```

The final theorem after this descent step exists is:

```lean
namespace DM1

theorem dm1_final
    {r B s : ℕ}
    (hr : 0 < r) (hB : 0 < B) (hcop : Nat.Coprime r B)
    (heq : s ^ 2 + B ^ 4 = r ^ 4 + r ^ 2 * B ^ 2) :
    r = 1 ∧ B = 1 := by
  exact target_from_descent
    (descent := dm1_descent_step_nonbase)
    hr hB hcop heq

end DM1
```

## Lemmas needed for `dm1_descent_step_nonbase`

1. Define over integers

```text
A = 2*r^2 + B^2,
U = A - 2*s,
V = A + 2*s.
```

Prove positivity, the factor identity

```text
U * V = 5 * B^4,
```

and the required gcd/parity facts. The identity is a `ring_nf` calculation from the equation.

2. Prove a reusable fourth-power split:

```lean
lemma coprime_mul_eq_fourth_power
    {x y z : ℕ}
    (hx : 0 < x) (hy : 0 < y)
    (hcop : Nat.Coprime x y)
    (hxy : x * y = z ^ 4) :
    ∃ a b : ℕ, x = a ^ 4 ∧ y = b ^ 4 ∧ z = a * b
```

A good route is to view `z^4` as `(z^2)^2`, split a coprime product of squares using `Int.sq_of_gcd_eq_one`, then split the square roots once more.

3. Split the factorization

```lean
lemma split_five_mul_fourth
    {U V B : ℕ}
    (hU : 0 < U) (hV : 0 < V)
    (hcop : Nat.Coprime U V)
    (hprod : U * V = 5 * B ^ 4) :
    ∃ a b : ℕ,
      0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ B = a * b ∧
        ((U = a ^ 4 ∧ V = 5 * b ^ 4) ∨
         (U = 5 * a ^ 4 ∧ V = b ^ 4))
```

Use `Nat.Prime.dvd_mul` for the prime `5`. If `5 ∣ U`, write `U = 5 * U0`; cancellation gives `U0 * V = B^4`, then apply the fourth-power split. The `5 ∣ V` case is symmetric.

4. Prove the Pythagorean square-leg descent:

```lean
lemma pythagorean_square_leg_descent
    {h y z : ℕ}
    (hh : 0 < h) (hy : 0 < y)
    (hcop : Nat.Coprime h y)
    (heven : Even h) (hodd : Odd y)
    (heq : h ^ 2 + y ^ 4 = z ^ 2) :
    ∃ u v : ℕ,
      0 < u ∧ u < v ∧ Odd u ∧ Odd v ∧ Nat.Coprime u v ∧
      y = u * v ∧ 2 * h + u ^ 4 = v ^ 4
```

Use `PythagoreanTriple.coprime_classification'` on `(x,y,z) = (y^2,h,z)` over `ℤ`, then split

```text
y^2 = (m-n)(m+n)
```

with `Int.sq_of_gcd_eq_one`.

5. Finish the case algebra:

- If `U = a^4` and `V = 5*b^4`, then
  `4*r^2 = (a^2-b^2)^2 + 4*b^4`.
  If `a=b`, prove the base case. If `a>b`, return `(r',B',s') = (v,u,a)`. If `a<b`, return `(r',B',s') = (u,v,a)` and prove `u ≠ 1` to get strict descent.
- If `U = 5*a^4` and `V = b^4`, then
  `4*r^2 = (b^2-a^2)^2 + 4*a^4`; return `(r',B',s') = (v,u,b)`.

In all descent branches, `u < v` proves the returned solution is non-base.

## Conclusion

The outer induction theorem above is complete Lean code. The full requested theorem still requires the genuine formal proof of `dm1_descent_step_nonbase`; that is the actual several-hundred-line arithmetic descent formalization, not something currently supplied by Mathlib as a single theorem.
