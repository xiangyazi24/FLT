# `coprime_fourth_power_factor`

Here is a Lean proof of the requested factor-splitting lemma, with the unique-factorization step isolated as one explicit axiom.  I include the hypothesis `0 < q`: without it, the requested conclusion with `0 < m`, `0 < n`, and `m*n=q` is false for negative `q`.  In the descent application this is available from `2 ≤ q`.

The proof is organized as follows.

1. From `5 ∣ A`, write `A = 5*X`.
2. Positivity of `A` gives `0 < X`.
3. From `A*B = 5*q^4`, obtain `X*B = q^4`.
4. From `IsCoprime A B`, obtain `IsCoprime X B`, since `A = 5*X`.
5. Apply the one UFD/prime-factorization axiom: if `X` and `Y` are coprime positive integers and `X*Y=q^4`, then `X=m^4`, `Y=n^4`, and `m*n=q`.
6. Substitute back to get `A=5*m^4`, `B=n^4`.

```lean
import Mathlib

/-!
# Coprime factors of `5*q^4`

The only non-elementary input is the UFD/factorization fact that coprime
positive factors of a fourth power are themselves fourth powers.
-/

namespace Scratch.ChatGPTDropDM1

/--
UFD / prime-factorization input over `ℤ`.

If two positive coprime integers multiply to a positive fourth power, then each
factor is a fourth power, with compatible positive roots.
-/
axiom coprime_product_eq_fourth_power
    (X Y q : ℤ)
    (hXpos : 0 < X)
    (hYpos : 0 < Y)
    (hqpos : 0 < q)
    (hcop : IsCoprime X Y)
    (hXY : X * Y = q ^ 4) :
    ∃ m n : ℤ,
      X = m ^ 4 ∧
      Y = n ^ 4 ∧
      m * n = q ∧
      0 < m ∧
      0 < n

/--
If `A` and `B` are coprime positive integers, `5 ∣ A`, and
`A * B = 5 * q^4` with `q > 0`, then `A = 5*m^4`, `B = n^4`, and `m*n=q`.
-/
theorem coprime_fourth_power_factor
    (A B q : ℤ)
    (hAB : A * B = 5 * q ^ 4)
    (hcop : IsCoprime A B)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (hqpos : 0 < q)
    (h5A : (5 : ℤ) ∣ A) :
    ∃ m n : ℤ,
      A = 5 * m ^ 4 ∧
      B = n ^ 4 ∧
      m * n = q ∧
      0 < m ∧
      0 < n := by
  rcases h5A with ⟨X, hAX⟩
  have hXpos : 0 < X := by
    rw [hAX] at hApos
    nlinarith
  have hXY : X * B = q ^ 4 := by
    rw [hAX] at hAB
    nlinarith
  have hcopXB : IsCoprime X B := by
    rcases hcop with ⟨r, s, hbez⟩
    refine ⟨5 * r, s, ?_⟩
    rw [hAX] at hbez
    nlinarith
  obtain ⟨m, n, hm, hn, hmn, hmpos, hnpos⟩ :=
    coprime_product_eq_fourth_power X B q hXpos hBpos hqpos hcopXB hXY
  refine ⟨m, n, ?_, hn, hmn, hmpos, hnpos⟩
  rw [hAX, hm]
  ring

end Scratch.ChatGPTDropDM1
```

A symmetric version with `5 ∣ B` follows by swapping `A` and `B`; in the descent proof this is the other branch of the same split.
