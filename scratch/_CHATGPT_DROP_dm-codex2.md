# Q2448 EulerAux descent shortest DAG after helpers

## 0. Normalize the seed once

Use a positive odd common leg.  If the current file still carries a signed `D`, do the sign-normalization before this DAG and call the normalized leg `B`.

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

namespace EulerAux

structure EulerAuxWitness (A B S R : ℤ) : Prop where
  hApos : 0 < A
  hBpos : 0 < B
  hBodd : Odd B
  hAB : IsCoprime A B
  hSpos : 0 < S
  hRpos : 0 < R
  hS : S^2 = (2*A)^2 + B^2
  hR : R^2 = (4*A)^2 + B^2

end EulerAux
```

Pure algebra adapters from equations to triples:

```lean
namespace EulerAux

theorem witness_left_triple {A B S R : ℤ} (W : EulerAuxWitness A B S R) :
    PythagoreanTriple B (2*A) S := by
  dsimp [PythagoreanTriple]
  nlinarith [W.hS]

theorem witness_right_triple {A B S R : ℤ} (W : EulerAuxWitness A B S R) :
    PythagoreanTriple B (4*A) R := by
  dsimp [PythagoreanTriple]
  nlinarith [W.hR]

end EulerAux
```

## 1. Two-triangle parametrization theorem

Use the existing `twoA_triangle_param_with_A` twice.  The right triangle is applied with `A := 2*A` because its even leg is `4*A = 2*(2*A)`.

Expected helper shape:

```lean
namespace EulerAux

theorem twoA_triangle_param_with_A
    {A B C : ℤ}
    (htri : PythagoreanTriple B (2*A) C)
    (hcop : IsCoprime B (2*A))
    (hBodd : Odd B)
    (hCpos : 0 < C) :
    ∃ m n : ℤ,
      0 < m ∧ 0 < n ∧
      B = m^2 - n^2 ∧
      A = m*n ∧
      C = m^2 + n^2 ∧
      IsCoprime m n ∧
      ((Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) := by
  -- already supplied/being validated from `PythagoreanTriple.coprime_classification'`
  sorry

end EulerAux
```

The first new assembly theorem should not expose classifier case splits.  It should expose exactly the two coprime factorizations needed by refinement.

```lean
namespace EulerAux

structure EulerAuxParam (A B S R : ℤ) where
  U V U' V' : ℤ
  hUpos : 0 < U
  hVpos : 0 < V
  hU'pos : 0 < U'
  hV'pos : 0 < V'
  hUeven : Even U
  hVodd : Odd V
  hU'even : Even U'
  hV'odd : Odd V'
  hUV_coprime : IsCoprime U V
  hU'V'_coprime : IsCoprime U' V'
  hA_left : A = U*V
  hA_right : A = U'*V'
  hB_left : B = U^2 - V^2
  hB_right : B = (2*U')^2 - V'^2
  hS : S = U^2 + V^2
  hR : R = (2*U')^2 + V'^2

/-- Two-triangle parametrization in the exact shape consumed by common-refinement. -/
theorem EulerAux_param
    {A B S R : ℤ}
    (W : EulerAuxWitness A B S R) :
    EulerAuxParam A B S R := by
  -- left: apply `twoA_triangle_param_with_A` to
  --   `PythagoreanTriple B (2*A) S`.
  -- choose orientation so `U` is even and `V` is odd; if the classifier returns
  -- the odd/even order, swap the parameters and replace `B` by the already
  -- normalized positive common leg convention before this theorem.
  --
  -- right: apply `twoA_triangle_param_with_A` to
  --   `PythagoreanTriple B (2*(2*A)) R`.
  -- it returns `2*A = M*N`, with one of `M,N` even and the other odd.
  -- orient so `M` is even and write `M = 2*U'`.
  -- Since `A = U*V` with `U` even and `V` odd, `A` is even.  Since
  -- `A = U'*V'` and `V'` is odd, `U'` is even.
  --
  -- Pure local parity lemmas needed here:
  --   `even_left_of_even_mul_odd : Even (x*y) -> Odd y -> Even x`
  --   `pos_of_mul_pos_left/right` for the positive factors.
  sorry

end EulerAux
```

If sign normalization is not yet separated, replace the two `hB_*` fields by fields for `normOddLeg B`; the rest of the DAG is unchanged.

## 2. Positive common-refinement theorem

Prefer this positive statement over the older signed statement.  It avoids all sign repair before the descent algebra.

```lean
namespace EulerAux

def PairwiseCoprime2abcd (a b c d : ℤ) : Prop :=
  IsCoprime (2*a) b ∧
  IsCoprime (2*a) c ∧
  IsCoprime (2*a) d ∧
  IsCoprime b c ∧
  IsCoprime b d ∧
  IsCoprime c d

structure RefinedFactors (A U V U' V' : ℤ) where
  a b c d : ℤ
  hapos : 0 < a
  hbpos : 0 < b
  hcpos : 0 < c
  hdpos : 0 < d
  hU : U = 2*a*b
  hV : V = c*d
  hU' : U' = 2*a*c
  hV' : V' = b*d
  hA : A = 2*a*b*c*d
  hdodd : Odd d
  hpair : PairwiseCoprime2abcd a b c d

/-- Positive version of the two-coprime-factorization common refinement. -/
theorem two_coprime_factorizations_refine_even_pos
    {A U V U' V' : ℤ}
    (hApos : 0 < A)
    (hUV : A = U*V)
    (hU'V' : A = U'*V')
    (hUpos : 0 < U) (hVpos : 0 < V)
    (hU'pos : 0 < U') (hV'pos : 0 < V')
    (hUeven : Even U) (hU'even : Even U')
    (hVodd : Odd V) (hV'odd : Odd V')
    (hUVcop : IsCoprime U V)
    (hU'V'cop : IsCoprime U' V') :
    RefinedFactors A U V U' V' := by
  -- Proof source:
  --   signed common-refinement of two coprime factorizations,
  --   then positivity fixes all unit/sign choices.
  --
  -- This is the only remaining factor-refinement lemma.  It is independent of
  -- Pythagorean triples and independent of square balance.
  sorry

end EulerAux
```

This theorem is the clean replacement for the older signed statement
`P = 2*a*b`, `Q = c*d`, `U = 2*a*c`, `V = b*d`.

## 3. Algebraic balance identity and square-balance use

From parametrization and refinement:

```lean
namespace EulerAux

theorem EulerAux_balance_identity
    {B a b c d : ℤ}
    (hB_left : B = (2*a*b)^2 - (c*d)^2)
    (hB_right : B = (2*(2*a*c))^2 - (b*d)^2) :
    b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2) := by
  nlinarith [hB_left, hB_right]

/-- The remaining gcd lemma for the two balanced cofactors. -/
theorem coprime_four_sq_add_d_sq_sixteen_sq_add_d_sq
    {a d : ℤ}
    (hapos : 0 < a)
    (hdpos : 0 < d)
    (had : IsCoprime a d)
    (hdodd : Odd d) :
    IsCoprime (4*a^2 + d^2) (16*a^2 + d^2) := by
  -- Prime-divisor proof:
  --   any prime divisor of both divides their difference `12*a^2`;
  --   using `IsCoprime a d`, it cannot divide `a`, hence it divides `12`;
  --   oddness rules out `2`; modulo `3`, `a^2 + d^2` is never `0` when
  --   `a,d` are coprime, so `3` is ruled out.
  -- This is small number theory, not descent.
  sorry

theorem EulerAux_square_balance_consequence
    {a b c d : ℤ}
    (hapos : 0 < a) (hbpos : 0 < b) (hcpos : 0 < c) (hdpos : 0 < d)
    (hbc : IsCoprime b c)
    (had : IsCoprime a d)
    (hdodd : Odd d)
    (hbal : b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2)) :
    (4*a^2 + d^2 = c^2) ∧ (16*a^2 + d^2 = b^2) := by
  have hMpos : 0 < 4*a^2 + d^2 := by nlinarith [sq_pos_of_ne_zero (ne_of_gt hdpos)]
  have hNpos : 0 < 16*a^2 + d^2 := by nlinarith [sq_pos_of_ne_zero (ne_of_gt hdpos)]
  have hMN : IsCoprime (4*a^2 + d^2) (16*a^2 + d^2) :=
    coprime_four_sq_add_d_sq_sixteen_sq_add_d_sq hapos hdpos had hdodd
  -- `square_factor_balance_int` returns `M = c^2 ∧ N = b^2`.
  exact square_factor_balance_int hbpos hcpos hMpos hNpos hbc hMN hbal

end EulerAux
```

Required coprimality projections from `PairwiseCoprime2abcd`:

```lean
namespace EulerAux

theorem pairwise_bc {a b c d : ℤ} (h : PairwiseCoprime2abcd a b c d) :
    IsCoprime b c := h.2.2.2.1

theorem pairwise_ad {a b c d : ℤ} (h : PairwiseCoprime2abcd a b c d) :
    IsCoprime a d := by
  -- From `IsCoprime (2*a) d` by divisibility descent `a ∣ 2*a`.
  exact h.2.2.1.of_dvd_left ⟨2, by ring⟩

end EulerAux
```

## 4. Descent step and measure decrease

The new witness is

```lean
Anew = a
Bnew = d
Snew = c
Rnew = b
```

because square-balance gives

```lean
c^2 = (2*a)^2 + d^2
b^2 = (4*a)^2 + d^2.
```

Skeleton:

```lean
namespace EulerAux

theorem EulerAux_measure_decrease
    {A a b c d : ℤ}
    (hA : A = 2*a*b*c*d)
    (hapos : 0 < a) (hbpos : 0 < b) (hcpos : 0 < c) (hdpos : 0 < d) :
    a < A := by
  have hb1 : 1 ≤ b := by omega
  have hc1 : 1 ≤ c := by omega
  have hd1 : 1 ≤ d := by omega
  nlinarith

theorem EulerAux_descent_step
    {A B S R : ℤ}
    (W : EulerAuxWitness A B S R) :
    ∃ Anew Bnew Snew Rnew : ℤ,
      EulerAuxWitness Anew Bnew Snew Rnew ∧ Anew < A := by
  let P := EulerAux_param W
  let F := two_coprime_factorizations_refine_even_pos
    W.hApos
    P.hA_left P.hA_right
    P.hUpos P.hVpos P.hU'pos P.hV'pos
    P.hUeven P.hU'even P.hVodd P.hV'odd
    P.hUV_coprime P.hU'V'_coprime

  have hB_left_refined : B = (2*F.a*F.b)^2 - (F.c*F.d)^2 := by
    -- rewrite `P.hB_left` by `F.hU`, `F.hV`
    nlinarith [P.hB_left, F.hU, F.hV]

  have hB_right_refined : B = (2*(2*F.a*F.c))^2 - (F.b*F.d)^2 := by
    -- rewrite `P.hB_right` by `F.hU'`, `F.hV'`
    nlinarith [P.hB_right, F.hU', F.hV']

  have hbal :
      F.b^2 * (4*F.a^2 + F.d^2) =
        F.c^2 * (16*F.a^2 + F.d^2) :=
    EulerAux_balance_identity hB_left_refined hB_right_refined

  have hsq :
      (4*F.a^2 + F.d^2 = F.c^2) ∧
        (16*F.a^2 + F.d^2 = F.b^2) :=
    EulerAux_square_balance_consequence
      F.hapos F.hbpos F.hcpos F.hdpos
      (pairwise_bc F.hpair)
      (pairwise_ad F.hpair)
      F.hdodd
      hbal

  refine ⟨F.a, F.d, F.c, F.b, ?_, ?_⟩
  · refine ⟨F.hapos, F.hdpos, F.hdodd, ?_, F.hcpos, F.hbpos, ?_, ?_⟩
    · exact pairwise_ad F.hpair
    · -- `F.c^2 = (2*F.a)^2 + F.d^2`
      nlinarith [hsq.1]
    · -- `F.b^2 = (4*F.a)^2 + F.d^2`
      nlinarith [hsq.2]
  · exact EulerAux_measure_decrease F.hA F.hapos F.hbpos F.hcpos F.hdpos

end EulerAux
```

## 5. What is pure Lean algebra vs. real descent

```text
Pure Lean algebra/order after helpers:
  - `witness_left_triple`, `witness_right_triple`.
  - rewriting parametrized equations by refined factors.
  - `EulerAux_balance_identity`.
  - positivity of `4*a^2+d^2`, `16*a^2+d^2`.
  - constructing `EulerAuxWitness a d c b` from square-balance output.
  - `EulerAux_measure_decrease` from `A = 2*a*b*c*d` and positivity.

Small number-theory lemmas still needed:
  - `two_coprime_factorizations_refine_even_pos` if not already proved.
  - `coprime_four_sq_add_d_sq_sixteen_sq_add_d_sq`.

Real mathematical descent endpoint:
  - `EulerAux_descent_step` plus well-founded/minimal-counterexample packaging:
      from any witness, produce a strictly smaller witness.
  - final contradiction by choosing a witness with minimal positive `A`.
```
