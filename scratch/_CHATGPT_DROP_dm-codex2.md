# Q2429 EulerAux gcd lemmas audit

## Verdict

Both proposed statements are mathematically true as written.

* Lemma A, `two_coprime_factorizations_refine_even`, is true.  The key is to divide the two even factors by `2`, prove a signed common refinement for two coprime factorizations of the same nonzero integer, then use `Q` and `V` odd to upgrade ordinary pairwise coprimality of `a,b,c,d` to coprimality of `2*a` with `b,c,d`.
* Lemma B, `square_factor_balance`, is true.  The hypothesis `Nat.Coprime M.natAbs N.natAbs` is essential; without it the statement is false.  Example without `hMN`: `b=2`, `c=3`, `M=45`, `N=20` gives `b^2*M = c^2*N = 180`, but `M ≠ c^2` and `N ≠ b^2`.

Minor shaping corrections only:

* In Lemma A, `hQ_odd` and `hV_odd` are logically redundant from `P`/`U` even, nonzero, and the two coprimality hypotheses, but keeping them is good for the Lean proof because they avoid an extra parity detour.
* In Lemma B, `hMpos` and `hNpos` can be weakened to `0 ≤ M` and `0 ≤ N`; some sign/nonnegativity assumption is necessary.  Without it, `b=c=1`, `M=N=-1` satisfies the equality and coprimality but not the conclusion.

## Lemma B: prove the Nat theorem first

This is the cleanest route.  The Int theorem should be only a `natAbs` wrapper plus positivity casts.

```lean
import Mathlib

namespace EulerAux

/-- Nat core for `square_factor_balance`. -/
theorem nat_square_factor_balance
    {b c M N : ℕ}
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : Nat.Coprime b c)
    (hMN : Nat.Coprime M N)
    (h : b^2 * M = c^2 * N) :
    M = c^2 ∧ N = b^2 := by
  -- Proof plan, with the intended APIs:
  --
  -- 1. Get square coprimality.
  --      have hcb2 : Nat.Coprime (c^2) (b^2) :=
  --        (hbc.symm.pow_left 2).pow_right 2
  --      have hbc2 : Nat.Coprime (b^2) (c^2) :=
  --        (hbc.pow_left 2).pow_right 2
  --
  -- 2. Euclid divisibility.
  --      have hc2_dvd_M : c^2 ∣ M := by
  --        apply hcb2.dvd_of_dvd_mul_left
  --        rw [h]
  --        exact dvd_mul_right (c^2) N
  --      have hb2_dvd_N : b^2 ∣ N := by
  --        apply hbc2.dvd_of_dvd_mul_left
  --        rw [← h]
  --        exact dvd_mul_right (b^2) M
  --
  -- 3. Write `M = c^2*k`, `N = b^2*l`.
  --      rcases hc2_dvd_M with ⟨k, rfl⟩
  --      rcases hb2_dvd_N with ⟨l, rfl⟩
  --
  -- 4. Cancel the nonzero common factor `b^2*c^2` from `h`.
  --      have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  --      have hcpos : 0 < c := Nat.pos_of_ne_zero hc
  --      have hprodpos : 0 < b^2 * c^2 := by positivity
  --      have hkl : k = l := by
  --        have h' : (b^2 * c^2) * k = (b^2 * c^2) * l := by
  --          simpa [mul_assoc, mul_left_comm, mul_comm] using h
  --        exact Nat.mul_left_cancel hprodpos h'
  --
  -- 5. Since the same `k` divides both rewritten factors and `M,N` are coprime,
  --    prove `k = 1` using `Nat.dvd_gcd` and `Nat.dvd_one.mp`.
  --      subst l
  --      have hk_dvd_gcd : k ∣ Nat.gcd (c^2*k) (b^2*k) :=
  --        Nat.dvd_gcd (dvd_mul_left k (c^2)) (dvd_mul_left k (b^2))
  --      have hk1 : k = 1 := by
  --        have : k ∣ 1 := by
  --          simpa [Nat.Coprime] using hk_dvd_gcd
  --        exact Nat.dvd_one.mp this
  --
  -- 6. Finish by `simp [hk1, pow_two]`.
  --
  -- This is intentionally left as the implementation recipe, not as an axiom.
  -- In the final Lean patch, replace this comment block by the steps above.
  sorry

end EulerAux
```

Important APIs for the Nat proof:

```lean
import Mathlib

#check Nat.Coprime.symm
#check Nat.Coprime.pow_left
#check Nat.Coprime.pow_right
#check Nat.Coprime.dvd_of_dvd_mul_left
#check Nat.dvd_gcd
#check Nat.dvd_one
#check Nat.mul_left_cancel
```

Then wrap the Nat theorem for integers.

```lean
import Mathlib

namespace EulerAux

/-- Tiny cast helper for the Int wrapper. -/
theorem Int.eq_sq_of_natAbs_eq_of_nonneg
    {M c : ℤ}
    (hM : 0 ≤ M)
    (h : M.natAbs = c.natAbs^2) :
    M = c^2 := by
  -- Proof plan:
  --   have hcast : (M.natAbs : ℤ) = (c.natAbs : ℤ)^2 := by exact_mod_cast h
  --   rewrite `(M.natAbs : ℤ)` to `M` using the nonnegative natAbs cast theorem,
  --   and rewrite `(c.natAbs : ℤ)^2` to `c^2` using `Int.natAbs_mul`/`Int.natAbs_pow`
  --   or simply `nlinarith [sq_nonneg c]` after normalizing absolute values.
  -- Useful APIs:
  --   Int.natAbs_mul
  --   Int.natAbs_pow
  --   Int.natAbs_eq_zero
  --   exact_mod_cast
  sorry

/-- Recommended Int-facing wrapper. -/
theorem square_factor_balance
    {b c M N : ℤ}
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hMpos : 0 < M) (hNpos : 0 < N)
    (hbc : Nat.Coprime b.natAbs c.natAbs)
    (hMN : Nat.Coprime M.natAbs N.natAbs)
    (h : b^2 * M = c^2 * N) :
    M = c^2 ∧ N = b^2 := by
  -- Proof plan:
  --
  -- 1. Take `Int.natAbs` of `h`.
  --      have hnat : b.natAbs^2 * M.natAbs = c.natAbs^2 * N.natAbs := by
  --        have hh := congrArg Int.natAbs h
  --        simpa [Int.natAbs_mul, Int.natAbs_pow, mul_assoc, mul_left_comm, mul_comm]
  --          using hh
  --
  -- 2. Convert nonzero factors.
  --      have hb0 : b.natAbs ≠ 0 := by
  --        intro h0; exact hb (Int.natAbs_eq_zero.mp h0)
  --      have hc0 : c.natAbs ≠ 0 := by
  --        intro h0; exact hc (Int.natAbs_eq_zero.mp h0)
  --
  -- 3. Apply `nat_square_factor_balance hb0 hc0 hbc hMN hnat`.
  --
  -- 4. Convert `M.natAbs = c.natAbs^2` and `N.natAbs = b.natAbs^2`
  --    back to integer equalities using `Int.eq_sq_of_natAbs_eq_of_nonneg` with
  --    `le_of_lt hMpos` and `le_of_lt hNpos`.
  sorry

end EulerAux
```

## Lemma A: reduce to a signed common-refinement lemma

Do not prove Lemma A directly.  First prove this signed refinement theorem for two coprime factorizations of the same nonzero integer.

```lean
import Mathlib

namespace EulerAux

/-- Ordinary pairwise coprimality for the signed common refinement. -/
def PairwiseCoprime4Int (a b c d : ℤ) : Prop :=
  Nat.Coprime a.natAbs b.natAbs ∧
  Nat.Coprime a.natAbs c.natAbs ∧
  Nat.Coprime a.natAbs d.natAbs ∧
  Nat.Coprime b.natAbs c.natAbs ∧
  Nat.Coprime b.natAbs d.natAbs ∧
  Nat.Coprime c.natAbs d.natAbs

/-- Euclid lemma over Int, routed through natAbs. -/
theorem Int.euclid_natAbs_left
    {x y z : ℤ}
    (hxy : Nat.Coprime x.natAbs y.natAbs)
    (hdiv : x ∣ y * z) :
    x ∣ z := by
  -- Proof plan:
  --   obtain nat divisibility using `Int.natAbs_dvd_natAbs.mpr hdiv`
  --   simplify with `Int.natAbs_mul`
  --   apply `hxy.dvd_of_dvd_mul_left`
  --   convert back using `Int.natAbs_dvd_natAbs.mp`
  sorry

/-- If `a ∣ x` and `b ∣ y`, coprimality descends from `x,y` to `a,b`. -/
theorem Int.coprime_natAbs_of_dvd_of_dvd
    {a b x y : ℤ}
    (hxy : Nat.Coprime x.natAbs y.natAbs)
    (ha : a ∣ x)
    (hb : b ∣ y) :
    Nat.Coprime a.natAbs b.natAbs := by
  -- Proof plan:
  --   convert `ha`, `hb` to Nat divisibility using `Int.natAbs_dvd_natAbs`
  --   use `hxy.coprime_dvd_left` and `Nat.Coprime.coprime_dvd_right`
  sorry

/-- GCD splitting: write two nonzero Ints as `a*b` and `a*c` with `b,c` coprime. -/
theorem Int.exists_gcd_factor_coprime
    {X R : ℤ}
    (hXR : X ≠ 0 ∨ R ≠ 0) :
    ∃ a b c : ℤ,
      X = a*b ∧ R = a*c ∧ a ≠ 0 ∧
      Nat.Coprime b.natAbs c.natAbs := by
  -- Proof plan:
  --   take `a = (Int.gcd X R : ℤ)`
  --   use `Int.gcd_dvd_left` and `Int.gcd_dvd_right` to obtain `b,c`
  --   use the quotient-after-gcd coprime theorem; if no Int theorem is already
  --   convenient, prove the Nat version and transfer via natAbs:
  --        Nat.Coprime (X.natAbs / Nat.gcd X.natAbs R.natAbs)
  --                    (R.natAbs / Nat.gcd X.natAbs R.natAbs)
  --   under `X ≠ 0 ∨ R ≠ 0`.
  sorry

/-- Signed common refinement of two coprime factorizations. -/
theorem Int.coprime_factorizations_refine_signed
    {X Y R S : ℤ}
    (h : X*Y = R*S)
    (hXY : Nat.Coprime X.natAbs Y.natAbs)
    (hRS : Nat.Coprime R.natAbs S.natAbs)
    (hX : X ≠ 0) (hY : Y ≠ 0) (hR : R ≠ 0) (hS : S ≠ 0) :
    ∃ a b c d : ℤ,
      X = a*b ∧ Y = c*d ∧ R = a*c ∧ S = b*d ∧
      a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧
      PairwiseCoprime4Int a b c d := by
  -- Proof plan:
  --
  -- 1. Apply `Int.exists_gcd_factor_coprime` to `X,R`:
  --      X = a*b, R = a*c, gcd(b,c)=1, a ≠ 0.
  --
  -- 2. Substitute into `h` and cancel `a`:
  --      have hbcYS : b*Y = c*S := ...
  --
  -- 3. Since `c ∣ b*Y` and `gcd(c,b)=1`, use `Int.euclid_natAbs_left`
  --    to get `c ∣ Y`; write `Y = c*d`.
  --
  -- 4. Substitute `Y = c*d` into `b*Y = c*S` and cancel `c ≠ 0` to get
  --    `S = b*d`.
  --
  -- 5. Nonzero facts follow from nonzero products.
  --
  -- 6. Pairwise coprimality follows by descent from `hXY` and `hRS`:
  --      a,c,d from `a ∣ X`, `c ∣ Y`, `d ∣ Y`;
  --      a,b,d from `a ∣ R`, `b ∣ S`, `d ∣ S`;
  --      b,c from the gcd split.
  sorry

end EulerAux
```

The exact APIs to target for this section are:

```lean
import Mathlib

#check Int.gcd
#check Int.gcd_dvd_left
#check Int.gcd_dvd_right
#check Int.dvd_gcd
#check Int.natAbs_mul
#check Int.natAbs_eq_zero
#check Int.natAbs_dvd_natAbs
#check Nat.Coprime.coprime_dvd_left
#check Nat.Coprime.coprime_dvd_right
#check Nat.Coprime.dvd_of_dvd_mul_left
```

## Parity upgrade for Lemma A

After applying `Int.coprime_factorizations_refine_signed` to the halved factorizations, the remaining work is parity bookkeeping.

```lean
import Mathlib

namespace EulerAux

/-- Product odd implies left factor odd. -/
theorem Int.odd_left_of_odd_mul {x y : ℤ} (h : Odd (x*y)) : Odd x := by
  -- Proof plan:
  --   cases `Int.even_or_odd x`.
  --   If `x` is even, `x*y` is even by `Even.mul_right`, contradicting `h.not_even`.
  --   Otherwise done.
  sorry

/-- Product odd implies right factor odd. -/
theorem Int.odd_right_of_odd_mul {x y : ℤ} (h : Odd (x*y)) : Odd y := by
  -- Proof plan:
  --   use `Int.odd_left_of_odd_mul` after rewriting by `mul_comm`.
  sorry

/-- Upgrade `gcd(a,x)=1` to `gcd(2*a,x)=1` when `x` is odd. -/
theorem nat_coprime_two_mul_natAbs_of_odd_right
    {a x : ℤ}
    (hax : Nat.Coprime a.natAbs x.natAbs)
    (hx : Odd x) :
    Nat.Coprime (2*a).natAbs x.natAbs := by
  -- Proof plan:
  --   have h2x : Nat.Coprime 2 x.natAbs := by
  --     translate `Odd x` to `x.natAbs % 2 = 1` or `¬ 2 ∣ x.natAbs`.
  --   simp [Int.natAbs_mul]
  --   exact h2x.mul_left hax   -- or `Nat.Coprime.mul_left h2x hax`, depending on local notation.
  sorry

end EulerAux
```

Then the final theorem is a wrapper:

```lean
import Mathlib

namespace EulerAux

def PairwiseCoprime2abcd (a b c d : ℤ) : Prop :=
  Nat.Coprime (2*a).natAbs b.natAbs ∧
  Nat.Coprime (2*a).natAbs c.natAbs ∧
  Nat.Coprime (2*a).natAbs d.natAbs ∧
  Nat.Coprime b.natAbs c.natAbs ∧
  Nat.Coprime b.natAbs d.natAbs ∧
  Nat.Coprime c.natAbs d.natAbs

theorem two_coprime_factorizations_refine_even
    {A P Q U V : ℤ}
    (hPQ : A = P*Q) (hUV : A = U*V)
    (hP_even : Even P) (hU_even : Even U)
    (hQ_odd : Odd Q) (hV_odd : Odd V)
    (hcopPQ : Nat.Coprime P.natAbs Q.natAbs)
    (hcopUV : Nat.Coprime U.natAbs V.natAbs)
    (hA : A ≠ 0) :
    ∃ a b c d : ℤ,
      P = 2*a*b ∧ Q = c*d ∧ U = 2*a*c ∧ V = b*d ∧
      A = 2*a*b*c*d ∧
      a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧ Odd d ∧
      PairwiseCoprime2abcd a b c d := by
  -- Proof plan:
  --
  -- 1. Destructure evenness:
  --      obtain ⟨X, hP2⟩ := hP_even
  --      obtain ⟨R, hU2⟩ := hU_even
  --    Normalize `hP2`, `hU2` to `P = 2*X`, `U = 2*R` by `ring`/`omega`.
  --
  -- 2. From `hPQ`, `hUV`, cancel the common factor `2` and prove:
  --      hcore : X*Q = R*V
  --
  -- 3. From `hA`, prove `P,Q,U,V,X,R` are all nonzero.
  --
  -- 4. Descend coprimality from `P=2*X` to `X`:
  --      have hcopXQ : Nat.Coprime X.natAbs Q.natAbs :=
  --        hcopPQ.coprime_dvd_left <| by
  --          -- show `X.natAbs ∣ P.natAbs` using `hP2` and `Int.natAbs_mul`
  --      have hcopRV : Nat.Coprime R.natAbs V.natAbs := similarly
  --
  -- 5. Apply `Int.coprime_factorizations_refine_signed hcore hcopXQ hcopRV`:
  --      X = a*b, Q = c*d, R = a*c, V = b*d,
  --      plus ordinary pairwise coprimality.
  --
  -- 6. Rebuild the requested equations:
  --      P = 2*a*b, U = 2*a*c, A = 2*a*b*c*d.
  --
  -- 7. From `hQ_odd` and `Q = c*d`, derive `Odd c` and `Odd d`.
  --    From `hV_odd` and `V = b*d`, derive `Odd b` and another `Odd d`.
  --
  -- 8. Upgrade ordinary pairwise coprimality to `PairwiseCoprime2abcd` using
  --    `nat_coprime_two_mul_natAbs_of_odd_right` for `b`, `c`, and `d`.
  sorry

end EulerAux
```

## Recommended final local theorem DAG

Use this order in `EulerAux`:

1. `nat_square_factor_balance`.
2. `Int.eq_sq_of_natAbs_eq_of_nonneg`.
3. `square_factor_balance` as the Int wrapper.
4. `Int.euclid_natAbs_left`.
5. `Int.coprime_natAbs_of_dvd_of_dvd`.
6. `Int.exists_gcd_factor_coprime`.
7. `Int.coprime_factorizations_refine_signed`.
8. `Int.odd_left_of_odd_mul`, `Int.odd_right_of_odd_mul`.
9. `nat_coprime_two_mul_natAbs_of_odd_right`.
10. `two_coprime_factorizations_refine_even`.

This DAG keeps the two hard lemmas small.  Lemma B becomes mostly a Nat divisibility/cancellation proof.  Lemma A becomes a wrapper around a reusable signed refinement theorem plus parity upgrade, rather than a large one-off gcd proof.
