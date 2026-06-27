# Q1339 (dm1/dm3): Lean structure for the `quartic_plus` infinite descent

The key Lean organization is:

1. Define the quartic equation as a subtraction-free Nat predicate.
2. Prove a **single descent step**: every non-base solution produces a non-base solution with smaller `B`.
3. Close the theorem by strong induction on `B`.

Important correction: for the Pythagorean classification, use the triple

```lean
PythagoreanTriple ((b : ℤ) ^ 2) h (r : ℤ)
```

not `PythagoreanTriple h ((b : ℤ)^2) r`, if you want the precise output

```lean
(b : ℤ)^2 = m^2 - n^2,
h = 2*m*n,
r = m^2 + n^2.
```

`PythagoreanTriple.coprime_classification'` assumes the **first leg is odd**. Here `b^2` is the odd leg; `h` is even.

## Strong induction wrapper on `B`

This wrapper is the part that should be fixed first. The descent step is the only real arithmetic work.

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

namespace DM1

/-- Subtraction-free form of `s^2 = r^4 + r^2 B^2 - B^4`. -/
def QuarticPlus (r B s : ℕ) : Prop :=
  0 < r ∧ 0 < B ∧ Nat.Coprime r B ∧
    s ^ 2 + B ^ 4 = r ^ 4 + r ^ 2 * B ^ 2

/-- The terminal/base solution. -/
def Base (r B : ℕ) : Prop :=
  r = 1 ∧ B = 1

/--
This is the shape of the arithmetic descent step.  The important point is that
it returns a smaller **non-base** solution, not merely a smaller solution.
-/
def DescentStep : Prop :=
  ∀ {r B s : ℕ}, QuarticPlus r B s → ¬ Base r B →
    ∃ r' B' s' : ℕ,
      QuarticPlus r' B' s' ∧ ¬ Base r' B' ∧ B' < B

/-- Strong-induction closure from a descent step. -/
theorem quarticPlus_base_of_descent
    (desc : DescentStep)
    {r B s : ℕ} (hsol : QuarticPlus r B s) :
    Base r B := by
  classical
  refine
    (Nat.strong_induction_on
      (p := fun B => ∀ r s : ℕ, QuarticPlus r B s → Base r B)
      B ?_) r s hsol
  intro B ih r s hsol
  by_cases hbase : Base r B
  · exact hbase
  · rcases desc hsol hbase with ⟨r', B', s', hsol', hnot', hlt⟩
    exact False.elim (hnot' (ih B' hlt r' s' hsol'))

end DM1
```

## Skeleton of the actual descent step

Inside `DescentStep`, after the factorization

```text
(2r^2+B^2-2s)(2r^2+B^2+2s)=5B^4
```

and the coprime odd split, the case

```text
U = a^4,
V = 5*b^4,
B = a*b
```

should be organized like this. I write the core algebra over `ℤ`; convert back to `ℕ` only at the very end.

```lean
namespace DM1

-- Local variables in the branch:
--   r B s a b : ℕ
--   hr : 0 < r, hB : 0 < B
--   habB : B = a * b
--   hsum : a^4 + 5*b^4 = 4*r^2 + 2*(a*b)^2
--   hab_coprime : Nat.Coprime a b
--   hodd_b : Odd b
--   hnonbase : ¬ Base r B

-- Work in integers for the half-difference.
-- If you are in the subcase `a > b`, use:
--   h = ((a:ℤ)^2 - (b:ℤ)^2) / 2
-- If you are in the subcase `a < b`, use the opposite sign.

/-- Local branch skeleton: the `a > b` case of `U=a^4, V=5b^4`. -/
lemma descent_case_a_gt_b_skeleton
    {r B s a b : ℕ}
    (hr : 0 < r) (hB : 0 < B)
    (habB : B = a * b)
    (hab_coprime : Nat.Coprime a b)
    (hodd_b : Odd b)
    (ha_gt_b : b < a)
    (hsum : a ^ 4 + 5 * b ^ 4 = 4 * r ^ 2 + 2 * (a * b) ^ 2)
    -- These are the local arithmetic facts you prove before calling classification.
    (hh_pos : 0 < (((a : ℤ) ^ 2 - (b : ℤ) ^ 2) / 2))
    (hh_even : Even (((a : ℤ) ^ 2 - (b : ℤ) ^ 2) / 2))
    (hgcd_b2_h : Int.gcd ((b : ℤ) ^ 2) (((a : ℤ) ^ 2 - (b : ℤ) ^ 2) / 2) = 1)
    (hfactor_coprime :
      ∀ {m n : ℤ}, Int.gcd m n = 1 →
        Int.gcd (m - n) (m + n) = 1)
    :
    ∃ r' B' s' : ℕ, QuarticPlus r' B' s' ∧ B' < B := by
  classical
  let h : ℤ := ((a : ℤ) ^ 2 - (b : ℤ) ^ 2) / 2

  -- Step 1: derive `h^2 + b^4 = r^2`.
  have hpy_eq : h ^ 2 + ((b : ℤ) ^ 2) ^ 2 = (r : ℤ) ^ 2 := by
    -- From `hsum`: `4*r^2 = (a^2-b^2)^2 + 4*b^4`.
    -- Then divide by 4 using the definition of `h`.
    -- In a real proof this is best as a separate lemma proved by `norm_num`/`ring_nf`.
    -- Typical local closer after coercing `hsum` to ℤ:
    --   have hsumZ : ... := by exact_mod_cast hsum
    --   dsimp [h]
    --   nlinarith [hsumZ]
    sorry

  -- Step 2: orient the Pythagorean triple with `b^2` first, because it is odd.
  have hpt : PythagoreanTriple ((b : ℤ) ^ 2) h (r : ℤ) := by
    dsimp [PythagoreanTriple]
    rw [add_comm]
    simpa [pow_two] using hpy_eq

  have hb2_odd : ((b : ℤ) ^ 2) % 2 = 1 := by
    -- from `hodd_b`; if needed:
    --   have hboddZ : Odd (b : ℤ) := hodd_b.natCast
    -- and then reduce modulo 2.
    sorry

  have hrZ_pos : 0 < (r : ℤ) := by exact_mod_cast hr

  -- Step 3: primitive Pythagorean parametrization.
  obtain ⟨m, n, hb2_mn, hh_2mn, hr_mn, hmn_gcd, hmn_parity, hm_nonneg⟩ :=
    hpt.coprime_classification' hgcd_b2_h hb2_odd hrZ_pos

  -- Now you have exactly:
  --   hb2_mn : (b:ℤ)^2 = m^2 - n^2
  --   hh_2mn : h = 2*m*n
  --   hr_mn  : (r:ℤ) = m^2 + n^2

  -- Step 4: factor `b^2 = (m-n)(m+n)`.
  have hprod : (m - n) * (m + n) = (b : ℤ) ^ 2 := by
    rw [hb2_mn]
    ring

  have hcop_factors : Int.gcd (m - n) (m + n) = 1 :=
    hfactor_coprime hmn_gcd

  -- Step 5: split coprime factors of a square.
  obtain ⟨u, hsub_u_or_neg⟩ :=
    Int.sq_of_gcd_eq_one hcop_factors hprod

  have hprod_comm : (m + n) * (m - n) = (b : ℤ) ^ 2 := by
    rw [mul_comm]
    exact hprod

  have hcop_factors_comm : Int.gcd (m + n) (m - n) = 1 := by
    rw [Int.gcd_comm]
    exact hcop_factors

  obtain ⟨v, hadd_v_or_neg⟩ :=
    Int.sq_of_gcd_eq_one hcop_factors_comm hprod_comm

  -- Step 6: use positivity of `m-n` and `m+n` to keep the positive square cases.
  -- You should have local facts:
  --   hmn_sub_pos : 0 < m - n
  --   hmn_add_pos : 0 < m + n
  -- Then:
  --   have hsub_u : m - n = u^2 := by cases hsub_u_or_neg with ...
  --   have hadd_v : m + n = v^2 := by cases hadd_v_or_neg with ...
  -- The negative alternatives contradict positivity since `-u^2 ≤ 0`.
  have hsub_u : m - n = u ^ 2 := by
    rcases hsub_u_or_neg with hpos | hneg
    · exact hpos
    · exfalso
      -- contradiction with positivity of `m-n`
      sorry

  have hadd_v : m + n = v ^ 2 := by
    rcases hadd_v_or_neg with hpos | hneg
    · exact hpos
    · exfalso
      -- contradiction with positivity of `m+n`
      sorry

  -- Step 7: `b = |u*v|`; in the positive branch this is `b = u.natAbs * v.natAbs`.
  have hb_uv_abs : b = u.natAbs * v.natAbs := by
    -- From `hprod`, `hsub_u`, `hadd_v`:
    --   (b:ℤ)^2 = (u*v)^2
    -- and positivity chooses the positive root.
    sorry

  -- Step 8: derive the new quartic equation.
  -- From `2*h = a^2 - b^2` and `2*h = v^4-u^4`, with `b = u*v`:
  have hnewZ :
      (a : ℤ) ^ 2 = v ^ 4 + v ^ 2 * u ^ 2 - u ^ 4 := by
    -- This is the key `ring`/`nlinarith` algebra step.
    -- Inputs: definition of h, hsub_u, hadd_v, hb_uv_abs.
    sorry

  -- Step 9: return the smaller solution `(r',B',s') = (v.natAbs, u.natAbs, a)`.
  refine ⟨v.natAbs, u.natAbs, a, ?_, ?_⟩
  · -- QuarticPlus v u a
    constructor
    · -- 0 < v.natAbs
      sorry
    constructor
    · -- 0 < u.natAbs
      sorry
    constructor
    · -- Coprime v u, inherited from the square-factor split.
      sorry
    · -- Convert `hnewZ` to the subtraction-free Nat equation.
      -- `norm_num [Int.natAbs_pow]` and `exact_mod_cast` are usually enough
      -- after proving `0 ≤ u`, `0 ≤ v`, or using natAbs throughout.
      sorry
  · -- strict descent: `u < u*v = b ≤ a*b = B`
    -- Use `0 < v`, `1 ≤ v`, and `habB : B = a*b`.
    -- In this branch the new B is `u.natAbs`.
    sorry

end DM1
```

## Where the other split branches plug in

For `U = a^4, V = 5b^4`:

* If `a = b`, coprimality gives `a=b=1`, hence `B=1`; the sum identity gives `r=1`, so this is the base case.
* If `a > b`, the branch above returns `(r',B',s') = (v,u,a)`.
* If `a < b`, use `h = (b^2-a^2)/2`; the new solution is `(r',B',s') = (u,v,a)`. To get strict descent `v < B`, prove `u ≠ 1`; if `u=1`, the resulting equation gives `a^2 = 1 + v^2 - v^4 < 0` for odd `v ≥ 3`.

For `U = 5a^4, V = b^4`, first use `U < V` to get `a < b`, then use `h = (b^2-a^2)/2`; the new solution is `(r',B',s') = (v,u,b)` with `u < uv = a ≤ ab = B`.

## Minimal theorem layout

Once all branch lemmas are implemented, define:

```lean
lemma quarticPlus_descent_step : DescentStep := by
  intro r B s hsol hnonbase
  -- build U,V; split `U*V = 5*B^4`; dispatch the four branches above
  -- every non-base branch returns `∃ r' B' s', QuarticPlus r' B' s' ∧ ¬ Base r' B' ∧ B' < B`
  sorry

theorem quarticPlus_base {r B s : ℕ} (hsol : QuarticPlus r B s) : Base r B := by
  exact quarticPlus_base_of_descent quarticPlus_descent_step hsol
```

The essential Lean point is to make `quarticPlus_descent_step` return a smaller **non-base** solution. If it only returns a smaller solution, the strong induction does not close.
