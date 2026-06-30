# Q2671: adversarial audit of the elementary Eisenstein-quartic descent branch

Target repo: `flt-ai`; likely target file: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`.

## Verdict

The **raw branch** formulas are sound, but only under the raw branch hypotheses

```lean
A ^ 2 = (m - n) * (m + n)
N ^ 2 = n * (2 * m - n)
S = m ^ 2 - m * n + n ^ 2
0 < n ∧ n < m ∧ Int.gcd m n = 1
```

Within that branch, the parity split is correct:

* `n` even: descent works; the smaller solution is `(e, f, d)` with `0 < e < f`, `gcd e f = 1`, and `f < N`.
* `n` odd and `m` even: impossible.
* `n` odd and `m` odd: descent works; the smaller solution is `(e, f, b)` with `0 < e < f`, `gcd e f = 1`, and `f < N`.

However, this is **not yet a global descent** for primitive Eisenstein quartics. Two things are missing:

1. **Unit sector:** `(A,N,S)=(1,1,1)` is primitive and has no smaller positive solution. Any theorem must either exclude it or return it as the base case.
2. **Divided-by-3 Eisenstein sector:** primitive Eisenstein triples are not exhausted by the raw formulas. There is also the sector
   ```lean
   3 * A ^ 2 = (m - n) * (m + n)
   3 * N ^ 2 = n * (2 * m - n)
   3 * S     = m ^ 2 - m * n + n ^ 2
   (3 : ℤ) ∣ m + n
   ```
   possibly after swapping `A` and `N`. This sector cannot be ignored merely because the triple is primitive. For ordinary Eisenstein triples, `(X,Y,Z)=(8,3,7)` comes from a divided-by-3 parametrization. For quartic-square triples, the unit `(1,1,1)` comes from `m=2,n=1`. A global proof must either prove the divided sector has only the unit square case, or give a descent for that sector too.

So the corrected roadmap is:

```lean
primitive quartic
  -> unit
   ∨ raw branch for (A,N)
   ∨ raw branch for (N,A)
   ∨ divided-by-3 branch for (A,N)
   ∨ divided-by-3 branch for (N,A)
```

Then prove descent for both raw orientations, and separately dispatch the divided branch.

## Recommended Lean setup

```lean
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic

namespace MazurProof.QuarticEisenstein

def EisensteinQuartic (A N S : ℤ) : Prop :=
  S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

structure RawSquareBranch (A N S m n : ℤ) : Prop where
  n_pos : 0 < n
  n_lt_m : n < m
  cop_mn : Int.gcd m n = 1
  hA : A ^ 2 = (m - n) * (m + n)
  hN : N ^ 2 = n * (2 * m - n)
  hS : S = m ^ 2 - m * n + n ^ 2

structure DividedSquareBranch (A N S m n : ℤ) : Prop where
  n_pos : 0 < n
  n_lt_m : n < m
  cop_mn : Int.gcd m n = 1
  three_dvd : (3 : ℤ) ∣ m + n
  hA : 3 * A ^ 2 = (m - n) * (m + n)
  hN : 3 * N ^ 2 = n * (2 * m - n)
  hS : 3 * S = m ^ 2 - m * n + n ^ 2
```

The branch equation itself gives the quartic equation:

```lean
theorem RawSquareBranch.quartic {A N S m n : ℤ}
    (h : RawSquareBranch A N S m n) : EisensteinQuartic A N S := by
  unfold EisensteinQuartic
  rw [h.hS]
  -- Use h.hA and h.hN; `nlinarith` or `ring_nf` after substituting.
  -- One robust route:
  --   have hA' : A ^ 2 = m ^ 2 - n ^ 2 := by nlinarith [h.hA]
  --   have hN' : N ^ 2 = 2*m*n - n ^ 2 := by nlinarith [h.hN]
  --   nlinarith [hA', hN']
  sorry
```

## Raw branch audit details

### Common factor facts

From `0 < n`, `n < m`, and `Int.gcd m n = 1`:

```lean
-- gcd(m-n,m+n) divides 2.
-- If m,n have opposite parity, it is 1.
-- If m,n are both odd, it is 2.

-- gcd(n,2*m-n) divides 2.
-- If n is odd, it is 1.
-- If n is even, then m is odd and it is 2.
```

For Lean, prove these as small divisibility/gcd lemmas before square extraction. Suggested residual statements:

```lean
theorem gcd_m_sub_n_m_add_n_eq_one_of_opp_parity
    {m n : ℤ} (hn : 0 < n) (hnm : n < m) (hcop : Int.gcd m n = 1)
    (hpar : Even m ∧ Odd n ∨ Odd m ∧ Even n) :
    Int.gcd (m - n) (m + n) = 1 := by
  -- Prime divisor of both divides 2*m and 2*n, hence divides 2.
  -- Opposite parity makes both factors odd, so 2 cannot divide either.
  sorry

theorem gcd_m_sub_n_m_add_n_eq_two_of_odd_odd
    {m n : ℤ} (hn : 0 < n) (hnm : n < m) (hcop : Int.gcd m n = 1)
    (hm : Odd m) (hnodd : Odd n) :
    Int.gcd (m - n) (m + n) = 2 := by
  -- Same divisibility bound, and both factors are even but not divisible by 4 together.
  sorry

theorem gcd_n_two_m_sub_n_eq_one_of_odd_n
    {m n : ℤ} (hcop : Int.gcd m n = 1) (hnodd : Odd n) :
    Int.gcd n (2 * m - n) = 1 := by
  -- Common prime divides n and 2*m, hence divides 2; odd n excludes 2.
  sorry

theorem gcd_half_n_half_two_m_sub_n_eq_one_of_even_n
    {m n : ℤ} (hn : 0 < n) (hcop : Int.gcd m n = 1) (hneven : Even n) :
    Int.gcd (n / 2) ((2 * m - n) / 2) = 1 := by
  -- First show m odd; both n and 2*m-n have exactly one common factor 2.
  sorry
```

Use `Int.sq_of_gcd_eq_one` or the earlier helper
`Int.exists_pos_sq_and_sq_of_mul_eq_sq_of_pos_of_isCoprime` for the square extractions.

## Case I: `n` even

Correct formulas:

```lean
n = 2 * c ^ 2
2 * m - n = 2 * d ^ 2
m - n = a ^ 2
m + n = b ^ 2
b - a = 2 * e ^ 2
b + a = 2 * f ^ 2
c = e * f
```

Then

```lean
d ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4
N = 2 * e * f * d
0 < e ∧ e < f
Int.gcd e f = 1
f < N
```

The proposed smaller triple `(e,f,|d|)` is sound; in Lean choose the positive root `d`, so no `abs` is needed.

Residual theorem statement:

```lean
theorem raw_branch_even_n_descends
    {A N S m n : ℤ} (hNpos : 0 < N)
    (h : RawSquareBranch A N S m n) (hneven : Even n) :
    ∃ e f d : ℤ,
      0 < e ∧ e < f ∧ 0 < d ∧ Int.gcd e f = 1 ∧
      f < N ∧ EisensteinQuartic e f d ∧
      ∃ a b c : ℤ,
        0 < a ∧ 0 < b ∧ 0 < c ∧
        n = 2 * c ^ 2 ∧
        2 * m - n = 2 * d ^ 2 ∧
        m - n = a ^ 2 ∧
        m + n = b ^ 2 ∧
        b - a = 2 * e ^ 2 ∧
        b + a = 2 * f ^ 2 ∧
        c = e * f := by
  -- 1. `hneven` + `h.cop_mn` gives `Odd m`.
  -- 2. Extract `n/2 = c^2`, `(2*m-n)/2 = d^2` from h.hN.
  -- 3. Extract `m-n = a^2`, `m+n = b^2` from h.hA.
  -- 4. Since `b^2-a^2 = 2*n = 4*c^2`, get
  --      ((b-a)/2) * ((b+a)/2) = c^2.
  -- 5. The two factors are coprime, hence squares: `(b-a)/2=e^2`, `(b+a)/2=f^2`.
  -- 6. Ring gives `d^2 = e^4 - e^2*f^2 + f^4`.
  -- 7. Positivity gives `0<e<f`, `N=2*e*f*d`, hence `f<N`.
  sorry
```

A particularly useful local identity for the final ring step:

```lean
example {a b c d e f m n : ℤ}
    (hn : n = 2 * c ^ 2)
    (hd : 2 * m - n = 2 * d ^ 2)
    (ha : m - n = a ^ 2)
    (hb : m + n = b ^ 2)
    (hba : b - a = 2 * e ^ 2)
    (hab : b + a = 2 * f ^ 2) :
    d ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4 := by
  nlinarith [hn, hd, ha, hb, hba, hab]
```

## Case II: `n` odd and `m` even

This case really is impossible. The clean contradiction is:

* `m-n` and `m+n` are positive, odd, coprime factors of `A^2`.
* Hence `m-n = a^2` and `m+n = b^2` with `a,b` odd.
* Odd squares are `1 mod 8`, so `2*n = (m+n)-(m-n)` is divisible by `8`.
* Thus `4 ∣ n`, contradicting `Odd n`.

Residual theorem statement:

```lean
theorem raw_branch_n_odd_m_even_impossible
    {A N S m n : ℤ}
    (h : RawSquareBranch A N S m n) (hnodd : Odd n) (hmeven : Even m) :
    False := by
  -- Extract squares from `(m-n)*(m+n)=A^2` using gcd=1.
  -- Then use odd-square mod 8.
  -- Reusable helper:
  --   odd_sq_modEq_one_mod_eight : Odd x -> x^2 ≡ 1 [ZMOD 8]
  sorry
```

Use this robust helper, already useful elsewhere:

```lean
private theorem odd_sq_modEq_one_mod_eight {x : ℤ} (hx : Odd x) :
    x ^ 2 ≡ 1 [ZMOD 8] := by
  rcases hx with ⟨k, rfl⟩
  rw [Int.modEq_iff_dvd]
  rcases Int.two_dvd_mul_add_one k with ⟨t, ht⟩
  refine ⟨-t, ?_⟩
  calc
    1 - (2 * k + 1) ^ 2 = -4 * (k * (k + 1)) := by ring
    _ = 8 * (-t) := by
      rw [ht]
      ring
```

## Case III: `n` odd and `m` odd

Correct formulas:

```lean
n = c ^ 2
2 * m - n = d ^ 2
m - n = 2 * a ^ 2
m + n = 2 * b ^ 2
d - c = 2 * e ^ 2
d + c = 2 * f ^ 2
a = e * f
```

Then

```lean
b ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4
N = c * d = (f ^ 2 - e ^ 2) * (f ^ 2 + e ^ 2)
0 < e ∧ e < f
Int.gcd e f = 1
f < N
```

The proposed smaller triple `(e,f,|b|)` is sound; again choose `0 < b`, so no `abs` is needed.

Residual theorem statement:

```lean
theorem raw_branch_odd_odd_descends
    {A N S m n : ℤ} (hNpos : 0 < N)
    (h : RawSquareBranch A N S m n) (hnodd : Odd n) (hmodd : Odd m) :
    ∃ e f b : ℤ,
      0 < e ∧ e < f ∧ 0 < b ∧ Int.gcd e f = 1 ∧
      f < N ∧ EisensteinQuartic e f b ∧
      ∃ a c d : ℤ,
        0 < a ∧ 0 < c ∧ 0 < d ∧
        n = c ^ 2 ∧
        2 * m - n = d ^ 2 ∧
        m - n = 2 * a ^ 2 ∧
        m + n = 2 * b ^ 2 ∧
        d - c = 2 * e ^ 2 ∧
        d + c = 2 * f ^ 2 ∧
        a = e * f := by
  -- 1. Extract `n=c^2`, `2*m-n=d^2` from h.hN, since gcd is 1.
  -- 2. Extract `(m-n)/2=a^2`, `(m+n)/2=b^2` from h.hA, since common gcd is 2.
  -- 3. From `d^2-c^2 = 2*(m-n) = 4*a^2`, split
  --      ((d-c)/2) * ((d+c)/2) = a^2.
  -- 4. The two factors are coprime, hence squares: `(d-c)/2=e^2`, `(d+c)/2=f^2`.
  -- 5. Ring gives `b^2 = e^4 - e^2*f^2 + f^4`.
  -- 6. Positivity gives `0<e<f`, `N=(f^2-e^2)*(f^2+e^2)`, hence `f<N`.
  sorry
```

Useful local identity:

```lean
example {a b c d e f m n : ℤ}
    (hn : n = c ^ 2)
    (hd : 2 * m - n = d ^ 2)
    (ha : m - n = 2 * a ^ 2)
    (hb : m + n = 2 * b ^ 2)
    (hda : d - c = 2 * e ^ 2)
    (had : d + c = 2 * f ^ 2) :
    b ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4 := by
  nlinarith [hn, hd, ha, hb, hda, had]
```

## Combined raw-branch descent

This is the theorem the proposed branch actually supports:

```lean
theorem raw_square_branch_descends
    {A N S m n : ℤ} (hNpos : 0 < N)
    (h : RawSquareBranch A N S m n) :
    ∃ A' N' S' : ℤ,
      0 < A' ∧ 0 < N' ∧ 0 < S' ∧
      Int.gcd A' N' = 1 ∧ N' < N ∧ EisensteinQuartic A' N' S' := by
  rcases Int.even_or_odd n with hneven | hnodd
  · obtain ⟨e, f, d, he, hef, hd, hef_cop, hfN, hquartic, _⟩ :=
      raw_branch_even_n_descends hNpos h hneven
    exact ⟨e, f, d, he, lt_trans he hef, hd, hef_cop, hfN, hquartic⟩
  · rcases Int.even_or_odd m with hmeven | hmodd
    · exact (raw_branch_n_odd_m_even_impossible h hnodd hmeven).elim
    · obtain ⟨e, f, b, he, hef, hb, hef_cop, hfN, hquartic, _⟩ :=
        raw_branch_odd_odd_descends hNpos h hnodd hmodd
      exact ⟨e, f, b, he, lt_trans he hef, hb, hef_cop, hfN, hquartic⟩
```

If the branch is obtained with `A` and `N` swapped, the same theorem gives a smaller second coordinate relative to the swapped old second coordinate, i.e. `N' < A` in the original names. Therefore a global minimal-counterexample proof should minimize a symmetric measure such as `max A N` or `A * N`, or explicitly swap the original counterexample before applying the branch.

## Missing divided-by-3 sector

This is the part the proposed descent does **not** cover. Do not silently assume it away.

A corrected parametrization theorem for primitive quartic-square Eisenstein triples should return these alternatives:

```lean
theorem primitive_quartic_square_param_branches
    {A N S : ℤ} (hA : 0 < A) (hN : 0 < N) (hS : 0 < S)
    (hcop : Int.gcd A N = 1)
    (hQ : EisensteinQuartic A N S) :
    (A = 1 ∧ N = 1 ∧ S = 1) ∨
      (∃ m n : ℤ, RawSquareBranch A N S m n) ∨
      (∃ m n : ℤ, RawSquareBranch N A S m n) ∨
      (∃ m n : ℤ, DividedSquareBranch A N S m n) ∨
      (∃ m n : ℤ, DividedSquareBranch N A S m n) := by
  -- This must come from the corrected Eisenstein-triple parametrization.
  -- The raw branches correspond to `¬ (3 : ℤ) ∣ m+n`.
  -- The divided branches correspond to `(3 : ℤ) ∣ m+n`.
  sorry
```

To finish a global descent, prove one of the following residual theorems. The first is stronger; the second is enough.

```lean
/-- Strong obstruction: no non-unit divided branch has both coordinates squares. -/
theorem divided_square_branch_unit
    {A N S m n : ℤ} (hA : 0 < A) (hN : 0 < N) (hS : 0 < S)
    (hcop : Int.gcd A N = 1)
    (h : DividedSquareBranch A N S m n) :
    A = 1 ∧ N = 1 ∧ S = 1 := by
  -- Not implied by parity alone. This is a real residual theorem.
  -- Start from:
  --   3*A^2 = (m-n)*(m+n), 3*N^2 = n*(2*m-n), 3 ∣ m+n.
  -- The prime 3 occurs in `m+n` and `2*m-n`, not in `m-n` or `n`.
  -- Analyze the remaining gcd-1 or gcd-2 factors as in the raw branch.
  sorry

/-- Weaker but sufficient: the divided branch either is the unit or descends. -/
theorem divided_square_branch_unit_or_descends
    {A N S m n : ℤ} (hA : 0 < A) (hN : 0 < N) (hS : 0 < S)
    (hcop : Int.gcd A N = 1)
    (h : DividedSquareBranch A N S m n) :
    (A = 1 ∧ N = 1 ∧ S = 1) ∨
      ∃ A' N' S' : ℤ,
        0 < A' ∧ 0 < N' ∧ 0 < S' ∧
        Int.gcd A' N' = 1 ∧ N' < N ∧ EisensteinQuartic A' N' S' := by
  -- Use this if the strong obstruction is not convenient.
  sorry
```

## Bottom line

The proposed case formulas are **correct for the raw branch** and the inequalities `f < N` are valid in Cases I and III. The smaller triples are primitive and nontrivial if positive square roots are chosen.

But the proof is not globally sound until the unit and divided-by-3 sectors are added to the statement and handled. The safest Lean roadmap is:

1. Prove `raw_branch_even_n_descends`.
2. Prove `raw_branch_n_odd_m_even_impossible`.
3. Prove `raw_branch_odd_odd_descends`.
4. Combine them into `raw_square_branch_descends`.
5. Fix the Eisenstein parametrization theorem so it returns raw/divided/swapped/unit branches.
6. Prove `divided_square_branch_unit` or `divided_square_branch_unit_or_descends`.
7. Only then state the global primitive Eisenstein quartic descent theorem.

end MazurProof.QuarticEisenstein
```