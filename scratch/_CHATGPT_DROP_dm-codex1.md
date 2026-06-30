# Q2712 (dm-codex1): audit of `N12RawBranchEuler` route

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Local file under audit: `FLT/Assumptions/MazurProof/N12RawBranchEuler.lean`  
Namespace: `MazurProof.RationalPointsN12`

## Verdict

The route is mathematically sound. I do not see a hidden parity or gcd obstruction in the construction of `EulerSquarePair` from either raw factor package. The key divisibility facts

```text
4 ∣ c   -- even-factor package
4 ∣ a   -- odd-factor package
```

really do follow from the stated identities, once the relevant oddness hypotheses are derived.

The only important caveat is dependency/architecture, not mathematics: a downstream file importing `N12QuarticEisenstein` can prove the contradiction theorem there, but do not import that downstream file back into `N12QuarticEisenstein` unless the import graph is arranged to avoid a cycle. If `DescentFromBranchUnorderedStatement` lives upstream, prove a downstream theorem with the same statement or move only the final theorem to a later assembly file.

## Step 1: no `EulerSquarePair` under descent

This is sound. Every `EulerSquarePair` has

```text
0 < E.A * E.D
```

from `hApos` and `hDpos`. If descent gives `F.A * F.D < E.A * E.D`, then positivity on both products lets `(·).natAbs` reflect the strict inequality. A `Nat.find` minimal counterexample on

```lean
fun k => ∃ E : EulerSquarePair, k = (E.A * E.D).natAbs
```

is a standard no-infinite-descent proof.

Lean-level risk: the only fragile line is usually the helper converting positive integer strict inequality to `natAbs` strict inequality. If `norm_num`/`exact_mod_cast` is brittle, prove it by `rcases Int.eq_succ_of_zero_lt hx` and `rcases Int.eq_succ_of_zero_lt hy`, then finish the resulting Nat inequality with `omega` or `exact_mod_cast`.

## Step 2: even raw factors

Open

```text
m - n = a^2,
m + n = b^2,
n = 2*c^2,
2*m - n = 2*d^2,
0 < a,b,c,d.
```

The algebra is correct:

```text
d^2 = a^2 + c^2,
b^2 = a^2 + 4*c^2.
```

Derivation:

```text
2*m - n = 2*d^2 and n = 2*c^2
  ⇒ m = c^2 + d^2.

m - n = a^2
  ⇒ a^2 = (c^2+d^2) - 2*c^2 = d^2 - c^2
  ⇒ d^2 = a^2 + c^2.

m + n = b^2
  ⇒ b^2 = (c^2+d^2) + 2*c^2 = d^2 + 3*c^2
          = a^2 + 4*c^2.
```

The parity chain is also correct:

```text
Odd m, Even n
  ⇒ Odd (m-n)
  ⇒ Odd (a^2)
  ⇒ Odd a.
```

Then from

```text
a^2 + c^2 = d^2
```

with `a` odd, `d` must be odd. If `d` were even, the equation is impossible modulo `4`; Lean can prove this by cases on the parity of `c`. With `a` and `d` odd, the standard mod-8 fact gives

```text
4 ∣ c.
```

Indeed odd squares are `1 mod 8`, so `c^2 = d^2 - a^2` is `0 mod 8`. If `c` were even but not divisible by `4`, then `c^2 ≡ 4 mod 8`; if `c` were odd, `c^2 ≡ 1 mod 8`. Both are impossible.

Thus writing `c = 4*t` and setting

```text
A0 = 2*t   -- so c = 2*A0, A0 > 0, and Even A0
D0 = a
B0 = b
C0 = d
```

constructs the requested `EulerSquarePair` fields:

```text
B0^2 = b^2 = a^2 + 4*c^2 = D0^2 + 16*A0^2,
C0^2 = d^2 = a^2 + c^2   = D0^2 + 4*A0^2.
```

The gcd field is sound, but it must use the branch coprimality:

```text
IsCoprime m n
⇒ IsCoprime (m-n) n
⇒ IsCoprime a^2 (2*c^2)
⇒ IsCoprime a c
⇒ IsCoprime (c/2) a.
```

The last step uses `(c/2) ∣ c`, implemented division-free as `c = 2*A0`, and symmetry of `IsCoprime`.

## Step 3: odd raw factors

Open

```text
m - n = 2*a^2,
m + n = 2*b^2,
n = c^2,
2*m - n = d^2,
0 < a,b,c,d.
```

The algebra is correct:

```text
b^2 = a^2 + c^2,
d^2 = 4*a^2 + c^2.
```

Derivation:

```text
m = a^2 + b^2,
n = b^2 - a^2 = c^2,
2*m - n = 2*(a^2+b^2) - c^2
        = 2*a^2 + 2*b^2 - (b^2-a^2)
        = 3*a^2 + b^2
        = 4*a^2 + c^2.
```

The parity chain is correct:

```text
Odd n, n = c^2
  ⇒ Odd c.
```

Then from

```text
c^2 + a^2 = b^2
```

with `c` odd, `b` is odd, and the same mod-8 lemma gives

```text
4 ∣ a.
```

Writing `a = 4*t` and setting

```text
A0 = 2*t   -- so a = 2*A0, A0 > 0, and Even A0
D0 = c
B0 = d
C0 = b
```

constructs the requested `EulerSquarePair` fields:

```text
B0^2 = d^2 = 4*a^2 + c^2 = 16*A0^2 + D0^2,
C0^2 = b^2 = a^2 + c^2   = 4*A0^2 + D0^2.
```

The gcd field is again sound and must use branch coprimality:

```text
IsCoprime m n
⇒ IsCoprime (m-n) n
⇒ IsCoprime (2*a^2) c^2
⇒ IsCoprime a c
⇒ IsCoprime (a/2) c.
```

The step `IsCoprime (2*a^2) c^2 ⇒ IsCoprime a c` is valid by the standard `IsCoprime` factor-monotonicity lemmas, not by any parity assumption. The final step uses `(a/2) ∣ a`, implemented as `a = 2*A0`.

## Critical Lean lemmas to check

These are the exact facts whose proof/API details are most likely to cause local Lean friction.

```lean
-- Positive integer product measure reflects strict descent through natAbs.
private lemma natAbs_lt_natAbs_of_pos_lt {x y : ℤ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x < y) :
    x.natAbs < y.natAbs := by
  -- robust proof: rcases `Int.eq_succ_of_zero_lt hx/hy`, then `omega`/`exact_mod_cast`.
  sorry

-- Robust mod-8 lemma, usually easiest by parity cases rather than modular APIs.
theorem four_dvd_of_odd_odd_sq_add_sq_eq_sq {x y z : ℤ}
    (hx : Odd x) (hy : Odd y) (h : x ^ 2 + z ^ 2 = y ^ 2) :
    (4 : ℤ) ∣ z := by
  -- cases on `Even z`; if `z = 2*t`, cases on `Even t`; odd/even contradictions by `ring_nf` + `omega`.
  sorry

-- Even branch gcd bridge.
private lemma isCoprime_half_c_a_of_even_raw
    {m n a c A0 : ℤ}
    (hcop : IsCoprime m n)
    (hma : m - n = a ^ 2)
    (hnc : n = 2 * c ^ 2)
    (hcA : c = 2 * A0) :
    IsCoprime A0 a := by
  -- IsCoprime (m-n) n
  -- → IsCoprime a^2 (2*c^2)
  -- → IsCoprime a c
  -- → IsCoprime A0 a using A0 ∣ c.
  sorry

-- Odd branch gcd bridge.
private lemma isCoprime_half_a_c_of_odd_raw
    {m n a c A0 : ℤ}
    (hcop : IsCoprime m n)
    (hma : m - n = 2 * a ^ 2)
    (hnc : n = c ^ 2)
    (haA : a = 2 * A0) :
    IsCoprime A0 c := by
  -- IsCoprime (m-n) n
  -- → IsCoprime (2*a^2) c^2
  -- → IsCoprime a c
  -- → IsCoprime A0 c using A0 ∣ a.
  sorry
```

The `sorry`s above are not mathematical gaps; they mark the four API-sensitive proof snippets to verify locally. The full construction is sound if these helpers are implemented as described.

## Final contradiction

Given

```lean
rawSqBranchFactorizationStatement :
  RawSqBranchFactorizationStatement

eulerSquarePairDescent :
  EulerSquarePairDescent
```

it is sound to prove

```lean
theorem rawSqBranchDescentFromFactorsStatement :
    RawSqBranchDescentFromFactorsStatement := by
  intro A N S m n hbranch hfac
  have hno : ¬ Nonempty EulerSquarePair :=
    no_eulerSquarePair_of_descent eulerSquarePairDescent
  apply hno
  rcases hfac with hEven | hOdd
  · exact rawEvenFactors_to_eulerSquarePair hbranch hEven.1 hEven.2
  · exact rawOddFactors_to_eulerSquarePair hbranch hOdd.1 hOdd.2
```

and then any residual whose conclusion is existential, such as `DescentFromBranchUnorderedStatement`, can be proved by deriving the raw factor disjunction from `rawSqBranchFactorizationStatement hbranch`, applying the contradiction theorem above, and closing by `False.elim`.

That last step is logically valid: this route proves the raw branch is impossible, which is stronger than producing a descendant from the raw branch.
