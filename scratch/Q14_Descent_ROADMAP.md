
═══ BRIDGE SUBMITTED  dm3 | task c7eb2b52 | 1583B in | "Q7 (dm3): Lean 4 / Mathlib. flt-ai. The HARD obstruction for…" ═══

[ask-gpt dm3 tid=c7eb2b52 +0s] dispatched, waiting for answer
[ask-gpt dm3 tid=c7eb2b52 +90s] waiting (status=processing)
[ask-gpt dm3 tid=c7eb2b52 +180s] waiting (status=processing)
[ask-gpt dm3 tid=c7eb2b52 +270s] waiting (status=processing)
[ask-gpt dm3 tid=c7eb2b52 +360s] waiting (status=processing)
[ask-gpt dm3 tid=c7eb2b52 +450s] waiting (status=processing)
[ask-gpt dm3 tid=c7eb2b52 +540s] waiting (status=processing)
[ask-gpt dm3 tid=c7eb2b52 +541s] terminal: status=completed

═══ BRIDGE RUN #37  dm3 | task c7eb2b52 | 12001 B | ✅ COMPLETE ═══

First, one correction: for

```text
v^2 + 22 v - 7
```

the discriminant is

```text
22^2 + 28 = 512 = 2^9,
```

not `480`. So the quadratic roots are

```text
-11 ± 8 * sqrt 2,
```

and the only rational 2-torsion point on

```text
Q14 : z² = v³ + 22v² - 7v
```

is `(0, 0)`.

I would **not** try to prove `obstruction_Q14` by a one-shot integer box. The correct mirror of the N10/20a4 proof is:

```text
rational point
→ denominator normalization v = A / B², z = C / B³
→ squareclass split A = d * M² with d ∈ {1, -1, 7, -7}
→ four quartic cases
→ d = -1 and d = 7 killed mod 16
→ d = 1 and d = -7 killed by the N10-style fourth-power split / descent tail
→ v ∈ {-7, 0, 1}
```

The analogue of the N10 “constant `5 / 48`” is:

```text
quadratic-factor discriminant squareclass: 2
quartic descent discriminant:             -7
factor-split constant:                    128 = 2^7
```

The two hard quartics are:

```text
d = 1:
  Y² = M⁴ + 22M²N² - 7N⁴
      = (M² + 11N²)² - 128N⁴

d = -7:
  Y² = -7M⁴ + 22M²N² + N⁴
      = (N² + 11M²)² - 128M⁴
```

So the Pellian/fourth-power split is literally:

```text
(M² + 11N² - Y)(M² + 11N² + Y) = 128N⁴

(N² + 11M² - Y)(N² + 11M² + Y) = 128M⁴
```

That is the place to port the N10 `fourth_power_split` + `Nat.strong_induction` tail.

---

## Exact descent equations

Start with a nonzero rational point:

```lean
z^2 = v^3 + 22*v^2 - 7*v
```

Normalize:

```text
v = A / B²,    z = C / B³,
gcd A B = 1,  B > 0.
```

Then:

```text
C² = A * (A² + 22*A*B² - 7*B⁴).
```

Because

```text
gcd(A, A² + 22*A*B² - 7*B⁴) ∣ 7,
```

the squareclass of `A` is one of:

```text
1, -1, 7, -7.
```

So there exist integers `d M N Y`, with `N > 0`, `IsCoprime M N`, and

```lean
d ∈ ({1, -1, 7, -7} : Finset ℤ)
```

such that

```text
v = d * (M / N)²
```

and

```text
d * Y² = d²*M⁴ + 22*d*M²*N² - 7*N⁴.
```

Expanding the four `d` cases gives:

```lean
-- d = 1
Y^2 = M^4 + 22*M^2*N^2 - 7*N^4

-- d = -1
Y^2 = -M^4 + 22*M^2*N^2 + 7*N^4

-- d = 7
Y^2 = 7*M^4 + 22*M^2*N^2 - N^4

-- d = -7
Y^2 = -7*M^4 + 22*M^2*N^2 + N^4
```

The `d = -1` and `d = 7` cases are local contradictions modulo `16`. The `d = 1` case forces `M² = N²`, hence `v = 1`. The `d = -7` case forces `M = 0 ∨ M² = N²`, hence `v = 0 ∨ v = -7`.

---

## Concrete Lean lemma DAG

Use these as the Q14-specific replacement for the N10 obstruction tail.

```lean
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

noncomputable section

open scoped BigOperators

lemma mem_Q14_target_rat {v : ℚ} :
    v ∈ ({-7, 0, 1} : Finset ℚ) ↔ v = -7 ∨ v = 0 ∨ v = 1 := by
  norm_num [Finset.mem_insert, Finset.mem_singleton]

lemma mem_Q14_squareclasses_int {d : ℤ} :
    d ∈ ({1, -1, 7, -7} : Finset ℤ) ↔
      d = 1 ∨ d = -1 ∨ d = 7 ∨ d = -7 := by
  norm_num [Finset.mem_insert, Finset.mem_singleton]
```

The first real descent lemma should be this one. It is the exact Q14 analogue of the N10 rational-denominator/squareclass split.

```lean
structure Q14DescentDatum (v z : ℚ) where
  d M N Y : ℤ
  d_mem : d ∈ ({1, -1, 7, -7} : Finset ℤ)
  N_pos : 0 < N
  coprime_MN : IsCoprime M N
  v_eq : v = (d : ℚ) * ((M : ℚ) / (N : ℚ))^2
  descent_eq :
    d * Y^2 = d^2 * M^4 + 22*d*M^2*N^2 - 7*N^4

/--
Squareclass descent for `Q14`.

This is obtained from `v = A/B²`, `z = C/B³`, then

`C² = A * (A² + 22*A*B² - 7*B⁴)`

and

`gcd A (A² + 22*A*B² - 7*B⁴) ∣ 7`.
-/
lemma Q14_squareclass_descent
    {v z : ℚ}
    (hv : v ≠ 0)
    (h : z^2 = v^3 + 22*v^2 - 7*v) :
    ∃ D : Q14DescentDatum v z, True := by
  -- Port the N10 denominator normalization:
  --   v = A / B², z = C / B³, gcd A B = 1.
  --
  -- Then:
  --   C² = A * (A² + 22*A*B² - 7*B⁴).
  --
  -- Compute:
  --   gcd(A, A² + 22*A*B² - 7*B⁴) ∣ 7.
  --
  -- Hence squareclass(A) ∈ {1, -1, 7, -7}.
  --
  -- Choose `d`, `M`, `N = B`, `Y` and package the equation:
  --   d * Y² = d²*M⁴ + 22*d*M²*N² - 7*N⁴.
  --
  -- This is the first lemma to port from `ObstructionN10*`.
  sorry
```

The two easy local cases should be separated and proved by finite residue checks modulo `16`.

```lean
/-- The `d = -1` quartic has no primitive integer solution. -/
lemma Q14_quartic_d_neg_one_no_solution
    {M N Y : ℤ}
    (hN : 0 < N)
    (hcop : IsCoprime M N)
    (h :
      Y^2 = -M^4 + 22*M^2*N^2 + 7*N^4) :
    False := by
  -- Mod 16 check.
  --
  -- For primitive `(M,N)`, at least one of `M,N` is odd.
  -- Enumerate the four parity/residue cases modulo 16.
  --
  -- Recommended implementation:
  --   1. Prove a finite `ZMod 16` lemma by `decide`.
  --   2. Apply it to `(M : ZMod 16)`, `(N : ZMod 16)`, `(Y : ZMod 16)`.
  --
  -- This should be much shorter than the descent tails.
  sorry

/-- The `d = 7` quartic has no primitive integer solution. -/
lemma Q14_quartic_d_pos_seven_no_solution
    {M N Y : ℤ}
    (hN : 0 < N)
    (hcop : IsCoprime M N)
    (h :
      Y^2 = 7*M^4 + 22*M^2*N^2 - N^4) :
    False := by
  -- Same mod 16 finite check.
  sorry
```

The two hard descent-tail lemmas are these.

```lean
/--
Hard Q14 descent tail, `d = 1`.

This is the exact analogue of the N10 fourth-power split + strong-induction tail.

Equation:

`Y² = M⁴ + 22M²N² - 7N⁴`

is rewritten as

`(M² + 11N² - Y)(M² + 11N² + Y) = 128N⁴`.

The conclusion is `M² = N²`, hence `v = 1`.
-/
lemma Q14_quartic_d_one_descent_tail
    {M N Y : ℤ}
    (hN : 0 < N)
    (hcop : IsCoprime M N)
    (h :
      Y^2 = M^4 + 22*M^2*N^2 - 7*N^4) :
    M^2 = N^2 := by
  -- Port N10 tail with constants:
  --   split constant: 128 = 2^7
  --   midpoint:       M² + 11N²
  --   discriminant:   -7
  --
  -- Factor:
  --   let A := M² + 11*N²
  --   (A - Y) * (A + Y) = 128 * N^4
  --
  -- Then use the existing:
  --   coprime_product_eq_fourth_power
  --
  -- The finite divisor split is over divisors of 128, not 48.
  -- The strong-induction measure is `Int.natAbs N`.
  sorry

/--
Hard Q14 descent tail, `d = -7`.

Equation:

`Y² = -7M⁴ + 22M²N² + N⁴`

is rewritten as

`(N² + 11M² - Y)(N² + 11M² + Y) = 128M⁴`.

The conclusion is `M = 0 ∨ M² = N²`, hence `v = 0 ∨ v = -7`.
-/
lemma Q14_quartic_d_neg_seven_descent_tail
    {M N Y : ℤ}
    (hN : 0 < N)
    (hcop : IsCoprime M N)
    (h :
      Y^2 = -7*M^4 + 22*M^2*N^2 + N^4) :
    M = 0 ∨ M^2 = N^2 := by
  -- Same N10 tail, with `M` and `N` interchanged in the factor split:
  --
  --   let A := N² + 11*M²
  --   (A - Y) * (A + Y) = 128 * M^4
  --
  -- The `M = 0` branch gives the rational point `v = 0`.
  sorry
```

Once those four quartic lemmas exist, the actual obstruction proof is short.

```lean
theorem obstruction_Q14
    (v z : ℚ)
    (h : z^2 = v^3 + 22*v^2 - 7*v) :
    v ∈ ({-7, 0, 1} : Finset ℚ) := by
  classical

  by_cases hv0 : v = 0
  · rw [hv0]
    norm_num

  obtain ⟨D, -⟩ := Q14_squareclass_descent hv0 h

  rw [mem_Q14_squareclasses_int] at D.d_mem
  rcases D.d_mem with hd | hd | hd | hd

  · -- d = 1, hence v = (M/N)^2 and the descent tail gives M² = N².
    subst hd

    have hq :
        D.Y^2 = D.M^4 + 22*D.M^2*D.N^2 - 7*D.N^4 := by
      simpa using D.descent_eq

    have hMN : D.M^2 = D.N^2 :=
      Q14_quartic_d_one_descent_tail
        (M := D.M) (N := D.N) (Y := D.Y)
        D.N_pos D.coprime_MN hq

    have hv : v = 1 := by
      rw [D.v_eq]
      field_simp [ne_of_gt D.N_pos]
      norm_num
      -- goal reduces to `D.M^2 = D.N^2`
      exact_mod_cast hMN

    rw [hv]
    norm_num

  · -- d = -1, impossible mod 16.
    subst hd

    have hq :
        D.Y^2 = -D.M^4 + 22*D.M^2*D.N^2 + 7*D.N^4 := by
      -- From
      --   (-1)*Y² = 1*M⁴ - 22*M²N² - 7N⁴
      -- multiply by `-1`.
      nlinarith [D.descent_eq]

    exact False.elim <|
      Q14_quartic_d_neg_one_no_solution
        (M := D.M) (N := D.N) (Y := D.Y)
        D.N_pos D.coprime_MN hq

  · -- d = 7, impossible mod 16.
    subst hd

    have hq :
        D.Y^2 = 7*D.M^4 + 22*D.M^2*D.N^2 - D.N^4 := by
      -- From
      --   7*Y² = 49*M⁴ + 154*M²N² - 7*N⁴
      -- divide by 7. `nlinarith` handles this over `ℤ` after normalization,
      -- but if it does not, cast to `ℚ`.
      nlinarith [D.descent_eq]

    exact False.elim <|
      Q14_quartic_d_pos_seven_no_solution
        (M := D.M) (N := D.N) (Y := D.Y)
        D.N_pos D.coprime_MN hq

  · -- d = -7, hence v = -7*(M/N)^2.
    subst hd

    have hq :
        D.Y^2 = -7*D.M^4 + 22*D.M^2*D.N^2 + D.N^4 := by
      -- From
      --   (-7)*Y² = 49*M⁴ - 154*M²N² - 7*N⁴
      -- divide by `-7`.
      nlinarith [D.descent_eq]

    have hMN :
        D.M = 0 ∨ D.M^2 = D.N^2 :=
      Q14_quartic_d_neg_seven_descent_tail
        (M := D.M) (N := D.N) (Y := D.Y)
        D.N_pos D.coprime_MN hq

    rcases hMN with hM0 | hM2
    · have hv : v = 0 := by
        rw [D.v_eq, hM0]
        norm_num
      contradiction

    · have hv : v = -7 := by
        rw [D.v_eq]
        field_simp [ne_of_gt D.N_pos]
        norm_num
        exact_mod_cast hM2

      rw [hv]
      norm_num
```

In practice, the two `nlinarith [D.descent_eq]` divisions over `ℤ` may need one of these patterns:

```lean
have hqQ : ((D.Y : ℚ)^2 =
    -7*(D.M : ℚ)^4 + 22*(D.M : ℚ)^2*(D.N : ℚ)^2 + (D.N : ℚ)^4) := by
  have hcast := congrArg (fun x : ℤ => (x : ℚ)) D.descent_eq
  norm_num at hcast ⊢
  nlinarith

exact_mod_cast hqQ
```

or prove the four specialized equations inside `Q14_squareclass_descent` so `obstruction_Q14` never has to divide by `d`.

---

## The finite `decide` box

This is useful **after** descent, not before. Do not try:

```lean
lemma ... (V Z : ℤ) (hV : V ∈ Icc ...) ... := by
  decide
```

That will not work well because `V Z : ℤ` are still unbounded variables. Instead define a finite bad set and prove it empty by `decide`.

```lean
def Q14IntegerBox : Finset (ℤ × ℤ) :=
  (Finset.Icc (-7 : ℤ) 1).product (Finset.Icc (-28 : ℤ) 28)

def Q14IntegerBad : Finset (ℤ × ℤ) :=
  Q14IntegerBox.filter fun P =>
    decide
      (P.2^2 = P.1^3 + 22*P.1^2 - 7*P.1 ∧
       P.1 ∉ ({-7, 0, 1} : Finset ℤ))

lemma Q14IntegerBad_empty :
    Q14IntegerBad = ∅ := by
  decide

lemma Q14_integer_box_complete
    {V Z : ℤ}
    (hV : V ∈ Finset.Icc (-7 : ℤ) 1)
    (hZ : Z ∈ Finset.Icc (-28 : ℤ) 28)
    (h : Z^2 = V^3 + 22*V^2 - 7*V) :
    V ∈ ({-7, 0, 1} : Finset ℤ) := by
  classical
  by_contra hbad

  have hpair : (V, Z) ∈ Q14IntegerBox := by
    simp [Q14IntegerBox, hV, hZ]

  have hmem : (V, Z) ∈ Q14IntegerBad := by
    simp [Q14IntegerBad, Q14IntegerBox, hpair, h, hbad]

  rw [Q14IntegerBad_empty] at hmem
  simpa using hmem
```

If you want a rational-to-integer-box theorem, its useful shape is:

```lean
lemma Q14_rational_point_integral_box
    {v z : ℚ}
    (h : z^2 = v^3 + 22*v^2 - 7*v) :
    ∃ V Z : ℤ,
      v = V ∧
      z = Z ∧
      V ∈ Finset.Icc (-7 : ℤ) 1 ∧
      Z ∈ Finset.Icc (-28 : ℤ) 28 := by
  -- This is equivalent in difficulty to `obstruction_Q14`.
  -- It follows from the squareclass descent plus the two descent tails.
  sorry
```

But for `order14_point_obstructed_by_X14_rank_zero`, the direct squareclass conclusion is cleaner than proving this box lemma.

---

## First lemma to dispatch

Start here:

```lean
lemma Q14_squareclass_descent
    {v z : ℚ}
    (hv : v ≠ 0)
    (h : z^2 = v^3 + 22*v^2 - 7*v) :
    ∃ D : Q14DescentDatum v z, True := by
  sorry
```

This validates all constants and prevents wasted work. The proof should mirror the N10 denominator normalization exactly; only the gcd computation changes:

```text
gcd(A, A² + 22*A*B² - 7*B⁴) ∣ 7
```

because modulo `A`,

```text
A² + 22*A*B² - 7*B⁴ ≡ -7*B⁴,
```

and `gcd(A, B) = 1`.

After that, port the two tail lemmas:

```lean
Q14_quartic_d_one_descent_tail
Q14_quartic_d_neg_seven_descent_tail
```

Those are the genuine grind. The local `d = -1` and `d = 7` cases are much easier than the N10 tails; they are finite mod-16 checks.

So: Q14 is **not harder conceptually** than the 20a4 obstruction, but it is still a real descent grind. The constants are cleaner in one respect (`128 = 2^7`) and messier in another (`-7` discriminant in the quartic tail).
