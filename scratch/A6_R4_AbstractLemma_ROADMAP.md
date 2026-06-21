
═══ BRIDGE  Q18 →dm3  SUBMITTED ═══
     "Q14 (dm3): A6-height design R4. Lean 4 / Mathlib. The PURE ABSTRACT fi…"
     ↳ debug: task f951ccbe

[ask-gpt Q18 dm3 tid=f951ccbe +0s] dispatched, waiting for answer
[ask-gpt Q18 dm3 tid=f951ccbe +90s] waiting (status=processing)
[ask-gpt Q18 dm3 tid=f951ccbe +180s] waiting (status=processing)
[ask-gpt Q18 dm3 tid=f951ccbe +270s] waiting (status=processing)
[ask-gpt Q18 dm3 tid=f951ccbe +360s] waiting (status=processing)
[ask-gpt Q18 dm3 tid=f951ccbe +450s] waiting (status=processing)
[ask-gpt Q18 dm3 tid=f951ccbe +540s] waiting (status=processing)
[ask-gpt Q18 dm3 tid=f951ccbe +586s] terminal: status=completed

═══ BRIDGE  Q18 →dm3  ✅ COMPLETE (21.3KB, 9m46s) ═══
     "Q14 (dm3): A6-height design R4. Lean 4 / Mathlib. The PURE ABSTRACT fi…"
     ↳ debug: task f951ccbe

I’ll inspect the available FLT/N10 obstruction files first to match the landed descent skeleton and constants, then translate it to Q14 and flag any inaccessible or genuinely new arithmetic kernel.

I can’t see the scratch files, so I’ll reconstruct the descent from Q14 itself. A key correction is that the discriminant is 512, making the bad squareclasses ±1, ±2, ±7, ±14, not just divisors of -7.

First, one correction: for

v^2 + 22 v - 7

the discriminant is

22^2 + 28 = 512 = 2^9,

not 480. So the quadratic roots are

-11 ± 8 * sqrt 2,

and the only rational 2-torsion point on

Q14 : z² = v³ + 22v² - 7v

is (0, 0).

I would not try to prove obstruction_Q14 by a one-shot integer box. The correct mirror of the N10/20a4 proof is:

rational point
→ denominator normalization v = A / B², z = C / B³
→ squareclass split A = d * M² with d ∈ {1, -1, 7, -7}
→ four quartic cases
→ d = -1 and d = 7 killed mod 16
→ d = 1 and d = -7 killed by the N10-style fourth-power split / descent tail
→ v ∈ {-7, 0, 1}

The analogue of the N10 “constant 5 / 48” is:

quadratic-factor discriminant squareclass: 2
quartic descent discriminant:             -7
factor-split constant:                    128 = 2^7

The two hard quartics are:

d = 1:
  Y² = M⁴ + 22M²N² - 7N⁴
      = (M² + 11N²)² - 128N⁴

d = -7:
  Y² = -7M⁴ + 22M²N² + N⁴
      = (N² + 11M²)² - 128M⁴

So the Pellian/fourth-power split is literally:

(M² + 11N² - Y)(M² + 11N² + Y) = 128N⁴

(N² + 11M² - Y)(N² + 11M² + Y) = 128M⁴

That is the place to port the N10 fourth_power_split + Nat.strong_induction tail.

Exact descent equations

Start with a nonzero rational point:

lean
z^2 = v^3 + 22*v^2 - 7*v

Normalize:

v = A / B²,    z = C / B³,
gcd A B = 1,  B > 0.

Then:

C² = A * (A² + 22*A*B² - 7*B⁴).

Because

gcd(A, A² + 22*A*B² - 7*B⁴) ∣ 7,

the squareclass of A is one of:

1, -1, 7, -7.

So there exist integers d M N Y, with N > 0, IsCoprime M N, and

lean
d ∈ ({1, -1, 7, -7} : Finset ℤ)

such that

v = d * (M / N)²

and

d * Y² = d²*M⁴ + 22*d*M²*N² - 7*N⁴.

Expanding the four d cases gives:

lean
-- d = 1
Y^2 = M^4 + 22*M^2*N^2 - 7*N^4

-- d = -1
Y^2 = -M^4 + 22*M^2*N^2 + 7*N^4

-- d = 7
Y^2 = 7*M^4 + 22*M^2*N^2 - N^4

-- d = -7
Y^2 = -7*M^4 + 22*M^2*N^2 + N^4

The d = -1 and d = 7 cases are local contradictions modulo 16. The d = 1 case forces M² = N², hence v = 1. The d = -7 case forces M = 0 ∨ M² = N², hence v = 0 ∨ v = -7.

Concrete Lean lemma DAG

Use these as the Q14-specific replacement for the N10 obstruction tail.

lean
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

The first real descent lemma should be this one. It is the exact Q14 analogue of the N10 rational-denominator/squareclass split.

lean
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

The two easy local cases should be separated and proved by finite residue checks modulo 16.

lean
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

The two hard descent-tail lemmas are these.

lean
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

Once those four quartic lemmas exist, the actual obstruction proof is short.

lean
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

In practice, the two nlinarith [D.descent_eq] divisions over ℤ may need one of these patterns:

lean
have hqQ : ((D.Y : ℚ)^2 =
    -7*(D.M : ℚ)^4 + 22*(D.M : ℚ)^2*(D.N : ℚ)^2 + (D.N : ℚ)^4) := by
  have hcast := congrArg (fun x : ℤ => (x : ℚ)) D.descent_eq
  norm_num at hcast ⊢
  nlinarith

exact_mod_cast hqQ

or prove the four specialized equations inside Q14_squareclass_descent so obstruction_Q14 never has to divide by d.

The finite decide box

This is useful after descent, not before. Do not try:

lean
lemma ... (V Z : ℤ) (hV : V ∈ Icc ...) ... := by
  decide

That will not work well because V Z : ℤ are still unbounded variables. Instead define a finite bad set and prove it empty by decide.

lean
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

If you want a rational-to-integer-box theorem, its useful shape is:

lean
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

But for order14_point_obstructed_by_X14_rank_zero, the direct squareclass conclusion is cleaner than proving this box lemma.

First lemma to dispatch

Start here:

lean
lemma Q14_squareclass_descent
    {v z : ℚ}
    (hv : v ≠ 0)
    (h : z^2 = v^3 + 22*v^2 - 7*v) :
    ∃ D : Q14DescentDatum v z, True := by
  sorry

This validates all constants and prevents wasted work. The proof should mirror the N10 denominator normalization exactly; only the gcd computation changes:

gcd(A, A² + 22*A*B² - 7*B⁴) ∣ 7

because modulo A,

A² + 22*A*B² - 7*B⁴ ≡ -7*B⁴,

and gcd(A, B) = 1.

After that, port the two tail lemmas:

lean
Q14_quartic_d_one_descent_tail
Q14_quartic_d_neg_seven_descent_tail

Those are the genuine grind. The local d = -1 and d = 7 cases are much easier than the N10 tails; they are finite mod-16 checks.

So: Q14 is not harder conceptually than the 20a4 obstruction, but it is still a real descent grind. The constants are cleaner in one respect (128 = 2^7) and messier in another (-7 discriminant in the quartic tail).

e2e ok

I’ll first align with the repo’s height/Northcott names, then isolate the pure torsion-finiteness lemma before wiring it into the A6 elliptic-height chain.

I’ll use the standard sublevel-finiteness form of Northcott; if your repo packages it as a structure or class, only a thin adapter should change.

The abstract lemma is sound, and the clean proof is even simpler than the “2^k orbit is bounded” version: take the finite cyclic subgroup generated by a torsion element, choose a point where h is maximal, and use closure under doubling.

Mathlib facts used below: IsOfFinAddOrder.exists_nsmul_eq_zero, AddCommGroup.mem_torsion, Set.Finite.fintype, Finite.of_injective, Finset.max', Finset.max'_mem, and Finset.max'_le_iff. Mathlib’s torsion subgroup is AddCommGroup.torsion, with membership characterized by IsOfFinAddOrder; finite sets expose a Finite.fintype; and Finset.max' is the nonempty finite-set maximum API. 
GitHub
+2
GitHub
+2

1. Abstract lemma
lean
import Mathlib.GroupTheory.Torsion
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section

open Function

/--
`Northcott h` means that every height sublevel set is finite.
-/
def Northcott {G : Type*} (h : G → ℝ) : Prop :=
  ∀ B : ℝ, ({g : G | h g ≤ B} : Set G).Finite

private lemma nsmul_mod_eq_of_nsmul_eq_zero
    {G : Type*} [AddCommGroup G]
    {g : G} {n m : ℕ}
    (hn : n • g = 0) :
    (m % n) • g = m • g := by
  rw [← Nat.mod_add_div m n]
  rw [add_nsmul, mul_nsmul, hn, nsmul_zero, add_zero]

/--
If `g` is torsion and `h(2g) ≥ 4h(g)-C`, then `h g ≤ C/3`.

Proof idea: choose `n > 0` with `n • g = 0`. On the finite set
`{i • g | i < n}`, choose `x` maximizing `h`. Since the set is closed under
doubling, `h(2x) ≤ h(x)`. The doubling inequality gives
`4h(x)-C ≤ h(2x) ≤ h(x)`, hence `h(x) ≤ C/3`. Since `g` is in the same finite
set, `h(g) ≤ h(x) ≤ C/3`.
-/
lemma height_le_of_isOfFinAddOrder
    {G : Type*} [AddCommGroup G]
    (h : G → ℝ) (C : ℝ)
    (hdouble : ∀ g : G, 4 * h g - C ≤ h (2 • g))
    {g : G}
    (hg : IsOfFinAddOrder g) :
    h g ≤ C / 3 := by
  classical

  rcases hg.exists_nsmul_eq_zero with ⟨n, hn_pos, hn_g⟩

  let S : Finset G := (Finset.range n).image fun i : ℕ => i • g

  have hg_mem_S : g ∈ S := by
    refine Finset.mem_image.mpr ?_
    refine ⟨1 % n, Finset.mem_range.mpr (Nat.mod_lt 1 hn_pos), ?_⟩
    calc
      (1 % n) • g = 1 • g :=
        nsmul_mod_eq_of_nsmul_eq_zero (g := g) (n := n) (m := 1) hn_g
      _ = g := by simp

  have hS_nonempty : S.Nonempty := ⟨g, hg_mem_S⟩

  let vals : Finset ℝ := S.image h

  have hvals_nonempty : vals.Nonempty :=
    hS_nonempty.image h

  let M : ℝ := vals.max' hvals_nonempty

  have hM_mem : M ∈ vals := by
    exact Finset.max'_mem vals hvals_nonempty

  rcases Finset.mem_image.mp hM_mem with ⟨x, hx_mem_S, hx_max⟩

  have h_le_M : ∀ y : G, y ∈ S → h y ≤ M := by
    intro y hy
    have hy_val : h y ∈ vals := by
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    have h_all :
        ∀ a ∈ vals, a ≤ M := by
      simpa [M] using
        ((Finset.max'_le_iff
          (s := vals)
          (H := hvals_nonempty)
          (x := M)).mp le_rfl)
    exact h_all (h y) hy_val

  have hdouble_closed : 2 • x ∈ S := by
    rcases Finset.mem_image.mp hx_mem_S with ⟨i, hi_mem, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨(2 * i) % n,
      Finset.mem_range.mpr (Nat.mod_lt (2 * i) hn_pos),
      ?_⟩
    calc
      ((2 * i) % n) • g = (2 * i) • g :=
        nsmul_mod_eq_of_nsmul_eq_zero
          (g := g) (n := n) (m := 2 * i) hn_g
      _ = 2 • (i • g) := by
        rw [mul_nsmul]

  have hx2_le_M : h (2 • x) ≤ M :=
    h_le_M (2 • x) hdouble_closed

  have hdouble_x : 4 * h x - C ≤ h (2 • x) :=
    hdouble x

  have hM_le : M ≤ C / 3 := by
    nlinarith [hdouble_x, hx2_le_M, hx_max]

  exact (h_le_M g hg_mem_S).trans hM_le

/--
Pure abstract finiteness theorem.

No elliptic curves, no canonical height, no Mordell-Weil.
-/
theorem finite_torsion_of_northcott_double_lower
    {G : Type*} [AddCommGroup G]
    (h : G → ℝ) (C : ℝ)
    (hNorthcott : Northcott h)
    (hdouble : ∀ g : G, 4 * h g - C ≤ h (2 • g)) :
    Finite (AddCommGroup.torsion G) := by
  classical

  let B : ℝ := C / 3
  let S : Set G := {g : G | h g ≤ B}

  have hS_finite : S.Finite := hNorthcott B

  letI : Fintype S := hS_finite.fintype
  haveI : Finite S := inferInstance

  let incl : AddCommGroup.torsion G → S :=
    fun T =>
      ⟨T.1, by
        change h T.1 ≤ B
        exact height_le_of_isOfFinAddOrder
          (h := h)
          (C := C)
          hdouble
          ((AddCommGroup.mem_torsion T.1).mp T.2)⟩

  have hincl : Function.Injective incl := by
    intro A B hAB
    apply Subtype.ext
    exact congrArg Subtype.val hAB

  exact Finite.of_injective incl hincl

The proof deliberately avoids limits, bounded sequences, and 2^k estimates. The finite cyclic subgroup maximum is the robust Lean version.

2. Wiring for A6

Use whatever your actual R2/R3 names are, but the clean target shapes should be these.

lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.Torsion

open scoped WeierstrassCurve.Affine
open WeierstrassCurve
open WeierstrassCurve.Affine

noncomputable section

abbrev RatPts (E : WeierstrassCurve ℚ) [E.IsElliptic] : Type :=
  (E⁄ℚ).Point

/--
Your naive x-height on rational points.

Typically:
* infinity maps to `0`;
* affine `(x,y)` maps to the logarithmic height of `x`.
-/
noncomputable def xHeight
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    RatPts E → ℝ :=
  sorry

R3 should expose:

lean
theorem xHeight_northcott
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Northcott (xHeight E) := by
  -- R3
  sorry

R2 should expose either a constant explicitly:

lean
noncomputable def xHeightDoubleConstant
    (E : WeierstrassCurve ℚ) [E.IsElliptic] : ℝ :=
  sorry

theorem xHeight_double_lower
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ P : RatPts E,
      4 * xHeight E P - xHeightDoubleConstant E ≤
        xHeight E (2 • P) := by
  -- R2
  sorry

or existentially:

lean
theorem xHeight_double_lower_exists
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : ℝ,
      ∀ P : RatPts E,
        4 * xHeight E P - C ≤ xHeight E (2 • P) := by
  -- R2
  sorry

Then A6 becomes:

lean
theorem rational_torsion_finite_from_xHeight
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Finite (AddCommGroup.torsion (RatPts E)) := by
  classical
  exact finite_torsion_of_northcott_double_lower
    (h := xHeight E)
    (C := xHeightDoubleConstant E)
    (xHeight_northcott E)
    (xHeight_double_lower E)

If R2 is existential:

lean
theorem rational_torsion_finite_from_xHeight'
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Finite (AddCommGroup.torsion (RatPts E)) := by
  classical
  rcases xHeight_double_lower_exists E with ⟨C, hC⟩
  exact finite_torsion_of_northcott_double_lower
    (h := xHeight E)
    (C := C)
    (xHeight_northcott E)
    hC

If the downstream theorem currently expects the set-level alias:

lean
theorem rational_torsion_finite_alias
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (RatPts E) : Set (RatPts E)).Finite := by
  classical
  haveI : Finite (AddCommGroup.torsion (RatPts E)) :=
    rational_torsion_finite_from_xHeight E
  exact Set.toFinite _

If downstream wants the typeclass instance directly:

lean
noncomputable instance rational_torsion_finite_inst
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Finite (AddCommGroup.torsion (RatPts E)) :=
  rational_torsion_finite_from_xHeight E

Then in rational_torsion_two_invariant_factors, replace the old dependency:

lean
haveI : Finite (AddCommGroup.torsion (RatPts E)) :=
  rational_torsion_finite_from_xHeight E

or, if that proof wants a set-finite hypothesis:

lean
have hfin :
    (AddCommGroup.torsion (RatPts E) : Set (RatPts E)).Finite :=
  rational_torsion_finite_alias E

letI : Fintype (AddCommGroup.torsion (RatPts E)) :=
  hfin.fintype

haveI : Finite (AddCommGroup.torsion (RatPts E)) :=
  inferInstance
3. Adversarial audit

The abstract argument is not the weak link. It is elementary finite-set algebra and has no dependency on canonical heights, Mordell-Weil, reduction, or elliptic-curve geometry.

Difficulty ranking:

Doubling lower bound for xHeight — hardest. You need the duplication formula, careful treatment of infinity and 2-torsion, denominator/numerator height estimates, and a constant depending only on the curve. This is elementary, but Lean-heavy.

Northcott for xHeight — medium. It reduces to Northcott for rational logarithmic height plus finite y choices for each bounded x. If Mathlib/FLT already has rational height Northcott, this is bounded. Without it, you must build rational height finiteness.

Abstract torsion finiteness lemma — easy. The code above is the whole mathematical core.

No circularity is present provided R2/R3 are proved for a naive height, not by invoking canonical height or Mordell-Weil. The route is:

naive x-height Northcott
+ naive x-height doubling lower bound
→ finite rational torsion

It does not require canonical height. Canonical height is one traditional way to prove finite generation; here it would be overkill and would risk circularly importing Mordell-Weil-style infrastructure.

Honest verdict: if R2 and R3 already exist or are close, A6 is a bounded project. If they do not, the abstract lemma is small, but the full height route is not “just a few lines.” With a usable rational-height API, I would expect a few hundred lines. Without one, especially for the duplication height estimate, it can grow into a larger elementary-height development. It is still much smaller than formalizing Mordell-Weil, and it does not hide a deep theorem.
