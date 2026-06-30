# Q2693 (dm-codex1): raw square branch parity/factorization Lean plan

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Target Lean area: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`  
Namespace: `MazurProof.RationalPointsN12`

Connector note: the GitHub connector still does not expose the target Lean file at the requested path, so I cannot honestly claim this was compiled against the repository checkout. The code below is written against the exact interfaces from the prompt. The helper layer avoids `sorry` and avoids new axioms. The only intentionally isolated uncertainty is the final adapter from the already-proved square-factor theorem names to the local adapter signatures; if the theorem argument order in the file differs, only that adapter block should need adjustment.

## Mathematical structure

The branch gives two square products:

```text
A^2 = (m - n) * (m + n)
N^2 = n * (2*m - n)
```

The correct split is:

* `m` is odd.
* If `n` is even, then `m-n` and `m+n` are odd and coprime; `n` and `2*m-n` are even with coprime halves.
* If `n` is odd, then `m-n` and `m+n` are even with coprime halves; `n` and `2*m-n` are odd and coprime.

The helpers below prove exactly those parity/coprimality facts using the `IsCoprime` Bezout definition, not `Int.gcd`.

## Pasteable helper layer and `rawSqBranchMParityStatement`

If this is pasted directly inside `N12QuarticEisenstein.lean`, delete the self-import line.

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

/-! ### Basic `Even`/`Odd`/`2 ∣ _` conversions over `ℤ` -/

lemma two_dvd_of_even_int {x : ℤ} (hx : Even x) : (2 : ℤ) ∣ x := by
  rcases hx with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [hk]
  ring

lemma even_of_two_dvd_int {x : ℤ} (hx : (2 : ℤ) ∣ x) : Even x := by
  rcases hx with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [hk]
  ring

lemma not_two_dvd_of_odd_int {x : ℤ} (hx : Odd x) : ¬ (2 : ℤ) ∣ x := by
  rintro ⟨k, hk⟩
  rcases hx with ⟨r, hr⟩
  rw [hk] at hr
  omega

lemma odd_of_not_two_dvd_int {x : ℤ} (hx : ¬ (2 : ℤ) ∣ x) : Odd x := by
  rcases Int.even_or_odd x with hxEven | hxOdd
  · exact False.elim (hx (two_dvd_of_even_int hxEven))
  · exact hxOdd

/-! ### Small modular fact: an integer square is never `3 mod 4`. -/

lemma int_sq_ne_four_mul_add_three (a k : ℤ) : a ^ 2 ≠ 4 * k + 3 := by
  intro h
  rcases Int.even_or_odd a with ha | ha
  · rcases ha with ⟨r, hr⟩
    subst a
    ring_nf at h
    omega
  · rcases ha with ⟨r, hr⟩
    subst a
    ring_nf at h
    omega

/-! ### Coprimality cannot coexist with both inputs even. -/

lemma not_isCoprime_of_even_even {m n : ℤ}
    (hm : Even m) (hn : Even n) : ¬ IsCoprime m n := by
  rintro ⟨u, v, huv⟩
  rcases hm with ⟨m0, hm0⟩
  rcases hn with ⟨n0, hn0⟩
  have hEvenOneWitness :
      (1 : ℤ) = (u * m0 + v * n0) + (u * m0 + v * n0) := by
    calc
      (1 : ℤ) = u * m + v * n := by rw [huv]
      _ = (u * m0 + v * n0) + (u * m0 + v * n0) := by
        rw [hm0, hn0]
        ring
  omega

lemma odd_of_isCoprime_even_left {m n : ℤ}
    (hcop : IsCoprime m n) (hm : Even m) : Odd n := by
  rcases Int.even_or_odd n with hnEven | hnOdd
  · exact False.elim ((not_isCoprime_of_even_even hm hnEven) hcop)
  · exact hnOdd

/-! ### Parity transport lemmas for the four branch factors. -/

lemma odd_sub_even_int {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (m - n) := by
  rcases hm with ⟨a, ha⟩
  rcases hn with ⟨b, hb⟩
  refine ⟨a - b, ?_⟩
  rw [ha, hb]
  ring

lemma odd_add_even_int {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (m + n) := by
  rcases hm with ⟨a, ha⟩
  rcases hn with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  rw [ha, hb]
  ring

lemma even_sub_odd_odd_int {m n : ℤ} (hm : Odd m) (hn : Odd n) : Even (m - n) := by
  rcases hm with ⟨a, ha⟩
  rcases hn with ⟨b, hb⟩
  refine ⟨a - b, ?_⟩
  rw [ha, hb]
  ring

lemma even_add_odd_odd_int {m n : ℤ} (hm : Odd m) (hn : Odd n) : Even (m + n) := by
  rcases hm with ⟨a, ha⟩
  rcases hn with ⟨b, hb⟩
  refine ⟨a + b + 1, ?_⟩
  rw [ha, hb]
  ring

lemma even_two_mul_sub_of_odd_even_int {m n : ℤ}
    (hm : Odd m) (hn : Even n) : Even (2 * m - n) := by
  rcases hm with ⟨a, ha⟩
  rcases hn with ⟨b, hb⟩
  refine ⟨2 * a + 1 - b, ?_⟩
  rw [ha, hb]
  ring

lemma odd_two_mul_sub_of_odd_odd_int {m n : ℤ}
    (hm : Odd m) (hn : Odd n) : Odd (2 * m - n) := by
  rcases hm with ⟨a, ha⟩
  rcases hn with ⟨b, hb⟩
  refine ⟨2 * a - b, ?_⟩
  rw [ha, hb]
  ring

/-! ### Odd numbers are coprime to `2`. -/

lemma isCoprime_odd_two_int {x : ℤ} (hx : Odd x) : IsCoprime x (2 : ℤ) := by
  rcases hx with ⟨k, hk⟩
  use 1, -k
  rw [hk]
  ring

/-! ### Coprimality helpers for `(m-n,m+n)` and `(n,2*m-n)`. -/

lemma isCoprime_m_sub_n_m_add_n_of_even_n
    {m n : ℤ} (hcop : IsCoprime m n) (hm : Odd m) (hn : Even n) :
    IsCoprime (m - n) (m + n) := by
  have h_sub_n : IsCoprime (m - n) n := by
    have h0 : IsCoprime (m - (1 : ℤ) * n) n :=
      (IsCoprime.sub_mul_right_left_iff (x := m) (y := n) (z := (1 : ℤ))).2 hcop
    simpa [one_mul] using h0
  have h_sub_odd : Odd (m - n) := odd_sub_even_int hm hn
  have h_sub_two : IsCoprime (m - n) (2 : ℤ) := isCoprime_odd_two_int h_sub_odd
  have h_sub_two_n : IsCoprime (m - n) ((2 : ℤ) * n) :=
    h_sub_two.mul_right h_sub_n
  have h1 : IsCoprime (m - n) (((2 : ℤ) * n) + (m - n) * (1 : ℤ)) :=
    h_sub_two_n.add_mul_left_right (1 : ℤ)
  have harg : ((2 : ℤ) * n) + (m - n) * (1 : ℤ) = m + n := by
    ring
  simpa [harg] using h1

lemma isCoprime_n_two_mul_m_sub_n_of_odd_n
    {m n : ℤ} (hcop : IsCoprime m n) (hn : Odd n) :
    IsCoprime n (2 * m - n) := by
  have h_n_m : IsCoprime n m := hcop.symm
  have h_n_two : IsCoprime n (2 : ℤ) := isCoprime_odd_two_int hn
  have h_n_two_m : IsCoprime n ((2 : ℤ) * m) := h_n_two.mul_right h_n_m
  have h1 : IsCoprime n (((2 : ℤ) * m) - (1 : ℤ) * n) :=
    (IsCoprime.sub_mul_right_right_iff
      (x := n) (y := ((2 : ℤ) * m) (z := (1 : ℤ))).2 h_n_two_m
  have harg : ((2 : ℤ) * m) - (1 : ℤ) * n = 2 * m - n := by
    ring
  simpa [harg] using h1

/-- If `m-n = 2*x` and `m+n = 2*y`, then coprimality of `m,n`
transfers to coprimality of the halves `x,y`. -/
lemma isCoprime_halves_m_sub_m_add
    {m n x y : ℤ} (hcop : IsCoprime m n)
    (hx : m - n = 2 * x) (hy : m + n = 2 * y) :
    IsCoprime x y := by
  rcases hcop with ⟨r, s, hrs⟩
  use r - s, r + s
  have hm : m = x + y := by omega
  have hn : n = y - x := by omega
  calc
    (r - s) * x + (r + s) * y = r * (x + y) + s * (y - x) := by ring
    _ = r * m + s * n := by rw [hm, hn]
    _ = 1 := hrs

/-- If `n = 2*x` and `2*m-n = 2*y`, then coprimality of `m,n`
transfers to coprimality of the halves `x,y`. -/
lemma isCoprime_halves_n_two_mul_sub
    {m n x y : ℤ} (hcop : IsCoprime m n)
    (hx : n = 2 * x) (hy : 2 * m - n = 2 * y) :
    IsCoprime x y := by
  rcases hcop with ⟨r, s, hrs⟩
  use r + 2 * s, r
  have hm : m = x + y := by omega
  calc
    (r + 2 * s) * x + r * y = r * (x + y) + s * (2 * x) := by ring
    _ = r * m + s * n := by rw [hm, hx]
    _ = 1 := hrs

/-! ### The requested `m`-parity theorem. -/

theorem rawSqBranchMParityStatement : RawSqBranchMParityStatement := by
  intro A N S m n hbranch
  rcases hbranch with ⟨hnpos, hnm, hcop, hA, hN, hS⟩
  rcases Int.even_or_odd m with hmEven | hmOdd
  · have hnOdd : Odd n := odd_of_isCoprime_even_left hcop hmEven
    exfalso
    rcases hmEven with ⟨u, hu⟩
    rcases hnOdd with ⟨v, hv⟩
    have hbad : A ^ 2 = 4 * (u ^ 2 - v ^ 2 - v - 1) + 3 := by
      calc
        A ^ 2 = (m - n) * (m + n) := hA
        _ = 4 * (u ^ 2 - v ^ 2 - v - 1) + 3 := by
          rw [hu, hv]
          ring
    exact int_sq_ne_four_mul_add_three A (u ^ 2 - v ^ 2 - v - 1) hbad
  · exact hmOdd

end MazurProof.RationalPointsN12
```

## Factorization assembly from square-factor adapters

This is the robust part: it proves the residual factorization from two adapter signatures matching exactly what this branch needs. It contains no `sorry` and does not depend on the internal argument order of the checked square-factor theorem constants.

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

/-- Adapter shape for `posSqOfCoprimeMulSqStatement`. -/
def PosSqFactorAdapter : Prop :=
  ∀ {x y z : ℤ},
    0 < x → 0 < y →
    IsCoprime x y →
    z ^ 2 = x * y →
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = a ^ 2 ∧ y = b ^ 2

/-- Adapter shape for `posTwoSqOfGcdTwoMulSqStatement`, phrased with explicit
positive halves. If the checked theorem in the file is phrased with `x / 2`,
prove this adapter once from that theorem and use the assembly unchanged. -/
def PosTwoFactorAdapter : Prop :=
  ∀ {x y z u v : ℤ},
    0 < x → 0 < y →
    x = 2 * u → y = 2 * v →
    IsCoprime u v →
    z ^ 2 = x * y →
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = 2 * a ^ 2 ∧ y = 2 * b ^ 2

/-- Branch factorization from the two already-proved square-factor lemmas,
with those lemmas supplied through stable local adapters. -/
theorem rawSqBranchFactorizationStatement_from_squareFactorAdapters
    (hSq : PosSqFactorAdapter)
    (hTwo : PosTwoFactorAdapter) :
    RawSqBranchFactorizationStatement := by
  intro A N S m n hbranch
  rcases hbranch with ⟨hnpos, hnm, hcop, hA, hN, hS⟩
  have hbranch' : EisensteinSqBranch A N S m n :=
    ⟨hnpos, hnm, hcop, hA, hN, hS⟩
  have hmOdd : Odd m := rawSqBranchMParityStatement hbranch'
  have hpos_m_sub_n : 0 < m - n := by omega
  have hpos_m_add_n : 0 < m + n := by omega
  have hpos_two_m_sub_n : 0 < 2 * m - n := by omega
  rcases Int.even_or_odd n with hnEven | hnOdd
  · left
    constructor
    · exact hnEven
    · have hcopA : IsCoprime (m - n) (m + n) :=
        isCoprime_m_sub_n_m_add_n_of_even_n hcop hmOdd hnEven
      rcases hSq (x := m - n) (y := m + n) (z := A)
          hpos_m_sub_n hpos_m_add_n hcopA hA with
        ⟨a, b, ha_pos, hb_pos, hma, hmb⟩
      have h2mnEven : Even (2 * m - n) :=
        even_two_mul_sub_of_odd_even_int hmOdd hnEven
      rcases hnEven with ⟨u, hu⟩
      rcases h2mnEven with ⟨v, hv⟩
      have hu2 : n = 2 * u := by
        rw [hu]
        ring
      have hv2 : 2 * m - n = 2 * v := by
        rw [hv]
        ring
      have hcopN : IsCoprime u v :=
        isCoprime_halves_n_two_mul_sub hcop hu2 hv2
      rcases hTwo (x := n) (y := 2 * m - n) (z := N) (u := u) (v := v)
          hnpos hpos_two_m_sub_n hu2 hv2 hcopN hN with
        ⟨c, d, hc_pos, hd_pos, hnc, h2md⟩
      exact ⟨a, b, c, d,
        ha_pos, hb_pos, hc_pos, hd_pos,
        hma, hmb, hnc, h2md⟩
  · right
    constructor
    · exact hnOdd
    · have hmnEven : Even (m - n) := even_sub_odd_odd_int hmOdd hnOdd
      have hmpEven : Even (m + n) := even_add_odd_odd_int hmOdd hnOdd
      rcases hmnEven with ⟨u, hu⟩
      rcases hmpEven with ⟨v, hv⟩
      have hu2 : m - n = 2 * u := by
        rw [hu]
        ring
      have hv2 : m + n = 2 * v := by
        rw [hv]
        ring
      have hcopA : IsCoprime u v :=
        isCoprime_halves_m_sub_m_add hcop hu2 hv2
      rcases hTwo (x := m - n) (y := m + n) (z := A) (u := u) (v := v)
          hpos_m_sub_n hpos_m_add_n hu2 hv2 hcopA hA with
        ⟨a, b, ha_pos, hb_pos, hma, hmb⟩
      have hcopN : IsCoprime n (2 * m - n) :=
        isCoprime_n_two_mul_m_sub_n_of_odd_n hcop hnOdd
      rcases hSq (x := n) (y := 2 * m - n) (z := N)
          hnpos hpos_two_m_sub_n hcopN hN with
        ⟨c, d, hc_pos, hd_pos, hnc, h2md⟩
      exact ⟨a, b, c, d,
        ha_pos, hb_pos, hc_pos, hd_pos,
        hma, hmb, hnc, h2md⟩

end MazurProof.RationalPointsN12
```

## Expected adapter instantiation from the checked theorem constants

If the checked theorem constants have the natural argument order matching the statement names, this should close the final theorem. If the existing `PosTwoSqOfGcdTwoMulSqStatement` is phrased with `Even x`, `Even y`, and `IsCoprime (x / 2) (y / 2)` instead of explicit halves, keep the previous assembly theorem unchanged and only replace the proof of `posTwoFactorAdapter_checked`.

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

theorem posSqFactorAdapter_checked : PosSqFactorAdapter := by
  intro x y z hx hy hcop hz
  exact posSqOfCoprimeMulSqStatement hx hy hcop hz

theorem posTwoFactorAdapter_checked : PosTwoFactorAdapter := by
  intro x y z u v hx hy hx2 hy2 hcop hz
  exact posTwoSqOfGcdTwoMulSqStatement hx hy hx2 hy2 hcop hz

theorem rawSqBranchFactorizationStatement : RawSqBranchFactorizationStatement :=
  rawSqBranchFactorizationStatement_from_squareFactorAdapters
    posSqFactorAdapter_checked
    posTwoFactorAdapter_checked

end MazurProof.RationalPointsN12
```

## Notes on exact theorem dependencies

The proof of `rawSqBranchMParityStatement` uses only:

* `Int.even_or_odd`;
* `omega`, `ring`, and `ring_nf`;
* the Bezout definition of `IsCoprime`.

The factorization assembly uses the square-factor theorems only through the two adapter propositions. This is deliberate: it keeps all branch-specific parity/gcd bookkeeping local and makes any mismatch in the global square-factor lemma signatures a one-line adapter problem, not a reason to rewrite the branch proof.
