# Q2635: focused audit for `EulerSquarePairDescent`

Target file: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`.
Namespace assumed below: `MazurProof.RationalPointsN12`.

I could not see the local target file or the local private refinement theorem through the GitHub code-search index, so the first helper below is written as an adapter around the Nat-refinement output. In the target file, replace the `hRef` hypothesis by the existing private Nat refinement theorem call; the remaining cast/parity steps are the important part.

Audit verdict:

* The route is sound, provided the Nat refinement returns positive `a0 b c d` and pairwise `Nat.Coprime` among `a0,b,c,d`.
* Derive `Odd c`, `Odd d` from `V = c*d` and `Odd V`, and derive `Odd b` from `Vp = b*d` and `Odd Vp`.
* Derive `Even a0` from `U = a0*b`, `Even U`, and `Odd b`; then write `a0 = 2*a`. This also gives `0 < a` from `0 < a0`.
* For `IsCoprime a d`, use `Nat.Coprime.of_dvd_left` before casting to `IsCoprime (a : Int) (d : Int)`.
* For the mod-8 step, avoid `ZMod` case splits. `Int.ModEq` plus `Int.two_dvd_mul_add_one` gives a short proof that odd squares are `1 mod 8`.
* Balance extraction orientation must be: first obtain
  `4*a^2+d^2 = c^2` and `16*a^2+d^2 = b^2`; then set `F.hB := (second).symm` and `F.hC := (first).symm`.
* The clean strict decrease is `a*d < E.A`, not just `a*d < E.A*E.D`, using `E.A = (2*a*b)*(c*d)` and `0 < b,c`.

## Imports

```lean
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic
```

## 1. Adapter for the Nat refinement output

The `hRef` shape below is the cleanest adapter target for the existing private Nat refinement theorem. If that theorem returns a bundled structure or nested pairwise statement, first reshape it to this `∃` block, then use the proof below unchanged.

```lean
namespace MazurProof.RationalPointsN12

/-- Cast/parity adapter for the Nat refinement of two coprime factorizations.

Replace `hRef` by the existing private Nat refinement theorem call. The output is deliberately
in `Int`, with `a0 = 2*a` already absorbed. -/
theorem refined_factors_from_signed_params
    {U V Up Vp : Int}
    (hUpos : 0 < U) (hVpos : 0 < V) (hUppos : 0 < Up) (hVppos : 0 < Vp)
    (hUeven : Even U) (hVodd : Odd V)
    (hUpeven : Even Up) (hVpodd : Odd Vp)
    (hRef : ∃ a0 b c d : Nat,
      0 < a0 ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      U.natAbs = a0 * b ∧ V.natAbs = c * d ∧
      Up.natAbs = a0 * c ∧ Vp.natAbs = b * d ∧
      Nat.Coprime a0 b ∧ Nat.Coprime a0 c ∧ Nat.Coprime a0 d ∧
      Nat.Coprime b c ∧ Nat.Coprime b d ∧ Nat.Coprime c d) :
    ∃ a b c d : Int,
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      U = 2 * a * b ∧ V = c * d ∧
      Up = 2 * a * c ∧ Vp = b * d ∧
      IsCoprime a b ∧ IsCoprime a c ∧ IsCoprime a d ∧
      IsCoprime b c ∧ IsCoprime b d ∧ IsCoprime c d ∧
      Odd b ∧ Odd c ∧ Odd d := by
  rcases hRef with
    ⟨a0, b, c, d,
      ha0pos, hbpos, hcpos, hdpos,
      hU_abs, hV_abs, hUp_abs, hVp_abs,
      ha0b, ha0c, ha0d, hbc, hbd, hcd⟩

  have hU0 : U = ((a0 * b : Nat) : Int) := by
    apply (Int.natAbs_inj_of_nonneg_of_nonneg (le_of_lt hUpos)
      (by exact_mod_cast (Nat.zero_le (a0 * b)))).mp
    simpa using hU_abs
  have hV0 : V = ((c * d : Nat) : Int) := by
    apply (Int.natAbs_inj_of_nonneg_of_nonneg (le_of_lt hVpos)
      (by exact_mod_cast (Nat.zero_le (c * d)))).mp
    simpa using hV_abs
  have hUp0 : Up = ((a0 * c : Nat) : Int) := by
    apply (Int.natAbs_inj_of_nonneg_of_nonneg (le_of_lt hUppos)
      (by exact_mod_cast (Nat.zero_le (a0 * c)))).mp
    simpa using hUp_abs
  have hVp0 : Vp = ((b * d : Nat) : Int) := by
    apply (Int.natAbs_inj_of_nonneg_of_nonneg (le_of_lt hVppos)
      (by exact_mod_cast (Nat.zero_le (b * d)))).mp
    simpa using hVp_abs

  have hcd_odd_int : Odd ((c : Int) * (d : Int)) := by
    simpa [hV0, Nat.cast_mul] using hVodd
  have hc_odd_int : Odd (c : Int) := (Int.odd_mul.mp hcd_odd_int).1
  have hd_odd_int : Odd (d : Int) := (Int.odd_mul.mp hcd_odd_int).2
  have hbd_odd_int : Odd ((b : Int) * (d : Int)) := by
    simpa [hVp0, Nat.cast_mul] using hVpodd
  have hb_odd_int : Odd (b : Int) := (Int.odd_mul.mp hbd_odd_int).1

  have ha0b_even_int : Even ((a0 : Int) * (b : Int)) := by
    simpa [hU0, Nat.cast_mul] using hUeven
  have ha0_even_int : Even (a0 : Int) := by
    by_contra hnot
    have ha0_odd_int : Odd (a0 : Int) := Int.not_even_iff_odd.mp hnot
    have hprod_odd : Odd ((a0 : Int) * (b : Int)) := ha0_odd_int.mul hb_odd_int
    exact (Int.not_even_iff_odd.mpr hprod_odd) ha0b_even_int
  have ha0_even_nat : Even a0 := by
    have : Even ((a0 : Int).natAbs) := (Int.natAbs_even.mpr ha0_even_int)
    simpa using this

  rcases ha0_even_nat with ⟨a, ha0_eq_add⟩
  have ha0_eq : a0 = 2 * a := by
    simpa [two_mul] using ha0_eq_add
  have ha_pos : 0 < a := by
    have ha_ne_zero : a ≠ 0 := by
      intro ha0
      have : a0 = 0 := by simp [ha0_eq, ha0]
      exact (Nat.ne_of_gt ha0pos) this
    exact Nat.pos_of_ne_zero ha_ne_zero

  have ha_dvd_a0 : a ∣ a0 := by
    refine ⟨2, ?_⟩
    simpa [ha0_eq, mul_comm]

  have hab_nat : Nat.Coprime a b := ha0b.of_dvd_left ha_dvd_a0
  have hac_nat : Nat.Coprime a c := ha0c.of_dvd_left ha_dvd_a0
  have had_nat : Nat.Coprime a d := ha0d.of_dvd_left ha_dvd_a0

  have hUeq : U = 2 * (a : Int) * (b : Int) := by
    calc
      U = ((a0 * b : Nat) : Int) := hU0
      _ = (a0 : Int) * (b : Int) := by simp
      _ = 2 * (a : Int) * (b : Int) := by
        rw [ha0_eq]
        norm_num
        ring
  have hVeq : V = (c : Int) * (d : Int) := by
    calc
      V = ((c * d : Nat) : Int) := hV0
      _ = (c : Int) * (d : Int) := by simp
  have hUpeq : Up = 2 * (a : Int) * (c : Int) := by
    calc
      Up = ((a0 * c : Nat) : Int) := hUp0
      _ = (a0 : Int) * (c : Int) := by simp
      _ = 2 * (a : Int) * (c : Int) := by
        rw [ha0_eq]
        norm_num
        ring
  have hVpeq : Vp = (b : Int) * (d : Int) := by
    calc
      Vp = ((b * d : Nat) : Int) := hVp0
      _ = (b : Int) * (d : Int) := by simp

  refine ⟨(a : Int), (b : Int), (c : Int), (d : Int), ?_, ?_, ?_, ?_,
    hUeq, hVeq, hUpeq, hVpeq, ?_, ?_, ?_, ?_, ?_, ?_, hb_odd_int, hc_odd_int,
    hd_odd_int⟩
  · exact_mod_cast ha_pos
  · exact_mod_cast hbpos
  · exact_mod_cast hcpos
  · exact_mod_cast hdpos
  · simpa using hab_nat.isCoprime
  · simpa using hac_nat.isCoprime
  · simpa using had_nat.isCoprime
  · simpa using hbc.isCoprime
  · simpa using hbd.isCoprime
  · simpa using hcd.isCoprime
```

Notes for integrating the private Nat refinement call:

```lean
  -- Instead of a hypothesis `hRef`, use roughly:
  obtain ⟨a0, b, c, d, ha0pos, hbpos, hcpos, hdpos,
    hU_abs, hV_abs, hUp_abs, hVp_abs,
    ha0b, ha0c, ha0d, hbc, hbd, hcd⟩ :=
      existing_private_nat_refinement_theorem
        -- usually applied to U.natAbs, V.natAbs, Up.natAbs, Vp.natAbs
        -- plus the casted/coprime hypotheses
```

## 2. Robust mod-8 helper and `even_a_of_euler_balance`

This is the most stable implementation I recommend. It uses `Int.ModEq` and avoids relying on any specialized odd-square modulo lemma.

```lean
private theorem odd_sq_modEq_one_mod_eight {x : Int} (hx : Odd x) :
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

/-- In the refined Euler balance, odd `b,c,d` force `a` even. -/
theorem even_a_of_euler_balance
    {a b c d : Int}
    (hbodd : Odd b) (hcodd : Odd c) (hdodd : Odd d)
    (hbal : b ^ 2 * (4 * a ^ 2 + d ^ 2) =
      c ^ 2 * (16 * a ^ 2 + d ^ 2)) :
    Even a := by
  by_contra hnot_even
  have haodd : Odd a := Int.not_even_iff_odd.mp hnot_even

  have hb2 : b ^ 2 ≡ 1 [ZMOD 8] := odd_sq_modEq_one_mod_eight hbodd
  have hc2 : c ^ 2 ≡ 1 [ZMOD 8] := odd_sq_modEq_one_mod_eight hcodd
  have hd2 : d ^ 2 ≡ 1 [ZMOD 8] := odd_sq_modEq_one_mod_eight hdodd
  have ha2 : a ^ 2 ≡ 1 [ZMOD 8] := odd_sq_modEq_one_mod_eight haodd

  have h4a2 : 4 * a ^ 2 ≡ 4 [ZMOD 8] := by
    simpa using ha2.mul_left (4 : Int)
  have h16a2 : 16 * a ^ 2 ≡ 0 [ZMOD 8] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(2 * a ^ 2), ?_⟩
    ring
  have hleft_factor : 4 * a ^ 2 + d ^ 2 ≡ 5 [ZMOD 8] := by
    simpa using h4a2.add hd2
  have hright_factor : 16 * a ^ 2 + d ^ 2 ≡ 1 [ZMOD 8] := by
    simpa using h16a2.add hd2

  have hleft : b ^ 2 * (4 * a ^ 2 + d ^ 2) ≡ 5 [ZMOD 8] := by
    simpa using hb2.mul hleft_factor
  have hright : c ^ 2 * (16 * a ^ 2 + d ^ 2) ≡ 1 [ZMOD 8] := by
    simpa using hc2.mul hright_factor
  have hbalance_mod :
      b ^ 2 * (4 * a ^ 2 + d ^ 2) ≡
        c ^ 2 * (16 * a ^ 2 + d ^ 2) [ZMOD 8] := by
    simpa [hbal]
  have hbad : (5 : Int) ≡ 1 [ZMOD 8] :=
    hleft.symm.trans (hbalance_mod.trans hright)
  norm_num [Int.ModEq] at hbad
```

## 3. Balance extraction and Euler pair construction

Because the local signatures of `square_factor_balance_int` and `EulerSquarePair` are not visible from the GitHub index, I recommend splitting this into a field-name-independent core and a tiny structure-literal wrapper.

The core fixes the orientation once and for all:

```lean
/-- Core descent data from refined factors. The conclusion is ordered for `EulerSquarePair`:
`hB` is the `16*a^2+d^2` equation, `hC` is the `4*a^2+d^2` equation. -/
theorem descent_pair_data_from_refined_factors
    {a b c d : Int}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hbodd : Odd b) (hcodd : Odd c) (hdodd : Odd d)
    (had : IsCoprime a d) (hbc : IsCoprime b c)
    (hbal : b ^ 2 * (4 * a ^ 2 + d ^ 2) =
      c ^ 2 * (16 * a ^ 2 + d ^ 2)) :
    b ^ 2 = 16 * a ^ 2 + d ^ 2 ∧
      c ^ 2 = 4 * a ^ 2 + d ^ 2 := by
  have haeven : Even a := even_a_of_euler_balance hbodd hcodd hdodd hbal
  have hPpos : 0 < 4 * a ^ 2 + d ^ 2 := by
    have hdsq : 0 < d ^ 2 := sq_pos_of_ne_zero (ne_of_gt hd)
    have hasq : 0 ≤ a ^ 2 := sq_nonneg a
    nlinarith
  have hQpos : 0 < 16 * a ^ 2 + d ^ 2 := by
    have hdsq : 0 < d ^ 2 := sq_pos_of_ne_zero (ne_of_gt hd)
    have hasq : 0 ≤ a ^ 2 := sq_nonneg a
    nlinarith
  have hcof_forward : IsCoprime (16 * a ^ 2 + d ^ 2) (4 * a ^ 2 + d ^ 2) := by
    simpa using euler_cofactor_coprime (A := a) (D := d) hdodd had
  have hcof : IsCoprime (4 * a ^ 2 + d ^ 2) (16 * a ^ 2 + d ^ 2) :=
    hcof_forward.symm

  /-
  Expected local call. Use whichever orientation your existing lemma has.

  The target orientation for the local result is:
    hsplit.1 : 4 * a^2 + d^2 = c^2
    hsplit.2 : 16 * a^2 + d^2 = b^2

  Example shape:
    have hsplit :
        4 * a ^ 2 + d ^ 2 = c ^ 2 ∧
        16 * a ^ 2 + d ^ 2 = b ^ 2 := by
      exact square_factor_balance_int
        hb hc hPpos hQpos hbc hcof hbal
  -/
  have hsplit :
      4 * a ^ 2 + d ^ 2 = c ^ 2 ∧
      16 * a ^ 2 + d ^ 2 = b ^ 2 := by
    -- Replace this block by the exact local `square_factor_balance_int` call.
    -- The proof obligations already prepared above are `hb`, `hc`, `hPpos`, `hQpos`,
    -- `hbc`, `hcof`, and `hbal`.
    exact square_factor_balance_int hb hc hPpos hQpos hbc hcof hbal

  exact ⟨hsplit.2.symm, hsplit.1.symm⟩
```

Then the structure wrapper should be this small. Adjust only positive field names if your structure uses different ones; the important part is the order of `hB` and `hC`.

```lean
/-- Construct the smaller Euler square pair from refined factors.
The order is `B=b`, `C=c`. -/
theorem descent_pair_from_refined_factors
    {a b c d : Int}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hbodd : Odd b) (hcodd : Odd c) (hdodd : Odd d)
    (had : IsCoprime a d) (hbc : IsCoprime b c)
    (hbal : b ^ 2 * (4 * a ^ 2 + d ^ 2) =
      c ^ 2 * (16 * a ^ 2 + d ^ 2)) :
    ∃ F : EulerSquarePair,
      F.A = a ∧ F.D = d ∧ F.B = b ∧ F.C = c := by
  obtain ⟨hB, hC⟩ :=
    descent_pair_data_from_refined_factors
      ha hb hc hd hbodd hcodd hdodd had hbc hbal
  refine ⟨{
    A := a, D := d, B := b, C := c,
    hApos := ha,
    hDpos := hd,
    hBpos := hb,
    hCpos := hc,
    hDodd := hdodd,
    hAD := had,
    hB := hB,
    hC := hC
  }, rfl, rfl, rfl, rfl⟩
```

If `EulerSquarePair` has no `hBpos`/`hCpos` fields, remove those two lines. If it uses names like `hA`, `hD`, `hB_positive`, etc., only those field labels need changing. The equations are intentionally in the requested order:

```lean
-- F.hB : b ^ 2 = 16 * a ^ 2 + d ^ 2
-- F.hC : c ^ 2 = 4 * a ^ 2 + d ^ 2
```

## 4. Strict inequality: use `a*d < E.A`

This is the strongest simple decrease. It only needs `E.A = U*V`, the refined equations for `U,V`, and positivity.

```lean
/-- The refined factors give the strict decrease `a*d < E.A`. -/
theorem refined_factors_mul_lt_original_A
    {EA a b c d : Int}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hEA : EA = (2 * a * b) * (c * d)) :
    a * d < EA := by
  have had_pos : 0 < a * d := mul_pos ha hd
  have hfactor : 1 < 2 * b * c := by nlinarith
  calc
    a * d < (a * d) * (2 * b * c) :=
      lt_mul_of_one_lt_right had_pos hfactor
    _ = (2 * a * b) * (c * d) := by ring
    _ = EA := hEA.symm

/-- Version in terms of the existing pair `E`. -/
theorem refined_factors_mul_lt_EA
    (E : EulerSquarePair)
    {U V a b c d : Int}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hEA : E.A = U * V)
    (hU : U = 2 * a * b) (hV : V = c * d) :
    a * d < E.A := by
  apply refined_factors_mul_lt_original_A ha hb hc hd
  calc
    E.A = U * V := hEA
    _ = (2 * a * b) * (c * d) := by rw [hU, hV]
```

## Integration outline in `EulerSquarePairDescent`

After `signed_even_odd_params_same_orientation`, use:

```lean
  obtain ⟨a, b, c, d,
    ha, hb, hc, hd,
    hU, hV, hUp, hVp,
    hab, hac, had, hbc, hbd, hcd,
    hbodd, hcodd, hdodd⟩ :=
      refined_factors_from_signed_params
        hUpos hVpos hUppos hVppos hUeven hVodd hUpeven hVpodd
        -- replace this with the Nat refinement theorem result, reshaped as `hRef`
        hRef

  have hbal : b ^ 2 * (4 * a ^ 2 + d ^ 2) =
      c ^ 2 * (16 * a ^ 2 + d ^ 2) := by
    exact refinement_equation_of_same_orientation
      -- expected arguments include the four refined equations hU hV hUp hVp
      -- plus the original balance/signed-parameter equations

  obtain ⟨F, rfl, rfl, rfl, rfl⟩ :=
    descent_pair_from_refined_factors
      ha hb hc hd hbodd hcodd hdodd had hbc hbal

  have hltEA : F.A * F.D < E.A := by
    -- after the `rfl`s above this is `a*d < E.A`
    exact refined_factors_mul_lt_EA E ha hb hc hd E.hA hU hV

  have hlt : F.A * F.D < E.A * E.D := by
    -- if the final descent theorem wants product decrease instead of `A` decrease
    have hDge1 : 1 ≤ E.D := by exact_mod_cast (show 1 ≤ E.D.natAbs from by omega)
    nlinarith [hltEA, E.hDpos]
```

The last `hlt` snippet is intentionally secondary: prefer carrying `hltEA : F.A*F.D < E.A` as long as possible. If the final API only accepts `F.A*F.D < E.A*E.D`, prove it from `hltEA` and `0 < E.D` with a local order lemma suited to the actual structure fields.

end MazurProof.RationalPointsN12
```