# Q2632 (dm-codex1): EulerSquarePairDescent constructive descent

Target file: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`

This drop is only about `EulerSquarePairDescent`.  I am not using or discussing the AP-to-Euler part.

## Adversarial verdict

The descent pair is mathematically correct as

```lean
F.A = a, F.D = d, F.B = b, F.C = c
```

**only if** `a` denotes **half of the common even refinement factor**.  The clean naming is:

```lean
U  = 2 * a * b
V  = c * d
Up = 2 * a * c
Vp = b * d
```

Then the orientation equations give

```lean
b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2)
```

and `square_factor_balance_int` gives

```lean
4*a^2 + d^2 = c^2
16*a^2 + d^2 = b^2
```

so `F=(a,d,b,c)` has exactly the two required square equations.

The important parity warning is this:

* If `a` is the half-common factor in `U=2*a*b`, then `Even a` **does not follow** from `Even U`, `Even Up`, and pairwise coprimality alone.  For example `a=b=c=d=1` gives `U=Up=2` and all pairwise coprimalities, but `a` is odd.
* The right proof of `Even a` uses the newly extracted square equation `c^2 = 4*a^2 + d^2` together with `Odd d`: if `a` were odd, the right side would be `5 mod 8`, impossible for a square.
* Equivalently, if the Nat refinement first returns a common factor `k` with `U=k*b`, `Up=k*c`, then `k` is even from `U` even and `b` odd; write `k=2*a`.  The square equation then forces this `a` even, i.e. `k` is actually divisible by `4`.

The negative orientation branch is not a problem.  In both branches the two expressions have the same signed value, either `E.D` or `-E.D`, so one still gets

```lean
U^2 - V^2 = 4*Up^2 - Vp^2
```

and hence the same balance equation.

## Hidden obligations before implementation

The implementation will get stuck unless the following small bridges exist.

1. **Int wrapper around the Nat refinement.**  Your existing `two_coprime_factorizations_refine_nat` is the right theorem, but the descent theorem has positive integers.  Add one wrapper returning positive `k b c d : ℤ` and at least the coprimalities `IsCoprime k d` and `IsCoprime b c`.  Returning all six pairwise coprimalities is best.
2. **Parity transfer.**  From `Odd (c*d)` get `Odd c` and `Odd d`; from `Odd (b*d)` get `Odd b`.  From `Even (k*b)` and `Odd b` get `Even k`.
3. **Half-common-factor coprimality.**  From `IsCoprime (2*a) d`, derive `IsCoprime a d`.
4. **Cofactor coprimality for balance.**  To use `square_factor_balance_int`, prove
   ```lean
   IsCoprime (4*a^2 + d^2) (16*a^2 + d^2)
   ```
   from `IsCoprime a d` and `Odd d`.  This is the least obvious hidden arithmetic lemma.  Common divisors divide both `12*a^2` and `3*d^2`; `Odd d` rules out `2`, and the mod-`3` square argument rules out `3`.
5. **Evenness of the new `A`.**  Prove `Even a` only after balance, using `c^2 = 4*a^2 + d^2` and `Odd d`, not before.
6. **Strict descent.**  Do not use the orientation formula for `E.D`.  It is enough that `E.D > 0` and
   ```lean
   E.A = 2*a*b*c*d
   ```
   with `a,b,c,d > 0`; then `a*d < E.A*E.D`.

## Lean-facing code skeleton

The theorem statement I would add is:

```lean
import FLT.Assumptions.MazurProof.N12EulerAux
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Integer-facing wrapper around the existing Nat refinement theorem. -/
private theorem two_coprime_factorizations_refine_int_pos
    {U V Up Vp : ℤ}
    (hUpos : 0 < U) (hVpos : 0 < V)
    (hUppos : 0 < Up) (hVppos : 0 < Vp)
    (hUV : IsCoprime U V)
    (hUpVp : IsCoprime Up Vp)
    (hprod : U * V = Up * Vp) :
    ∃ k b c d : ℤ,
      0 < k ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      U = k * b ∧ V = c * d ∧ Up = k * c ∧ Vp = b * d ∧
      IsCoprime k b ∧ IsCoprime k c ∧ IsCoprime k d ∧
      IsCoprime b c ∧ IsCoprime b d ∧ IsCoprime c d := by
  /-
  Implementation outline:
  * set `u := U.toNat`, `v := V.toNat`, `up := Up.toNat`, `vp := Vp.toNat`;
  * prove the Nat product equality by casting `hprod`;
  * convert `hUV` and `hUpVp` to `Nat.Coprime u v` and
    `Nat.Coprime up vp`;
  * call the checked `two_coprime_factorizations_refine_nat`;
  * cast the returned positive Nat factors back to Int;
  * convert the returned Nat coprimalities to `IsCoprime` over `ℤ`.
  -/
  sorry

private lemma odd_factors_of_odd_mul_int {x y : ℤ}
    (hxy : Odd (x * y)) : Odd x ∧ Odd y := by
  -- This is just parity modulo `2`; use the existing `Odd.mul` iff lemma if present.
  sorry

private lemma even_left_of_even_mul_odd_int {x y : ℤ}
    (hxy : Even (x * y)) (hy : Odd y) : Even x := by
  -- If `x` were odd, then `x*y` would be odd, contradicting `hxy`.
  sorry

private lemma even_pos_as_two_mul {k : ℤ}
    (hkpos : 0 < k) (hkeven : Even k) :
    ∃ a : ℤ, 0 < a ∧ k = 2 * a := by
  rcases hkeven with ⟨a, ha⟩
  -- Adjust this line if the local `Even` witness unfolds as `k = a + a`.
  refine ⟨a, ?_, ?_⟩
  · nlinarith
  · nlinarith

private lemma coprime_of_coprime_two_mul_left {a d : ℤ}
    (h : IsCoprime (2 * a) d) : IsCoprime a d := by
  -- Any common divisor of `a` and `d` also divides `2*a` and `d`.
  sorry

/-- Hidden arithmetic needed by `square_factor_balance_int`. -/
private lemma coprime_four_sq_add_odd_sq_sixteen_sq_add_odd_sq
    {a d : ℤ}
    (had : IsCoprime a d)
    (hdodd : Odd d) :
    IsCoprime (4 * a ^ 2 + d ^ 2) (16 * a ^ 2 + d ^ 2) := by
  /-
  Proof outline:
  * Let `g` be a common divisor of the two cofactors.
  * Then `g ∣ (16*a^2+d^2) - (4*a^2+d^2) = 12*a^2`.
  * Also `g ∣ 4*(4*a^2+d^2) - (16*a^2+d^2) = 3*d^2`.
  * Since `a ⟂ d`, any prime divisor of `g` divides `12` and `3`, hence only
    `2` or `3` can remain.
  * Both cofactors are odd because `d` is odd, so `2` is impossible.
  * If `3` divided both, then `a^2 + d^2 ≡ 0 [ZMOD 3]`, which forces
    `3 ∣ a` and `3 ∣ d`, contradicting `a ⟂ d`.
  -/
  sorry

private lemma pos_four_sq_add_sq_of_pos_right {a d : ℤ}
    (hdpos : 0 < d) : 0 < 4 * a ^ 2 + d ^ 2 := by
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hdsq : 0 < d ^ 2 := sq_pos_of_ne_zero hdne
  have hasq : 0 ≤ a ^ 2 := sq_nonneg a
  nlinarith

private lemma pos_sixteen_sq_add_sq_of_pos_right {a d : ℤ}
    (hdpos : 0 < d) : 0 < 16 * a ^ 2 + d ^ 2 := by
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hdsq : 0 < d ^ 2 := sq_pos_of_ne_zero hdne
  have hasq : 0 ≤ a ^ 2 := sq_nonneg a
  nlinarith

/-- The new descent `A` is even, but this must be proved after balance. -/
private lemma even_of_sq_eq_four_sq_add_odd_sq
    {a d c : ℤ}
    (hdodd : Odd d)
    (hc : c ^ 2 = 4 * a ^ 2 + d ^ 2) :
    Even a := by
  /-
  If `a` were odd, then `4*a^2 ≡ 4 (mod 8)` and `d^2 ≡ 1 (mod 8)`,
  so `c^2 ≡ 5 (mod 8)`, impossible for an integer square.
  Recommended local support lemmas:
    * `odd_sq_mod_eight_int : Odd x → x^2 % 8 = 1`
    * `sq_mod_eight_ne_five_int : x^2 % 8 ≠ 5`
  -/
  sorry

private lemma descent_product_lt
    {EA ED a b c d : ℤ}
    (hapos : 0 < a) (hbpos : 0 < b) (hcpos : 0 < c) (hdpos : 0 < d)
    (hEDpos : 0 < ED)
    (hEA : EA = 2 * a * b * c * d) :
    a * d < EA * ED := by
  have hadpos : 0 < a * d := mul_pos hapos hdpos
  have hbcpos : 0 < b * c := mul_pos hbpos hcpos
  have hbcepos : 0 < b * c * ED := mul_pos hbcpos hEDpos
  have hbce_ge_one : (1 : ℤ) ≤ b * c * ED := by omega
  have hfactor_gt_one : (1 : ℤ) < 2 * (b * c * ED) := by nlinarith
  have hdiffpos : 0 < a * d * (2 * (b * c * ED) - 1) := by
    exact mul_pos hadpos (sub_pos.mpr hfactor_gt_one)
  calc
    a * d < (a * d) * (2 * (b * c * ED)) := by nlinarith
    _ = (2 * a * b * c * d) * ED := by ring
    _ = EA * ED := by rw [hEA]

/--
Common signed-orientation adapter.  Use the existing
`refinement_equation_of_same_orientation` inside each branch if its statement
already matches; otherwise the direct proof is just `ring_nf` from the common
signed equality.
-/
private lemma balance_equation_of_signed_orientation
    {D U V Up Vp a b c d : ℤ}
    (hU : U = 2 * a * b)
    (hV : V = c * d)
    (hUp : Up = 2 * a * c)
    (hVp : Vp = b * d)
    (horient :
      (D = U ^ 2 - V ^ 2 ∧ D = 4 * Up ^ 2 - Vp ^ 2) ∨
      (-D = U ^ 2 - V ^ 2 ∧ -D = 4 * Up ^ 2 - Vp ^ 2)) :
    b ^ 2 * (4 * a ^ 2 + d ^ 2) =
      c ^ 2 * (16 * a ^ 2 + d ^ 2) := by
  rcases horient with hpos | hneg
  · -- Preferred if the existing theorem accepts the positive common value.
    exact refinement_equation_of_same_orientation hU hV hUp hVp hpos.1 hpos.2
  · -- Same theorem, with common value `-D`.
    exact refinement_equation_of_same_orientation hU hV hUp hVp hneg.1 hneg.2

/-- Constructive Euler descent. -/
theorem eulerSquarePairDescent_constructive :
    EulerSquarePairDescent := by
  intro E

  obtain ⟨U, V, Up, Vp,
      hUpos, hVpos, hUppos, hVppos,
      hUVcop, hUpVpcop,
      hUeven, hVodd, hUpeven, hVpodd,
      hEA_UV, hEA_UpVp,
      hCparam, hBparam,
      horient⟩ :=
    signed_even_odd_params_same_orientation E

  have hprod : U * V = Up * Vp := by
    exact hEA_UV.symm.trans hEA_UpVp

  obtain ⟨k, b, c, d,
      hkpos, hbpos, hcpos, hdpos,
      hUfac, hVfac, hUpfac, hVpfac,
      hkb, hkc, hkd, hbc, hbd, hcd⟩ :=
    two_coprime_factorizations_refine_int_pos
      hUpos hVpos hUppos hVppos hUVcop hUpVpcop hprod

  have hcdOdd : Odd (c * d) := by
    rw [← hVfac]
    exact hVodd
  obtain ⟨hcOdd, hdOdd⟩ := odd_factors_of_odd_mul_int hcdOdd

  have hbdOdd : Odd (b * d) := by
    rw [← hVpfac]
    exact hVpodd
  obtain ⟨hbOdd, _hdOdd'⟩ := odd_factors_of_odd_mul_int hbdOdd

  have hkEven : Even k := by
    have hkbEven : Even (k * b) := by
      rw [← hUfac]
      exact hUeven
    exact even_left_of_even_mul_odd_int hkbEven hbOdd

  obtain ⟨a, hapos, hk_eq⟩ := even_pos_as_two_mul hkpos hkEven

  have hUfac' : U = 2 * a * b := by
    rw [hUfac, hk_eq]
    ring
  have hUpfac' : Up = 2 * a * c := by
    rw [hUpfac, hk_eq]
    ring

  have hEA_prod : E.A = 2 * a * b * c * d := by
    calc
      E.A = U * V := hEA_UV
      _ = (2 * a * b) * (c * d) := by rw [hUfac', hVfac]
      _ = 2 * a * b * c * d := by ring

  have had : IsCoprime a d := by
    apply coprime_of_coprime_two_mul_left
    simpa [hk_eq] using hkd

  have hbalance :
      b ^ 2 * (4 * a ^ 2 + d ^ 2) =
        c ^ 2 * (16 * a ^ 2 + d ^ 2) :=
    balance_equation_of_signed_orientation
      (D := E.D)
      hUfac' hVfac hUpfac' hVpfac horient

  let M : ℤ := 4 * a ^ 2 + d ^ 2
  let N : ℤ := 16 * a ^ 2 + d ^ 2

  have hMpos : 0 < M := by
    dsimp [M]
    exact pos_four_sq_add_sq_of_pos_right hdpos
  have hNpos : 0 < N := by
    dsimp [N]
    exact pos_sixteen_sq_add_sq_of_pos_right hdpos
  have hMNcop : IsCoprime M N := by
    dsimp [M, N]
    exact coprime_four_sq_add_odd_sq_sixteen_sq_add_odd_sq had hdOdd
  have hbalanceMN : b ^ 2 * M = c ^ 2 * N := by
    dsimp [M, N]
    exact hbalance

  obtain ⟨hM_eq_csq, hN_eq_bsq⟩ :=
    square_factor_balance_int
      hbpos hcpos hMpos hNpos hbc hMNcop hbalanceMN

  have hCsq : c ^ 2 = 4 * a ^ 2 + d ^ 2 := by
    dsimp [M] at hM_eq_csq
    exact hM_eq_csq.symm
  have hBsq : b ^ 2 = 16 * a ^ 2 + d ^ 2 := by
    dsimp [N] at hN_eq_bsq
    exact hN_eq_bsq.symm

  have haEven : Even a :=
    even_of_sq_eq_four_sq_add_odd_sq hdOdd hCsq

  refine ⟨
    { A := a,
      D := d,
      B := b,
      C := c,
      hApos := hapos,
      hDpos := hdpos,
      hBpos := hbpos,
      hCpos := hcpos,
      hDodd := hdOdd,
      hAeven := haEven,
      hAD := had,
      hB := hBsq,
      hC := hCsq }, ?_⟩

  change a * d < E.A * E.D
  exact descent_product_lt hapos hbpos hcpos hdpos E.hDpos hEA_prod

end MazurProof.RationalPointsN12
```

If the actual `EulerSquarePair` field names differ, only the final named record literal and the projection `E.hDpos` need syntactic adjustment.  The theorem body is otherwise independent of AP material.

## Proof DAG

1. Call `signed_even_odd_params_same_orientation E`.
2. Turn the two equations `E.A=U*V` and `E.A=Up*Vp` into `U*V=Up*Vp`.
3. Apply the Int wrapper around `two_coprime_factorizations_refine_nat`:
   ```lean
   U=k*b, V=c*d, Up=k*c, Vp=b*d
   ```
   with positive `k,b,c,d` and pairwise coprimalities.
4. From `Odd V` and `V=c*d`, get `Odd c` and `Odd d`; from `Odd Vp` and `Vp=b*d`, get `Odd b`.
5. From `Even U`, `U=k*b`, and `Odd b`, get `Even k`; write `k=2*a`, with `0<a`.
6. Rewrite the refinement as
   ```lean
   U=2*a*b, V=c*d, Up=2*a*c, Vp=b*d.
   ```
7. Use the signed orientation branch to prove the balance equation.  The negative branch is handled by using common value `-E.D`.
8. Set
   ```lean
   M = 4*a^2+d^2
   N = 16*a^2+d^2
   ```
   prove `0<M`, `0<N`, and `IsCoprime M N`.
9. Apply `square_factor_balance_int` to get `M=c^2` and `N=b^2`; flip them to the `hC` and `hB` field orientations.
10. Prove `Even a` using `c^2 = 4*a^2 + d^2` and `Odd d` modulo `8`.
11. Construct
    ```lean
    F = ⟨a,d,b,c,...⟩
    ```
    and prove the strict descent from `E.A = 2*a*b*c*d` and `0<E.D`.
