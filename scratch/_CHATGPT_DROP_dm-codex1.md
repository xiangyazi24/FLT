# Q2632 (dm-codex1): EulerSquarePairDescent constructive descent

Target file: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`

This drop is only about `EulerSquarePairDescent`.  I am not using or discussing the already-checked AP-to-Euler construction.

## 1. Adversarial verdict on the proposed smaller pair

The proposed smaller pair

```lean
F.A = a
F.D = d
F.B = b
F.C = c
```

is mathematically correct **only with the following naming convention**:

```lean
U  = 2 * a * b
V  = c * d
Up = 2 * a * c
Vp = b * d
```

That is, `a` must be **half of the common refinement factor** in the two coprime factorizations of `E.A`.

If the Nat refinement theorem first returns

```lean
U  = k * b
V  = c * d
Up = k * c
Vp = b * d
```

then the descent factor is not `k`; it is `a` where `k = 2 * a`.  The final smaller pair is `(a,d,b,c)`, not `(k,d,b,c)`.

The subtle parity point is important:

* From `Even U`, `Odd b`, and `U = k*b`, we can prove `Even k`.
* Writing `k = 2*a`, we **cannot** prove `Even a` from the original parity/refinement data alone.
* Example showing the false step: `k = 2`, `a = 1`, `b = c = d = 1` has `U = Up = 2`, `V = Vp = 1`, and all pairwise coprimalities, but `a` is odd.
* The proof that the new Euler `A` is even must come **after** the square-factor balance gives

```lean
c^2 = 4*a^2 + d^2
```

with `Odd d`.  If `a` were odd, then modulo `8` the right side would be `4 + 1 = 5`, impossible for an integer square.  So `Even a` is a post-balance lemma, not a refinement/parity-transfer lemma.

The negative signed-orientation branch is harmless.  In both branches we get the same equality

```lean
U^2 - V^2 = 4*Up^2 - Vp^2
```

because both sides equal either `E.D` or `-E.D`.  Therefore both branches produce the same refinement equation

```lean
b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2)
```

and hence the same descended square pair.

## 2. Lean-friendly proof DAG

Use the following DAG for `eulerSquarePairDescent_constructive`.

1. Call `signed_even_odd_params_same_orientation E`, obtaining `U V Up Vp` and the two parameterizations.
2. Prove the common product equality:

   ```lean
   U * V = Up * Vp
   ```

   by transitivity through `E.A`.
3. Apply an integer wrapper around `two_coprime_factorizations_refine_nat`, returning positive integers `k b c d` with

   ```lean
   U  = k * b
   V  = c * d
   Up = k * c
   Vp = b * d
   ```

   and pairwise coprimalities.
4. Transfer parity:

   * from `Odd V` and `V = c*d`, get `Odd c` and `Odd d`;
   * from `Odd Vp` and `Vp = b*d`, get `Odd b`;
   * from `Even U`, `U = k*b`, and `Odd b`, get `Even k`;
   * since `0 < k`, write `k = 2*a` with `0 < a`.
5. Rewrite the refinement equations as

   ```lean
   U  = 2 * a * b
   V  = c * d
   Up = 2 * a * c
   Vp = b * d
   ```

6. Use the signed-orientation adapter around `refinement_equation_of_same_orientation` to prove

   ```lean
   hbal : b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2)
   ```

7. Set

   ```lean
   M := 4*a^2 + d^2
   N := 16*a^2 + d^2
   ```

   Prove `0 < M`, `0 < N`, and

   ```lean
   IsCoprime M N
   ```

   from `IsCoprime a d` and `Odd d`.
8. Apply the checked auxiliary theorem

   ```lean
   square_factor_balance_int
   ```

   with `hbpos hcpos hMpos hNpos hbccop hMNcop hbal`, obtaining

   ```lean
   M = c^2
   N = b^2
   ```

9. Convert these into the Euler equations for `F`:

   ```lean
   c^2 = 4*a^2 + d^2
   b^2 = 16*a^2 + d^2
   ```

10. Prove `Even a` from `c^2 = 4*a^2 + d^2` and `Odd d` by the mod-`8` lemma.
11. Construct

   ```lean
   F : EulerSquarePair :=
   { A := a, D := d, B := b, C := c, ... }
   ```

12. Prove descent using only positivity:

   ```lean
   E.A = 2*a*b*c*d
   0 < E.D
   0 < a, 0 < b, 0 < c, 0 < d
   ```

   Then `a*d < E.A * E.D` because `E.A * E.D = a*d * (2*b*c*E.D)` and `2*b*c*E.D > 1`.

## 3. Hidden missing hypotheses / likely false steps

These are the implementation traps I would fix before trying the final theorem.

1. **Do not try to prove `Even a` immediately after refinement.**  That is false if `a` is the half-common factor.  The correct proof uses the balanced square equation and `Odd d`.
2. **The balance theorem needs `IsCoprime M N`.**  This is not automatic from `IsCoprime b c`.  Add a dedicated lemma proving

   ```lean
   IsCoprime (4*a^2 + d^2) (16*a^2 + d^2)
   ```

   from `IsCoprime a d` and `Odd d`.
3. **You need an Int-facing refinement wrapper.**  The checked theorem is Nat-facing; the descent theorem data are positive integers.  Do the Nat conversion once in a private wrapper and keep the main descent proof purely over `ℤ`.
4. **The negative orientation branch should not branch the whole descent.**  Adapt both signed branches immediately into the same balance equation, then continue linearly.
5. **The descent inequality should not use the sign/orientation formula for `E.D`.**  It only needs the structure field `0 < E.D` and the factorization of `E.A`.
6. **If `IsCoprime` is sign-sensitive in local lemmas**, normalize signs in the Int wrapper by using positivity and `toNat`; after that all factors are positive.

## 4. Code skeleton

The following is the Lean-facing skeleton I would add.  The helper lemmas marked with `sorry` are the intended explicit auxiliary lemmas; the main descent proof then has no further mathematical branching.  Field accessor names for `EulerSquarePair` may need the local names from the existing structure, but the theorem statement should be this one.

```lean
import FLT.Assumptions.MazurProof.N12EulerAux
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/--
Integer-facing wrapper around the checked Nat refinement theorem.

Use `two_coprime_factorizations_refine_nat` internally.  The main descent proof
should not have to see `toNat` casts.
-/
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
  * use positivity to rewrite `(U.toNat : ℤ) = U`, etc.;
  * cast `hprod` to the Nat product equality;
  * convert `IsCoprime U V` and `IsCoprime Up Vp` to the Nat coprimalities
    required by `two_coprime_factorizations_refine_nat`;
  * call `two_coprime_factorizations_refine_nat`;
  * cast the returned positive Nat factors back to Int;
  * convert all returned Nat coprimalities to `IsCoprime` over `ℤ`.
  -/
  sorry

private lemma odd_factors_of_odd_mul_int {x y : ℤ}
    (hxy : Odd (x * y)) : Odd x ∧ Odd y := by
  -- Use the local parity API if it already has this.  Otherwise prove by
  -- contradiction: if one factor is even, the product is even.
  sorry

private lemma even_left_of_even_mul_odd_int {x y : ℤ}
    (hxy : Even (x * y)) (hy : Odd y) : Even x := by
  -- If `x` were odd, then `x*y` would be odd, contradicting `hxy`.
  sorry

private lemma even_pos_as_two_mul {k : ℤ}
    (hkpos : 0 < k) (hkeven : Even k) :
    ∃ a : ℤ, 0 < a ∧ k = 2 * a := by
  rcases hkeven with ⟨a, ha⟩
  refine ⟨a, ?_, ?_⟩
  · -- Depending on the local `Even` witness shape, `ha` is either
    -- `k = a + a` or `k = 2*a`; both are discharged by linear arithmetic.
    nlinarith
  · nlinarith

private lemma coprime_of_coprime_two_mul_left {a d : ℤ}
    (h : IsCoprime (2 * a) d) : IsCoprime a d := by
  -- Any common divisor of `a` and `d` is also a common divisor of `2*a` and `d`.
  -- This is usually a one-line divisibility/gcd argument using the local
  -- `IsCoprime` API.
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

/--
Cofactor coprimality needed by `square_factor_balance_int`.

Mathematics:
if a prime divides both cofactors, it divides their difference `12*a^2` and
also `4*(4*a^2+d^2) - (16*a^2+d^2) = 3*d^2`.  Since `a ⟂ d`, only primes
`2` or `3` can survive.  Odd `d` makes both cofactors odd, ruling out `2`.
Modulo `3`, the condition would force `a^2 + d^2 ≡ 0`, impossible unless
`3 ∣ a` and `3 ∣ d`, contradicting coprimality.
-/
private lemma coprime_four_sq_add_odd_sq_sixteen_sq_add_odd_sq
    {a d : ℤ}
    (had : IsCoprime a d)
    (hdodd : Odd d) :
    IsCoprime (4 * a ^ 2 + d ^ 2) (16 * a ^ 2 + d ^ 2) := by
  sorry

/-- The new descent `A` is even, but only after the balance equation. -/
private lemma even_of_sq_eq_four_sq_add_odd_sq
    {a d c : ℤ}
    (hdodd : Odd d)
    (hc : c ^ 2 = 4 * a ^ 2 + d ^ 2) :
    Even a := by
  /-
  Prove modulo 8.

  Suggested support lemmas:
    * `odd_sq_mod_eight_int : Odd x → x^2 % 8 = 1`
    * `sq_mod_eight_ne_five_int : x^2 % 8 ≠ 5`

  If `a` is odd, then `a^2 ≡ 1 (mod 8)`, hence `4*a^2 ≡ 4`, and odd `d`
  gives `d^2 ≡ 1`.  Then `c^2 ≡ 5 (mod 8)`, impossible.
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
  have hbcEDpos : 0 < b * c * ED := mul_pos hbcpos hEDpos
  have hbcED_ge_one : (1 : ℤ) ≤ b * c * ED := by omega
  have hfactor_gt_one : (1 : ℤ) < 2 * (b * c * ED) := by nlinarith
  calc
    a * d < (a * d) * (2 * (b * c * ED)) := by
      nlinarith [hadpos, hfactor_gt_one]
    _ = (2 * a * b * c * d) * ED := by ring
    _ = EA * ED := by rw [hEA]

/--
Signed-orientation adapter.  This keeps the negative branch out of the main
proof.  If the existing `refinement_equation_of_same_orientation` has a
slightly different argument order, adjust only this adapter.
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
  · exact refinement_equation_of_same_orientation hU hV hUp hVp hpos.1 hpos.2
  · exact refinement_equation_of_same_orientation hU hV hUp hVp hneg.1 hneg.2

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
      hU_kb, hV_cd, hUp_kc, hVp_bd,
      hkb_cop, hkc_cop, hkd_cop,
      hbc_cop, hbd_cop, hcd_cop⟩ :=
    two_coprime_factorizations_refine_int_pos
      hUpos hVpos hUppos hVppos hUVcop hUpVpcop hprod

  have hcd_odd : Odd (c * d) := by
    simpa [hV_cd] using hVodd
  have hcodd : Odd c := (odd_factors_of_odd_mul_int hcd_odd).1
  have hdodd : Odd d := (odd_factors_of_odd_mul_int hcd_odd).2

  have hbd_odd : Odd (b * d) := by
    simpa [hVp_bd] using hVpodd
  have hbodd : Odd b := (odd_factors_of_odd_mul_int hbd_odd).1

  have hkb_even : Even (k * b) := by
    simpa [hU_kb] using hUeven
  have hkeven : Even k :=
    even_left_of_even_mul_odd_int hkb_even hbodd

  obtain ⟨a, hapos, hk_eq_twoa⟩ :=
    even_pos_as_two_mul hkpos hkeven

  have hU : U = 2 * a * b := by
    calc
      U = k * b := hU_kb
      _ = (2 * a) * b := by rw [hk_eq_twoa]
      _ = 2 * a * b := by ring

  have hUp : Up = 2 * a * c := by
    calc
      Up = k * c := hUp_kc
      _ = (2 * a) * c := by rw [hk_eq_twoa]
      _ = 2 * a * c := by ring

  have htwoad_cop : IsCoprime (2 * a) d := by
    simpa [hk_eq_twoa] using hkd_cop
  have had_cop : IsCoprime a d :=
    coprime_of_coprime_two_mul_left htwoad_cop

  have hbal :
      b ^ 2 * (4 * a ^ 2 + d ^ 2) =
        c ^ 2 * (16 * a ^ 2 + d ^ 2) := by
    exact balance_equation_of_signed_orientation
      (D := E.D) hU hV_cd hUp hVp_bd horient

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
    exact coprime_four_sq_add_odd_sq_sixteen_sq_add_odd_sq had_cop hdodd

  have hbalMN : b ^ 2 * M = c ^ 2 * N := by
    dsimp [M, N]
    exact hbal

  obtain ⟨hM_eq_csq, hN_eq_bsq⟩ :=
    square_factor_balance_int
      hbpos hcpos hMpos hNpos hbc_cop hMNcop hbalMN

  have hC_F : c ^ 2 = 4 * a ^ 2 + d ^ 2 := by
    simpa [M] using hM_eq_csq.symm

  have hB_F : b ^ 2 = 16 * a ^ 2 + d ^ 2 := by
    simpa [N] using hN_eq_bsq.symm

  have haeven : Even a :=
    even_of_sq_eq_four_sq_add_odd_sq hdodd hC_F

  have hEA_factor : E.A = 2 * a * b * c * d := by
    calc
      E.A = U * V := hEA_UV
      _ = (2 * a * b) * (c * d) := by rw [hU, hV_cd]
      _ = 2 * a * b * c * d := by ring

  let F : EulerSquarePair :=
    { A := a
      D := d
      B := b
      C := c
      hApos := hapos
      hDpos := hdpos
      hBpos := hbpos
      hCpos := hcpos
      hDodd := hdodd
      hAeven := haeven
      hADcop := had_cop
      hB := hB_F
      hC := hC_F }

  refine ⟨F, ?_⟩
  have hlt : a * d < E.A * E.D :=
    descent_product_lt
      hapos hbpos hcpos hdpos E.hDpos hEA_factor
  simpa [F] using hlt

end MazurProof.RationalPointsN12
```

## 5. Implementation note on field names

The only intentionally uncertain names in the skeleton are structure field accessors such as `hApos`, `hDpos`, `hADcop`, and `E.hDpos`.  Replace those with the actual field names in `EulerSquarePair` if they differ.  The mathematical interfaces that matter are:

```lean
A D B C : ℤ
0 < A, 0 < D, 0 < B, 0 < C
Odd D
Even A
IsCoprime A D
B^2 = 16*A^2 + D^2
C^2 = 4*A^2 + D^2
```

Everything else in the theorem should remain as above: refine with common factor `k`, split `k = 2*a`, balance, prove `Even a`, construct `F=(a,d,b,c)`, and prove the strict inequality by positivity.
