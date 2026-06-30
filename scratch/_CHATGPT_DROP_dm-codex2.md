# Q2450 two coprime factorizations refinement Lean route

## Verdict

The stated theorem is true under the given hypotheses.  In fact, `hApos` and `hV'odd` are redundant for this exact refinement: positivity of `U,V,U',V'`, the two product equations, evenness of `U,U'`, oddness of `V`, and the two coprimality hypotheses already drive the construction.  Keep the redundant hypotheses anyway for interface stability with the Q2448/Q2450 EulerAux route.

A useful sanity check: if the second coprimality hypothesis is dropped, the statement is false.  Example:

```lean
A = 18, U = 2, V = 9, U' = 6, V' = 3
```

Then `A = U*V = U'*V'`, both first factors are even and both second factors are odd, and `IsCoprime U V` holds, but `IsCoprime U' V'` fails.  The desired refinement would force the common `b` factor to sit in `V'` while also remaining coprime to `U'`, which is impossible in this example.

## Best Lean route: stay in `ℤ`, use `Int.exists_gcd_one`

Do not start with `Nat` unless you want extra `natAbs` bookkeeping.  The clean route is:

1. Set `g : ℤ := (Int.gcd U U' : ℤ)`.
2. Use `Int.exists_gcd_one` to get
   `U = b*g`, `U' = c*g`, and `Int.gcd b c = 1`.
3. Convert `Int.gcd b c = 1` to `IsCoprime b c` using
   `Int.isCoprime_iff_gcd_eq_one.mpr`.
4. Since `2 ∣ U` and `2 ∣ U'`, prove `2 ∣ g` by `Int.dvd_coe_gcd`; write `g = 2*a`.
5. Cancel `g` from `U*V = U'*V'` to get `b*V = c*V'`.
6. Euclid with `IsCoprime b c` gives `c ∣ V` and `b ∣ V'`; write `V = c*d`, then cancel `c` to prove `V' = b*d`.
7. Project all pairwise coprimalities using `IsCoprime.mono` from the two original coprime factorizations.

The important point is that the pairwise facts involving `b` come from the *second* factorization, while the pairwise facts involving `c` come from the *first* factorization:

```text
IsCoprime (2*a) b : from IsCoprime U' V', since 2*a ∣ U' and b ∣ V'
IsCoprime (2*a) c : from IsCoprime U V,  since 2*a ∣ U  and c ∣ V
IsCoprime (2*a) d : from IsCoprime U V,  since 2*a ∣ U  and d ∣ V
IsCoprime b c     : from gcd-quotients by g = gcd U U'
IsCoprime b d     : from IsCoprime U V,  since b ∣ U and d ∣ V
IsCoprime c d     : from IsCoprime U' V', since c ∣ U' and d ∣ V'
```

## Compile-oriented patch

This is the first patch I would try.  It is intentionally local: no Pythagorean-triple dependencies and no square-balance descent assumptions.

```lean
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic

namespace EulerAux

def PairwiseCoprime2abcd (a b c d : ℤ) : Prop :=
  IsCoprime (2*a) b ∧
  IsCoprime (2*a) c ∧
  IsCoprime (2*a) d ∧
  IsCoprime b c ∧
  IsCoprime b d ∧
  IsCoprime c d

structure RefinedFactors (A U V U' V' : ℤ) where
  a b c d : ℤ
  hapos : 0 < a
  hbpos : 0 < b
  hcpos : 0 < c
  hdpos : 0 < d
  hU : U = 2*a*b
  hV : V = c*d
  hU' : U' = 2*a*c
  hV' : V' = b*d
  hA : A = 2*a*b*c*d
  hdodd : Odd d
  hpair : PairwiseCoprime2abcd a b c d

/--
Common refinement of two positive coprime factorizations whose first factors are even
and whose second factors are odd.

The proof uses `g = gcd U U'`, writes `U = b*g`, `U' = c*g`, proves
`g = 2*a`, then obtains the common tail `d` from `b*V = c*V'`.
-/
theorem two_coprime_factorizations_refine_even_pos
    {A U V U' V' : ℤ}
    (hApos : 0 < A)
    (hUV : A = U*V)
    (hU'V' : A = U'*V')
    (hUpos : 0 < U) (hVpos : 0 < V)
    (hU'pos : 0 < U') (hV'pos : 0 < V')
    (hUeven : Even U) (hU'even : Even U')
    (hVodd : Odd V) (hV'odd : Odd V')
    (hUVcop : IsCoprime U V)
    (hU'V'cop : IsCoprime U' V') :
    RefinedFactors A U V U' V' := by
  -- These two hypotheses are kept for caller compatibility, but this proof does not need them.
  have _hApos_keep : 0 < A := hApos
  have _hV'odd_keep : Odd V' := hV'odd

  let g : ℤ := (Int.gcd U U' : ℤ)

  have hgposNat : 0 < Int.gcd U U' :=
    Int.gcd_pos_of_ne_zero_left U' (ne_of_gt hUpos)
  have hgpos : 0 < g := by
    dsimp [g]
    exact_mod_cast hgposNat

  -- `Int.exists_gcd_one` gives primitive quotients by the positive integer gcd.
  obtain ⟨b, c, hbc_gcd, hU_bg0, hU'_cg0⟩ :=
    Int.exists_gcd_one (m := U) (n := U') hgposNat

  have hU_bg : U = b * g := by
    simpa [g] using hU_bg0
  have hU'_cg : U' = c * g := by
    simpa [g] using hU'_cg0

  have hbpos : 0 < b := by
    have hprod : 0 < b * g := by
      simpa [hU_bg] using hUpos
    exact pos_of_mul_pos_right hprod (le_of_lt hgpos)
  have hcpos : 0 < c := by
    have hprod : 0 < c * g := by
      simpa [hU'_cg] using hU'pos
    exact pos_of_mul_pos_right hprod (le_of_lt hgpos)

  have hbc : IsCoprime b c := by
    exact Int.isCoprime_iff_gcd_eq_one.mpr hbc_gcd

  -- Since both `U` and `U'` are even, their integer gcd is even.
  have h2g : (2 : ℤ) ∣ g := by
    dsimp [g]
    exact Int.dvd_coe_gcd hUeven.two_dvd hU'even.two_dvd
  obtain ⟨a, hg2a⟩ := h2g

  have hapos : 0 < a := by
    nlinarith [hgpos, hg2a]

  have hU_final : U = 2*a*b := by
    calc
      U = b * g := hU_bg
      _ = b * (2*a) := by rw [hg2a]
      _ = 2*a*b := by ring

  have hU'_final : U' = 2*a*c := by
    calc
      U' = c * g := hU'_cg
      _ = c * (2*a) := by rw [hg2a]
      _ = 2*a*c := by ring

  -- Cancel the common gcd from the equality of the two products.
  have hg_ne : g ≠ 0 := ne_of_gt hgpos
  have hgEq : g * (b * V) = g * (c * V') := by
    calc
      g * (b * V) = (b * g) * V := by ring
      _ = U * V := by rw [← hU_bg]
      _ = A := hUV.symm
      _ = U' * V' := hU'V'
      _ = (c * g) * V' := by rw [← hU'_cg]
      _ = g * (c * V') := by ring
  have hcommon : b * V = c * V' :=
    mul_left_cancel₀ hg_ne hgEq

  -- Euclid on the primitive quotients: `c | V` and `b | V'`.
  have hc_dvd_V : c ∣ V := by
    have hc_dvd_bV : c ∣ b * V := by
      rw [hcommon]
      exact ⟨V', by ring⟩
    exact hbc.symm.dvd_of_dvd_mul_left hc_dvd_bV

  have hb_dvd_V' : b ∣ V' := by
    have hb_dvd_cV' : b ∣ c * V' := by
      rw [← hcommon]
      exact ⟨V, by ring⟩
    exact hbc.dvd_of_dvd_mul_left hb_dvd_cV'

  obtain ⟨d, hV_cd⟩ := hc_dvd_V

  have hdpos : 0 < d := by
    have hprod : 0 < c * d := by
      simpa [hV_cd] using hVpos
    exact pos_of_mul_pos_left hprod (le_of_lt hcpos)

  have hV'_bd : V' = b * d := by
    have hcEq : c * (b * d) = c * V' := by
      calc
        c * (b * d) = b * (c * d) := by ring
        _ = b * V := by rw [← hV_cd]
        _ = c * V' := hcommon
    have hbd : b * d = V' :=
      mul_left_cancel₀ (ne_of_gt hcpos) hcEq
    exact hbd.symm

  have hdodd : Odd d := by
    have hcdodd : Odd (c * d) := by
      simpa [hV_cd] using hVodd
    exact Int.Odd.of_mul_right hcdodd

  have hA_final : A = 2*a*b*c*d := by
    calc
      A = U * V := hUV
      _ = (2*a*b) * (c*d) := by rw [hU_final, hV_cd]
      _ = 2*a*b*c*d := by ring

  -- Divisibility projections used by `IsCoprime.mono`.
  have h2a_dvd_U : 2*a ∣ U := by
    rw [hU_final]
    exact ⟨b, by ring⟩
  have hb_dvd_U : b ∣ U := by
    rw [hU_final]
    exact ⟨2*a, by ring⟩
  have h2a_dvd_U' : 2*a ∣ U' := by
    rw [hU'_final]
    exact ⟨c, by ring⟩
  have hc_dvd_U' : c ∣ U' := by
    rw [hU'_final]
    exact ⟨2*a, by ring⟩
  have hd_dvd_V : d ∣ V := by
    rw [hV_cd]
    exact ⟨c, by ring⟩
  have hd_dvd_V' : d ∣ V' := by
    rw [hV'_bd]
    exact ⟨b, by ring⟩

  have h2ab : IsCoprime (2*a) b :=
    IsCoprime.mono h2a_dvd_U' hb_dvd_V' hU'V'cop
  have h2ac : IsCoprime (2*a) c :=
    IsCoprime.mono h2a_dvd_U hc_dvd_V hUVcop
  have h2ad : IsCoprime (2*a) d :=
    IsCoprime.mono h2a_dvd_U hd_dvd_V hUVcop
  have hbd : IsCoprime b d :=
    IsCoprime.mono hb_dvd_U hd_dvd_V hUVcop
  have hcd : IsCoprime c d :=
    IsCoprime.mono hc_dvd_U' hd_dvd_V' hU'V'cop

  exact
  { a := a
    b := b
    c := c
    d := d
    hapos := hapos
    hbpos := hbpos
    hcpos := hcpos
    hdpos := hdpos
    hU := hU_final
    hV := hV_cd
    hU' := hU'_final
    hV' := hV'_bd
    hA := hA_final
    hdodd := hdodd
    hpair := ⟨h2ab, h2ac, h2ad, hbc, hbd, hcd⟩ }

end EulerAux
```

## API checklist

These are the key Mathlib APIs used above.

```lean
-- gcd positivity and primitive quotient split
Int.gcd_pos_of_ne_zero_left
Int.exists_gcd_one

-- gcd divisibility and parity
Int.dvd_coe_gcd
Even.two_dvd

-- gcd=1 to Bezout-style coprime
Int.isCoprime_iff_gcd_eq_one

-- Euclid and coprime projections
IsCoprime.symm
IsCoprime.dvd_of_dvd_mul_left
IsCoprime.mono

-- odd product projection over integers
Int.Odd.of_mul_right
-- equivalently, use: (Int.odd_mul.mp h).2

-- ordered-domain cancellation/sign helpers
mul_left_cancel₀
pos_of_mul_pos_right
pos_of_mul_pos_left
```

If one of the divisibility/coprime projection elaborations is fragile in your local Mathlib snapshot, replace the affected line by the fully explicit form below:

```lean
exact IsCoprime.mono
  (x := 2*a) (y := U') (z := b) (w := V')
  h2a_dvd_U' hb_dvd_V' hU'V'cop
```

and similarly for the other projections.

## Why not the Nat-first route?

A Nat version is also true, but it is not shorter once the caller theorem is over `ℤ`.  The Nat proof would use:

```lean
Nat.gcd_dvd_left
Nat.gcd_dvd_right
Nat.gcd_div_gcd_div_gcd
Nat.Coprime.dvd_mul_left
Nat.Coprime.of_dvd
Nat.odd_mul / Nat.Odd.of_mul_right
Nat.Coprime.isCoprime
```

Then the integer theorem would need a cast layer through positive `natAbs` values.  The direct integer proof above avoids that cast layer and uses `Int.exists_gcd_one`, which already packages the primitive quotients by the integer gcd.
