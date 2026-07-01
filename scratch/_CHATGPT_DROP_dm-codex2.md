# Q2743 dm-codex2: Lean DAG for `EisensteinTriplePrimitiveFullParamStatement`

Namespace assumed throughout: `MazurProof.RationalPointsN12`.

I could not inspect the unpushed local WIP at `/Users/huangx/repos/flt-ai` through the GitHub connector. This DAG is therefore keyed to the facts in the prompt and to the exposed shape of `EisensteinFullParam` you described.

## Audit result

The route is sound provided `EisensteinTriple X Y Z` unfolds to the minus-sign Eisenstein equation

```lean
X ^ 2 - X * Y + Y ^ 2 = Z ^ 2
```

not the plus-sign equation. The listed identities with `2*m - n` and `m^2 - m*n + n^2` are exactly the minus-sign case.

Hidden pitfalls to avoid:

1. `common divisors of EA, EB divide 3` is not enough. You still need either:
   * raw: `IsCoprime EA EB`, using `¬ (3 : ℤ) ∣ m+n`, or
   * divided: quotient coprimality after writing `EA = 3*EA'`, `EB = 3*EB'`.
2. Do not use integer `/` for the divided sector. Introduce quotient witnesses from `3 ∣ m+n`.
3. The algebra step needs `C ≠ 0`, obtained from `Y = n*C`, `0 < Y`, `0 < n`.
4. The primitive scale kill first proves the scale is an integer. Primitive-ness alone does not make `C / EB` meaningful in Lean.
5. No swapped branch is needed if `eisenstein_slope_cross` is `m * Y = n * (Z + X)`: the same slope orientation gives the left `(X,Y)` disjunct. The swapped alternative is harmless fallback only.
6. The unit triple `(1,1,1)` is the divided case with `(m,n)=(2,1)`, `EB=3`, `C=1`.

## Notation and imports

All snippets below are intended inside `FLT/Assumptions/MazurProof/N12ParamBridge.lean` above the frontier theorem. If making a temporary helper file, use:

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n
private abbrev EC (m n : ℤ) : ℤ := 2 * m * n - n ^ 2
private abbrev EZ (m n : ℤ) : ℤ := m ^ 2 - m * n + n ^ 2

end MazurProof.RationalPointsN12
```

## Implementation DAG

| order | lemma | kind | output used later |
|---:|---|---|---|
| 1 | `eisenstein_EC_eq_n_mul_EB` | pure algebra | `EC m n = n * EB m n` |
| 2 | `eisenstein_EB_pos` | linear arithmetic | `0 < EB m n` from `0<n`, `n<m` |
| 3 | `eisenstein_C_of_cross` | divisibility API | `∃ C, Y=n*C ∧ Z+X=m*C ∧ 0<C` |
| 4 | `eisenstein_core_identities_eq` | pure algebra + `C≠0` cancellation | `EB*Z=EZ*C`, `EB*X=EA*C`, `EB*Y=EC*C` |
| 5 | `eisenstein_EA_EB_common_dvd_three` | divisibility API | every common divisor of `EA`, `EB` divides `3` |
| 6 | `eisenstein_factor_raw` | divisibility API | `IsCoprime (EA m n) (EB m n)` under `¬3∣m+n` |
| 7 | `eisenstein_factor_divided` | divisibility API | witnesses `EA=3*EA'`, `EB=3*EB'`, `0<EB'`, `IsCoprime EA' EB'` |
| 8 | `eisenstein_scale_kill_raw` | exact scale kill | `C=EB`, `X=EA`, `Y=EC`, `Z=EZ` |
| 9 | `eisenstein_scale_kill_divided` | exact scale kill | `C=EB'`, `3X=EA`, `3Y=EC`, `3Z=EZ` |
| 10 | frontier theorem | assembly | raw or divided `EisensteinFullParam` |

## Lemmas 1-4: decomposition and algebra

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n
private abbrev EC (m n : ℤ) : ℤ := 2 * m * n - n ^ 2
private abbrev EZ (m n : ℤ) : ℤ := m ^ 2 - m * n + n ^ 2

private theorem eisenstein_EC_eq_n_mul_EB (m n : ℤ) :
    EC m n = n * EB m n := by
  unfold EC EB
  ring

private theorem eisenstein_EB_pos {m n : ℤ} (hnpos : 0 < n) (hnm : n < m) :
    0 < EB m n := by
  unfold EB
  omega

/--
From `m*Y = n*(Z+X)` and `IsCoprime m n`, get the common scale `C`.
Likely API names:
* `IsCoprime.dvd_of_dvd_mul_left`
* `IsCoprime.dvd_of_dvd_mul_right`
If the product orientation differs, normalize by `simpa [mul_comm, mul_left_comm, mul_assoc]`.
-/
private theorem eisenstein_C_of_cross
    {X Y Z m n : ℤ}
    (hnpos : 0 < n)
    (hmn : IsCoprime m n)
    (hYpos : 0 < Y)
    (hcross : m * Y = n * (Z + X)) :
    ∃ C : ℤ, Y = n * C ∧ Z + X = m * C ∧ 0 < C := by
  have hn0 : n ≠ 0 := ne_of_gt hnpos
  have hn_dvd_mY : n ∣ m * Y := ⟨Z + X, hcross⟩
  have hn_dvd_Y : n ∣ Y := by
    -- exact (hmn.symm.dvd_of_dvd_mul_left hn_dvd_mY)
    -- or: exact (hmn.symm.dvd_of_dvd_mul_right (by simpa [mul_comm] using hn_dvd_mY))
    exact hmn.symm.dvd_of_dvd_mul_left hn_dvd_mY
  rcases hn_dvd_Y with ⟨C, hYC⟩
  have hZXC : Z + X = m * C := by
    apply mul_left_cancel₀ hn0
    calc
      n * (Z + X) = m * Y := hcross.symm
      _ = m * (n * C) := by rw [hYC]
      _ = n * (m * C) := by ring
  have hCpos : 0 < C := by
    have hmul : 0 < n * C := by simpa [hYC] using hYpos
    exact pos_of_mul_pos_left hmul (le_of_lt hnpos)
  exact ⟨C, hYC, hZXC, hCpos⟩

/--
Pure algebra core for the minus-sign Eisenstein equation.
Keep this equation-level lemma separate from the `EisensteinTriple` adapter.
-/
private theorem eisenstein_core_identities_eq
    {X Y Z m n C : ℤ}
    (hEq : X ^ 2 - X * Y + Y ^ 2 = Z ^ 2)
    (hYC : Y = n * C)
    (hZXC : Z + X = m * C)
    (hCne : C ≠ 0) :
    EB m n * Z = EZ m n * C ∧
    EB m n * X = EA m n * C ∧
    EB m n * Y = EC m n * C := by
  have hXlin : X = m * C - Z := by omega
  have hZeq : EB m n * Z = EZ m n * C := by
    have hprod : C * ((EB m n * Z) - (EZ m n * C)) = 0 := by
      subst Y
      rw [hXlin] at hEq
      unfold EB EZ
      ring_nf at hEq ⊢
      exact hEq
    have hsub : (EB m n * Z) - (EZ m n * C) = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hCne
    exact sub_eq_zero.mp hsub
  have hXeq : EB m n * X = EA m n * C := by
    rw [hXlin]
    calc
      EB m n * (m * C - Z)
          = (EB m n * m - EZ m n) * C := by
              rw [hZeq]
              ring
      _ = EA m n * C := by
              unfold EA EB EZ
              ring
  have hYeq : EB m n * Y = EC m n * C := by
    rw [hYC]
    unfold EB EC
    ring
  exact ⟨hZeq, hXeq, hYeq⟩

/--
Adapter: replace the first argument by whatever projection/unfolding gives
`X^2 - X*Y + Y^2 = Z^2` from local `EisensteinTriple`.
-/
-- private theorem eisenstein_core_identities
--     {X Y Z m n C : ℤ}
--     (htri : EisensteinTriple X Y Z)
--     (hYC : Y = n * C)
--     (hZXC : Z + X = m * C)
--     (hCne : C ≠ 0) :
--     EB m n * Z = EZ m n * C ∧
--     EB m n * X = EA m n * C ∧
--     EB m n * Y = EC m n * C := by
--   exact eisenstein_core_identities_eq (X:=X) (Y:=Y) (Z:=Z) (m:=m) (n:=n) (C:=C)
--     (by simpa [EisensteinTriple] using htri) hYC hZXC hCne

end MazurProof.RationalPointsN12
```

If `ring_nf at hEq ⊢; exact hEq` in `hprod` produces the negative factor instead, replace the target factor by `C * ((EZ m n * C) - (EB m n * Z)) = 0` and finish with `eq_comm`/`sub_eq_zero.mp`. The dependency is still purely algebraic.

## Lemmas 5-7: factor coprimality

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n
private abbrev EC (m n : ℤ) : ℤ := 2 * m * n - n ^ 2
private abbrev EZ (m n : ℤ) : ℤ := m ^ 2 - m * n + n ^ 2

/-- Divisibility API lemma: from `gcd(m,n)=1`, get `gcd(m,2m-n)=1`. -/
private theorem eisenstein_coprime_m_EB {m n : ℤ}
    (hmn : IsCoprime m n) :
    IsCoprime m (EB m n) := by
  -- Best route: use Bezout form of `hmn`.
  -- If `a*m + b*n = 1`, then `(a + 2*b)*m - b*(2*m-n) = 1`.
  -- Implement with the local `IsCoprime` Bezout constructor/projection.
  -- Expected finishing line after obtaining the Bezout witnesses: `ring_nf [EB]`.
  admit

/-- Every common divisor of `EA` and `EB` divides `3`. -/
private theorem eisenstein_EA_EB_common_dvd_three
    {m n d : ℤ}
    (hmn : IsCoprime m n)
    (hdEA : d ∣ EA m n)
    (hdEB : d ∣ EB m n) :
    d ∣ (3 : ℤ) := by
  -- 1. `d ∣ (2m-n)*(2m+n) = 4m^2-n^2` from `hdEB`.
  have hd4 : d ∣ 4 * m ^ 2 - n ^ 2 := by
    have h := dvd_mul_of_dvd_left hdEB (2 * m + n)
    convert h using 1 <;> unfold EB <;> ring
  -- 2. subtract `EA = m^2-n^2`, so `d ∣ 3*m^2`.
  have hd3m2 : d ∣ 3 * m ^ 2 := by
    have h := dvd_sub hd4 hdEA
    convert h using 1 <;> unfold EA <;> ring
  -- 3. `IsCoprime m EB`; since `d ∣ EB`, also `IsCoprime m d`.
  have hmEB : IsCoprime m (EB m n) := eisenstein_coprime_m_EB hmn
  have hmd : IsCoprime m d := by
    -- API variants: `hmEB.isCoprime_of_dvd_right hdEB`,
    -- `hmEB.coprime_dvd_right hdEB`, or prove from common-divisor definition.
    exact hmEB.isCoprime_of_dvd_right hdEB
  -- 4. Since `d` is coprime to `m^2`, Euclid gives `d ∣ 3`.
  have hdm2 : IsCoprime d (m ^ 2) := by
    -- API variants: `hmd.symm.pow_right 2`, `hmd.symm.pow_left 2`.
    simpa [pow_two] using hmd.symm.mul_right hmd.symm
  exact hdm2.dvd_of_dvd_mul_right (by simpa [mul_comm, mul_left_comm, mul_assoc] using hd3m2)

/-- Raw sector factor coprimality. -/
private theorem eisenstein_factor_raw
    {m n : ℤ}
    (hmn : IsCoprime m n)
    (h3 : ¬ (3 : ℤ) ∣ m + n) :
    IsCoprime (EA m n) (EB m n) := by
  -- Prove common-divisor criterion for `IsCoprime EA EB`.
  -- For a common divisor `d`, `eisenstein_EA_EB_common_dvd_three` gives `d ∣ 3`.
  -- Also `d ∣ EB`. If `d` is nonunit, then a prime factor `3` divides `EB`.
  -- But `3 ∣ EB ↔ 3 ∣ m+n` because
  --   2*(m+n) = EB + 3*n
  -- and `IsCoprime (3:ℤ) 2`.
  -- Contradiction to `h3`; hence every common divisor is a unit.
  admit

/-- Divided sector quotient witnesses and quotient coprimality. Avoid `/`. -/
private theorem eisenstein_factor_divided
    {m n : ℤ}
    (hmn : IsCoprime m n)
    (hEBpos : 0 < EB m n)
    (h3 : (3 : ℤ) ∣ m + n) :
    ∃ EA' EB' : ℤ,
      EA m n = 3 * EA' ∧
      EB m n = 3 * EB' ∧
      0 < EB' ∧
      IsCoprime EA' EB' := by
  rcases h3 with ⟨s, hs⟩
  refine ⟨(m - n) * s, 2 * s - n, ?_, ?_, ?_, ?_⟩
  · unfold EA
    rw [hs]
    ring
  · unfold EB
    rw [hs]
    ring
  · have : 0 < 3 * (2 * s - n) := by
      simpa [EB, hs] using hEBpos
    nlinarith
  · -- quotient coprimality:
    -- Let `d ∣ (m-n)*s` and `d ∣ 2*s-n`.
    -- Then `3*d ∣ EA m n` and `3*d ∣ EB m n` by the two quotient equations.
    -- `eisenstein_EA_EB_common_dvd_three` gives `3*d ∣ 3`.
    -- Cancel nonzero `3` to get `IsUnit d`.
    -- Use the same common-divisor criterion for `IsCoprime`.
    admit

end MazurProof.RationalPointsN12
```

The two `admit` blocks above are not mathematical gaps; they are API-finding blocks. They should be implemented with the repo/mathlib `IsCoprime` constructors. If the local API is awkward, prove the raw and divided factor lemmas through `Int.gcd`/`natAbs` instead, but keep their signatures unchanged.

## Lemmas 8-9: exact scale killing

This is the exact primitive step requested. It uses only:

* `EB*X = EA*C`,
* `Y = n*C`,
* factor coprimality (`IsCoprime EA EB`, or quotient coprimality),
* `IsCoprime X Y`,
* positivity to rule out scale `-1`.

### Raw scale kill

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n
private abbrev EC (m n : ℤ) : ℤ := 2 * m * n - n ^ 2
private abbrev EZ (m n : ℤ) : ℤ := m ^ 2 - m * n + n ^ 2

private theorem eisenstein_scale_kill_raw
    {X Y Z m n C : ℤ}
    (hXY : IsCoprime X Y)
    (hnpos : 0 < n)
    (hYpos : 0 < Y)
    (hEBpos : 0 < EB m n)
    (hEAEB : IsCoprime (EA m n) (EB m n))
    (hZeq : EB m n * Z = EZ m n * C)
    (hXeq : EB m n * X = EA m n * C)
    (hYC : Y = n * C) :
    C = EB m n ∧ X = EA m n ∧ Y = EC m n ∧ Z = EZ m n := by
  have hEBne : EB m n ≠ 0 := ne_of_gt hEBpos
  have hCpos : 0 < C := by
    have hmul : 0 < n * C := by simpa [hYC] using hYpos
    exact pos_of_mul_pos_left hmul (le_of_lt hnpos)

  -- Euclid: `EB ∣ C` from `EB*X = EA*C` and `IsCoprime EA EB`.
  have hEBdvdC : EB m n ∣ C := by
    have hdiv : EB m n ∣ EA m n * C := ⟨X, hXeq.symm⟩
    -- Product orientation may require the right/left variant plus `simpa [mul_comm]`.
    exact hEAEB.symm.dvd_of_dvd_mul_left hdiv
  rcases hEBdvdC with ⟨k, hC⟩

  have hkpos : 0 < k := by
    have hmul : 0 < EB m n * k := by simpa [hC] using hCpos
    exact pos_of_mul_pos_left hmul (le_of_lt hEBpos)

  -- Cancel the nonzero `EB`: `X = EA*k`.
  have hXk : X = EA m n * k := by
    apply mul_left_cancel₀ hEBne
    calc
      EB m n * X = EA m n * C := hXeq
      _ = EA m n * (EB m n * k) := by rw [hC]
      _ = EB m n * (EA m n * k) := by ring

  have hYk : Y = (n * EB m n) * k := by
    rw [hYC, hC]
    ring

  have hkdvdX : k ∣ X := ⟨EA m n, by rw [hXk]; ring⟩
  have hkdvdY : k ∣ Y := ⟨n * EB m n, by rw [hYk]; ring⟩

  have hkunit : IsUnit k := hXY.isUnit_of_dvd hkdvdX hkdvdY
  have hk : k = 1 := by
    rcases Int.isUnit_iff.mp hkunit with hk | hk
    · exact hk
    · omega

  have hCraw : C = EB m n := by
    rw [hC, hk]
    ring
  have hXraw : X = EA m n := by
    rw [hXk, hk]
    ring
  have hYraw : Y = EC m n := by
    rw [hYk, hk]
    rw [eisenstein_EC_eq_n_mul_EB]
    ring
  have hZraw : Z = EZ m n := by
    apply mul_left_cancel₀ hEBne
    calc
      EB m n * Z = EZ m n * C := hZeq
      _ = EZ m n * EB m n := by rw [hCraw]
      _ = EB m n * EZ m n := by ring

  exact ⟨hCraw, hXraw, hYraw, hZraw⟩

end MazurProof.RationalPointsN12
```

Raw scale-kill equation chain, stripped down:

```text
EB*X = EA*C, IsCoprime EA EB
=> EB ∣ C
=> C = EB*k
=> X = EA*k                         -- cancel EB in EB*X = EA*(EB*k)
Y = n*C = n*EB*k
=> k ∣ X and k ∣ Y
IsCoprime X Y => IsUnit k
0 < k => k = 1
=> C=EB, X=EA, Y=n*EB=EC, Z=EZ
```

### Divided scale kill

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n
private abbrev EC (m n : ℤ) : ℤ := 2 * m * n - n ^ 2
private abbrev EZ (m n : ℤ) : ℤ := m ^ 2 - m * n + n ^ 2

private theorem eisenstein_scale_kill_divided
    {X Y Z m n C EA' EB' : ℤ}
    (hXY : IsCoprime X Y)
    (hnpos : 0 < n)
    (hYpos : 0 < Y)
    (hEA3 : EA m n = 3 * EA')
    (hEB3 : EB m n = 3 * EB')
    (hEB'pos : 0 < EB')
    (hEAEB' : IsCoprime EA' EB')
    (hZeq : EB m n * Z = EZ m n * C)
    (hXeq : EB m n * X = EA m n * C)
    (hYC : Y = n * C) :
    C = EB' ∧ 3 * X = EA m n ∧ 3 * Y = EC m n ∧ 3 * Z = EZ m n := by
  have h3ne : (3 : ℤ) ≠ 0 := by norm_num
  have hEB'ne : EB' ≠ 0 := ne_of_gt hEB'pos
  have hCpos : 0 < C := by
    have hmul : 0 < n * C := by simpa [hYC] using hYpos
    exact pos_of_mul_pos_left hmul (le_of_lt hnpos)

  -- First divide the equation by the known common factor `3`.
  have hXeq' : EB' * X = EA' * C := by
    apply mul_left_cancel₀ h3ne
    calc
      (3 : ℤ) * (EB' * X) = (3 * EB') * X := by ring
      _ = EB m n * X := by rw [← hEB3]
      _ = EA m n * C := hXeq
      _ = (3 * EA') * C := by rw [hEA3]
      _ = 3 * (EA' * C) := by ring

  -- Euclid: `EB' ∣ C` from `EB'*X = EA'*C` and `IsCoprime EA' EB'`.
  have hEB'dvdC : EB' ∣ C := by
    have hdiv : EB' ∣ EA' * C := ⟨X, hXeq'.symm⟩
    exact hEAEB'.symm.dvd_of_dvd_mul_left hdiv
  rcases hEB'dvdC with ⟨k, hC⟩

  have hkpos : 0 < k := by
    have hmul : 0 < EB' * k := by simpa [hC] using hCpos
    exact pos_of_mul_pos_left hmul (le_of_lt hEB'pos)

  have hXk : X = EA' * k := by
    apply mul_left_cancel₀ hEB'ne
    calc
      EB' * X = EA' * C := hXeq'
      _ = EA' * (EB' * k) := by rw [hC]
      _ = EB' * (EA' * k) := by ring

  have hYk : Y = (n * EB') * k := by
    rw [hYC, hC]
    ring

  have hkdvdX : k ∣ X := ⟨EA', by rw [hXk]; ring⟩
  have hkdvdY : k ∣ Y := ⟨n * EB', by rw [hYk]; ring⟩

  have hkunit : IsUnit k := hXY.isUnit_of_dvd hkdvdX hkdvdY
  have hk : k = 1 := by
    rcases Int.isUnit_iff.mp hkunit with hk | hk
    · exact hk
    · omega

  have hCdiv : C = EB' := by
    rw [hC, hk]
    ring
  have h3X : 3 * X = EA m n := by
    rw [hXk, hk, hEA3]
    ring
  have h3Y : 3 * Y = EC m n := by
    rw [hYk, hk]
    calc
      3 * (n * EB') = n * (3 * EB') := by ring
      _ = n * EB m n := by rw [← hEB3]
      _ = EC m n := by
        rw [eisenstein_EC_eq_n_mul_EB]
  have h3Z : 3 * Z = EZ m n := by
    apply mul_left_cancel₀ hEB'ne
    calc
      EB' * (3 * Z) = (3 * EB') * Z := by ring
      _ = EB m n * Z := by rw [← hEB3]
      _ = EZ m n * C := hZeq
      _ = EZ m n * EB' := by rw [hCdiv]
      _ = EB' * EZ m n := by ring

  exact ⟨hCdiv, h3X, h3Y, h3Z⟩

end MazurProof.RationalPointsN12
```

Divided scale-kill equation chain:

```text
EA = 3*EA', EB = 3*EB'
EB*X = EA*C
=> 3*EB'*X = 3*EA'*C
=> EB'*X = EA'*C
IsCoprime EA' EB' => EB' ∣ C
=> C = EB'*k
=> X = EA'*k, Y = n*EB'*k
=> k ∣ X and k ∣ Y
IsCoprime X Y => IsUnit k
0 < k => k = 1
=> C=EB', 3X=EA, 3Y=n*EB=EC, 3Z=EZ
```

## Final assembly theorem skeleton

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n
private abbrev EC (m n : ℤ) : ℤ := 2 * m * n - n ^ 2
private abbrev EZ (m n : ℤ) : ℤ := m ^ 2 - m * n + n ^ 2

-- Replace argument lists to match the already compiled local lemmas.
theorem EisensteinTriplePrimitiveFullParamStatement_proof :
    EisensteinTriplePrimitiveFullParamStatement := by
  intro X Y Z hXpos hYpos hZpos hXY htri

  let m : ℤ := eisenstein_m X Y Z
  let n : ℤ := eisenstein_n X Y Z

  have hmn_pack : 0 < n ∧ n < m ∧ IsCoprime m n := by
    simpa [m, n] using
      (eisenstein_mn_pos_coprime (X:=X) (Y:=Y) (Z:=Z)
        hXpos hYpos hZpos hXY htri)
  rcases hmn_pack with ⟨hnpos, hnm, hmn⟩

  have hcross : m * Y = n * (Z + X) := by
    simpa [m, n] using
      (eisenstein_slope_cross (X:=X) (Y:=Y) (Z:=Z)
        hXpos hYpos hZpos hXY htri)

  obtain ⟨C, hYC, hZXC, hCpos⟩ :=
    eisenstein_C_of_cross (X:=X) (Y:=Y) (Z:=Z) (m:=m) (n:=n)
      hnpos hmn hYpos hcross

  have hEBpos : 0 < EB m n := eisenstein_EB_pos hnpos hnm

  obtain ⟨hZeq, hXeq, hYeqEB⟩ :=
    eisenstein_core_identities (X:=X) (Y:=Y) (Z:=Z) (m:=m) (n:=n) (C:=C)
      htri hYC hZXC (ne_of_gt hCpos)

  by_cases h3 : (3 : ℤ) ∣ m + n
  · obtain ⟨EA', EB', hEA3, hEB3, hEB'pos, hEAEB'⟩ :=
      eisenstein_factor_divided (m:=m) (n:=n) hmn hEBpos h3

    obtain ⟨hC, h3X, h3Y, h3Z⟩ :=
      eisenstein_scale_kill_divided
        (X:=X) (Y:=Y) (Z:=Z) (m:=m) (n:=n) (C:=C) (EA':=EA') (EB':=EB')
        hXY hnpos hYpos hEA3 hEB3 hEB'pos hEAEB' hZeq hXeq hYC

    refine ⟨m, n, ?_⟩
    -- Match this to the actual `EisensteinFullParam` definition.
    -- Expected divided branch:
    --   `3 ∣ m+n`, `3Z=EZ`, and left orientation `3X=EA`, `3Y=EC`.
    unfold EisensteinFullParam
    right
    refine ⟨h3, h3Z, ?_⟩
    left
    exact ⟨h3X, h3Y⟩

  · have hEAEB : IsCoprime (EA m n) (EB m n) :=
      eisenstein_factor_raw (m:=m) (n:=n) hmn h3

    obtain ⟨hC, hXraw, hYraw, hZraw⟩ :=
      eisenstein_scale_kill_raw
        (X:=X) (Y:=Y) (Z:=Z) (m:=m) (n:=n) (C:=C)
        hXY hnpos hYpos hEBpos hEAEB hZeq hXeq hYC

    refine ⟨m, n, ?_⟩
    -- Expected raw branch:
    --   `¬3 ∣ m+n`, `Z=EZ`, and left orientation `X=EA`, `Y=EC`.
    unfold EisensteinFullParam
    left
    refine ⟨h3, hZraw, ?_⟩
    left
    exact ⟨hXraw, hYraw⟩

end MazurProof.RationalPointsN12
```

If the existing frontier is named exactly as in the prompt:

```lean
-- Replace the statement stub by:
theorem EisensteinTriplePrimitiveFullParamStatement :
    EisensteinTriplePrimitiveFullParamStatement := by
  exact EisensteinTriplePrimitiveFullParamStatement_proof
```

If Lean rejects theorem/value name shadowing, rename the `def` to the existing proposition name and call the proof theorem something like:

```lean
theorem eisensteinTriplePrimitiveFullParam :
    EisensteinTriplePrimitiveFullParamStatement := by
  -- assembly above
```

## API checklist for the remaining non-algebra blocks

Use these local searches if the exact method names differ:

```text
# IsCoprime Euclid
IsCoprime.dvd_of_dvd_mul_left
IsCoprime.dvd_of_dvd_mul_right

# common divisor is a unit
IsCoprime.isUnit_of_dvd

# integer units
Int.isUnit_iff

# coprime inherited by divisors
IsCoprime.isCoprime_of_dvd_right
IsCoprime.isCoprime_of_dvd_left

# powers/products of coprime values
IsCoprime.mul_left
IsCoprime.mul_right
IsCoprime.pow_left
IsCoprime.pow_right
```

The highest-leverage exact proof to write first is `eisenstein_scale_kill_raw`. Once that compiles, `eisenstein_scale_kill_divided` is the same proof after cancelling the explicit factor `3`.
