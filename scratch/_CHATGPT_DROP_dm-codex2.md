# Q2743 dm-codex2: Lean DAG for `EisensteinTriplePrimitiveFullParamStatement`

Namespace: `MazurProof.RationalPointsN12`.

This audit is keyed to the WIP facts in the prompt. I could not inspect `/Users/huangx/repos/flt-ai` through the GitHub connector.

## Audit verdict

The route is sound if `EisensteinTriple X Y Z` is the minus-sign equation

```lean
X ^ 2 - X * Y + Y ^ 2 = Z ^ 2
```

The identities with `2*m - n` and `m^2 - m*n + n^2` are false for the plus-sign equation.

Hidden false steps to avoid:

1. `common divisors of EA, EB divide 3` is not enough. You need the sharpened raw/divided split.
2. In the divided branch, do not use integer `/`; introduce quotient witnesses from `3 ∣ m+n`.
3. The algebra identity for `Z` needs `C ≠ 0`, obtained from `0<Y`, `0<n`, `Y=n*C`.
4. The primitive step first proves the scale is an integer. Primitive-ness alone does not justify `C / EB`.
5. The slope orientation `m*Y=n*(Z+X)` gives the left `(X,Y)` disjunct; the swapped disjunct is not needed for this path.
6. `(1,1,1)` appears in the divided branch with `(m,n)=(2,1)`, `EB=3`, `C=1`.

## Common notation

Use these helper abbreviations locally above the frontier theorem.

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

| order | theorem | kind | statement/output |
|---:|---|---|---|
| 1 | `eisenstein_EC_eq_n_mul_EB` | pure algebra | `EC m n = n * EB m n` |
| 2 | `eisenstein_EB_pos` | linear arithmetic | `0 < EB m n` from `0<n`, `n<m` |
| 3 | `eisenstein_C_of_cross` | divisibility API | `∃ C, Y=n*C ∧ Z+X=m*C ∧ 0<C` |
| 4 | `eisenstein_core_identities_eq` | pure algebra + cancel `C≠0` | `EB*Z=EZ*C`, `EB*X=EA*C`, `EB*Y=EC*C` |
| 5 | `eisenstein_coprime_m_EB` | divisibility API | `IsCoprime m (EB m n)` |
| 6 | `eisenstein_EA_EB_common_dvd_three` | divisibility API | common divisor of `EA`, `EB` divides `3` |
| 7 | `eisenstein_factor_raw` | divisibility API | `IsCoprime (EA m n) (EB m n)` under `¬3∣m+n` |
| 8 | `eisenstein_factor_divided` | divisibility API | `EA=3EA'`, `EB=3EB'`, `0<EB'`, `IsCoprime EA' EB'` |
| 9 | `eisenstein_scale_kill_raw` | exact scale kill | `C=EB`, `X=EA`, `Y=EC`, `Z=EZ` |
| 10 | `eisenstein_scale_kill_divided` | exact scale kill | `C=EB'`, `3X=EA`, `3Y=EC`, `3Z=EZ` |
| 11 | frontier assembly | constructors | raw or divided `EisensteinFullParam` |

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
    -- If this exact method name is reversed locally, use the right/left variant and normalize products.
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

-- Adapter signature; fill the equation projection according to the local definition.
-- private theorem eisenstein_core_identities
--     {X Y Z m n C : ℤ}
--     (htri : EisensteinTriple X Y Z)
--     (hYC : Y = n * C)
--     (hZXC : Z + X = m * C)
--     (hCne : C ≠ 0) :
--     EB m n * Z = EZ m n * C ∧
--     EB m n * X = EA m n * C ∧
--     EB m n * Y = EC m n * C :=
--   eisenstein_core_identities_eq
--     (by simpa [EisensteinTriple] using htri) hYC hZXC hCne

end MazurProof.RationalPointsN12
```

If the `hprod` factor comes out negated after `ring_nf`, use `C * ((EZ m n * C) - (EB m n * Z)) = 0` and flip the final equality.

## Lemmas 5-8: factor coprimality checklist

These are the divisibility/API lemmas. Keep the signatures exactly as below; implement them using either `IsCoprime` common-divisor criteria or `Int.gcd`/`natAbs`.

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n
private abbrev EC (m n : ℤ) : ℤ := 2 * m * n - n ^ 2
private abbrev EZ (m n : ℤ) : ℤ := m ^ 2 - m * n + n ^ 2

-- theorem signature:
-- private theorem eisenstein_coprime_m_EB {m n : ℤ}
--     (hmn : IsCoprime m n) :
--     IsCoprime m (EB m n)
-- proof:
--   Use Bezout from `hmn`.
--   If `a*m + b*n = 1`, then `(a + 2*b)*m - b*(2*m-n) = 1`.
--   Finish by `unfold EB; ring`.

-- theorem signature:
-- private theorem eisenstein_EA_EB_common_dvd_three
--     {m n d : ℤ}
--     (hmn : IsCoprime m n)
--     (hdEA : d ∣ EA m n)
--     (hdEB : d ∣ EB m n) :
--     d ∣ (3 : ℤ)
-- proof DAG:
--   hd4   : d ∣ 4*m^2 - n^2
--         from `hdEB` multiplied by `(2*m+n)`.
--   hd3m2 : d ∣ 3*m^2
--         from `hd4 - hdEA`.
--   hmEB  : IsCoprime m (EB m n)
--         from `eisenstein_coprime_m_EB hmn`.
--   hmd   : IsCoprime m d
--         because `d ∣ EB m n`.
--   hdm2  : IsCoprime d (m^2)
--         from `hmd` and product/power coprimality.
--   exact hdm2.dvd_of_dvd_mul_right hd3m2

-- theorem signature:
-- private theorem eisenstein_factor_raw
--     {m n : ℤ}
--     (hmn : IsCoprime m n)
--     (h3 : ¬ (3 : ℤ) ∣ m + n) :
--     IsCoprime (EA m n) (EB m n)
-- proof DAG:
--   For any common divisor `d` of `EA` and `EB`, lemma 6 gives `d ∣ 3`.
--   Show `¬ (3 : ℤ) ∣ EB m n`; otherwise
--       2*(m+n) = EB m n + 3*n
--     gives `3 ∣ 2*(m+n)`, hence `3 ∣ m+n` since `IsCoprime (3:ℤ) 2`.
--   Thus a common divisor of `3` and `EB` is a unit.
--   Apply the common-divisor criterion for `IsCoprime (EA m n) (EB m n)`.

-- theorem signature:
-- private theorem eisenstein_factor_divided
--     {m n : ℤ}
--     (hmn : IsCoprime m n)
--     (hEBpos : 0 < EB m n)
--     (h3 : (3 : ℤ) ∣ m + n) :
--     ∃ EA' EB' : ℤ,
--       EA m n = 3 * EA' ∧
--       EB m n = 3 * EB' ∧
--       0 < EB' ∧
--       IsCoprime EA' EB'
-- proof DAG:
--   rcases h3 with ⟨s, hs : m+n = 3*s⟩
--   choose `EA' = (m-n)*s`, `EB' = 2*s-n`.
--   `EA = 3*EA'` by `rw [hs]; unfold EA; ring`.
--   `EB = 3*EB'` by `rw [hs]; unfold EB; ring`.
--   `0<EB'` from `0 < 3*EB'` and `hEBpos`.
--   For quotient coprimality:
--     if `d ∣ EA'` and `d ∣ EB'`, then `3*d ∣ EA` and `3*d ∣ EB`.
--     lemma 6 gives `3*d ∣ 3`; cancel nonzero `3`, so `IsUnit d`.
--     Apply the common-divisor criterion.

end MazurProof.RationalPointsN12
```

## Lemma 9: raw scale-killing step

This is the exact requested scale kill.

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

  have hEBdvdC : EB m n ∣ C := by
    have hdiv : EB m n ∣ EA m n * C := ⟨X, hXeq.symm⟩
    exact hEAEB.symm.dvd_of_dvd_mul_left hdiv
  rcases hEBdvdC with ⟨k, hC⟩

  have hkpos : 0 < k := by
    have hmul : 0 < EB m n * k := by simpa [hC] using hCpos
    exact pos_of_mul_pos_left hmul (le_of_lt hEBpos)

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

  have hCraw : C = EB m n := by rw [hC, hk]; ring
  have hXraw : X = EA m n := by rw [hXk, hk]; ring
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

Stripped raw chain:

```text
EB*X = EA*C, IsCoprime EA EB
=> EB ∣ C
=> C = EB*k
=> X = EA*k                         -- cancel EB
Y = n*C = n*EB*k
=> k ∣ X and k ∣ Y
IsCoprime X Y => IsUnit k
0 < k => k = 1
=> C=EB, X=EA, Y=n*EB=EC, Z=EZ
```

## Lemma 10: divided scale-killing step

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

  have hXeq' : EB' * X = EA' * C := by
    apply mul_left_cancel₀ h3ne
    calc
      (3 : ℤ) * (EB' * X) = (3 * EB') * X := by ring
      _ = EB m n * X := by rw [← hEB3]
      _ = EA m n * C := hXeq
      _ = (3 * EA') * C := by rw [hEA3]
      _ = 3 * (EA' * C) := by ring

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

  have hCdiv : C = EB' := by rw [hC, hk]; ring
  have h3X : 3 * X = EA m n := by rw [hXk, hk, hEA3]; ring
  have h3Y : 3 * Y = EC m n := by
    rw [hYk, hk]
    calc
      3 * (n * EB') = n * (3 * EB') := by ring
      _ = n * EB m n := by rw [← hEB3]
      _ = EC m n := by rw [eisenstein_EC_eq_n_mul_EB]
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

Stripped divided chain:

```text
EA=3EA', EB=3EB'
EB*X=EA*C
=> EB'*X=EA'*C
IsCoprime EA' EB' => EB' ∣ C
=> C=EB'*k
=> X=EA'*k, Y=n*EB'*k
=> k ∣ X and k ∣ Y
IsCoprime X Y => IsUnit k
0 < k => k=1
=> C=EB', 3X=EA, 3Y=n*EB=EC, 3Z=EZ
```

## Frontier assembly skeleton

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n
private abbrev EC (m n : ℤ) : ℤ := 2 * m * n - n ^ 2
private abbrev EZ (m n : ℤ) : ℤ := m ^ 2 - m * n + n ^ 2

theorem eisensteinTriplePrimitiveFullParam_proof :
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

  obtain ⟨hZeq, hXeq, _hYeqEB⟩ :=
    eisenstein_core_identities (X:=X) (Y:=Y) (Z:=Z) (m:=m) (n:=n) (C:=C)
      htri hYC hZXC (ne_of_gt hCpos)

  by_cases h3 : (3 : ℤ) ∣ m + n
  · obtain ⟨EA', EB', hEA3, hEB3, hEB'pos, hEAEB'⟩ :=
      eisenstein_factor_divided (m:=m) (n:=n) hmn hEBpos h3
    obtain ⟨_hC, h3X, h3Y, h3Z⟩ :=
      eisenstein_scale_kill_divided
        (X:=X) (Y:=Y) (Z:=Z) (m:=m) (n:=n) (C:=C) (EA':=EA') (EB':=EB')
        hXY hnpos hYpos hEA3 hEB3 hEB'pos hEAEB' hZeq hXeq hYC
    refine ⟨m, n, ?_⟩
    unfold EisensteinFullParam
    right
    refine ⟨h3, h3Z, ?_⟩
    left
    exact ⟨h3X, h3Y⟩

  · have hEAEB : IsCoprime (EA m n) (EB m n) :=
      eisenstein_factor_raw (m:=m) (n:=n) hmn h3
    obtain ⟨_hC, hXraw, hYraw, hZraw⟩ :=
      eisenstein_scale_kill_raw
        (X:=X) (Y:=Y) (Z:=Z) (m:=m) (n:=n) (C:=C)
        hXY hnpos hYpos hEBpos hEAEB hZeq hXeq hYC
    refine ⟨m, n, ?_⟩
    unfold EisensteinFullParam
    left
    refine ⟨h3, hZraw, ?_⟩
    left
    exact ⟨hXraw, hYraw⟩

end MazurProof.RationalPointsN12
```

Constructor order may need flipping if `EisensteinFullParam` stores divided/raw in the opposite order. The equations should feed the left orientation inside each sector.

## API names to try first

```text
IsCoprime.dvd_of_dvd_mul_left
IsCoprime.dvd_of_dvd_mul_right
IsCoprime.isUnit_of_dvd
Int.isUnit_iff
IsCoprime.isCoprime_of_dvd_right
IsCoprime.isCoprime_of_dvd_left
IsCoprime.mul_left
IsCoprime.mul_right
IsCoprime.pow_left
IsCoprime.pow_right
```

The most important local milestone is compiling `eisenstein_scale_kill_raw`; after that, the divided scale kill is the same proof with the explicit `3` cancellation at the start.
