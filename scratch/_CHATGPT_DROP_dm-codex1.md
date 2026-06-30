# Q2627 (dm-codex1): assembly theorem for `PrimitiveCenteredToEulerSquarePair`

Target file: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`  
Namespace assumed from the previous drop: `MazurProof.RationalPointsN12`

This is the Lean-facing assembly layer for the primitive centered AP big triple.  It uses the checked names exactly in the big-triple coordinates:

```lean
primitiveCentered_big_pyth_triple S :
  PythagoreanTriple
    (primitiveCenteredRootProduct S)
    (16 * S.N ^ 2)
    (S.X ^ 2 - 20 * S.N ^ 2)

primitiveCentered_big_triple_coprime S :
  Int.gcd (primitiveCenteredRootProduct S) (16 * S.N ^ 2) = 1

primitiveCenteredRootProduct_mod_two S :
  primitiveCenteredRootProduct S % 2 = 1

primitiveCentered_big_hyp_pos S :
  0 < S.X ^ 2 - 20 * S.N ^ 2
```

The important correction versus my earlier Q2623 drop is that I do **not** introduce synthetic `S.O`/`S.Z` fields.  In the classification output below, the local name `hHyp` is the equation

```lean
S.X ^ 2 - 20 * S.N ^ 2 = m ^ 2 + n ^ 2
```

and the center-square cofactor equation is proved as

```lean
S.X ^ 2 = (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2)
```

from `hHyp`, `S.N = A * D`, and the split.

The only two serious residual theorem interfaces are the requested ones:

1. `coprime_product_eq_eight_square_split_int`
2. `euler_cofactors_are_squares_of_center_square`

The `Even S.N` fact is shown below as a small generic odd-adjacent-roots/gap lemma.  In the final assembly theorem I recommend passing `hNeven : Even S.N` into the payload theorem, then using the local already-available root/gap names to discharge it in the no-extra-argument wrapper.  If your file already has a wrapper, e.g. `primitiveCentered_N_even S`, just use that one-line proof.

---

## Code skeleton

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-!
Residual interface 1.

This is the only place where the coprime product

  m * n = 8 * N ^ 2

is split.  The `Even N` input is what forces the square cofactor `A` to be even
rather than merely integral.
-/
theorem coprime_product_eq_eight_square_split_int
    {N m n : ℤ}
    (hNpos : 0 < N)
    (hNeven : Even N)
    (hmpos : 0 < m) (hnpos : 0 < n)
    (hmn : m * n = 8 * N ^ 2)
    (hmn_coprime : Int.gcd m n = 1)
    (hparity :
      (m % 2 = 0 ∧ n % 2 = 1) ∨
      (m % 2 = 1 ∧ n % 2 = 0)) :
    ∃ A D : ℤ,
      0 < A ∧ 0 < D ∧
      Even A ∧ Odd D ∧ IsCoprime A D ∧
      N = A * D ∧
      ((m = 8 * A ^ 2 ∧ n = D ^ 2) ∨
       (m = D ^ 2 ∧ n = 8 * A ^ 2)) := by
  -- residual 1
  sorry

/-!
Residual interface 2.

If this theorem already exists in the file, do not redeclare it; keep only the
application site in `PrimitiveCenteredToEulerSquarePair_payload`.
-/
theorem euler_cofactors_are_squares_of_center_square
    (S : PrimitiveCenteredFourSqAP) {A D : ℤ}
    (hDodd : Odd D)
    (hAD : IsCoprime A D)
    (hcenter :
      S.X ^ 2 =
        (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2)) :
    ∃ B C : ℤ,
      B ^ 2 = 16 * A ^ 2 + D ^ 2 ∧
      C ^ 2 = 4 * A ^ 2 + D ^ 2 := by
  -- residual 2, already checked per Q2627
  sorry

/-- Divide the classified even-leg equation by `2`. -/
private lemma q2627_mn_eq_eight_square
    {N m n : ℤ}
    (h : 16 * N ^ 2 = 2 * m * n) :
    m * n = 8 * N ^ 2 := by
  have h2 : 2 * (m * n) = 2 * (8 * N ^ 2) := by
    calc
      2 * (m * n) = 2 * m * n := by ring
      _ = 16 * N ^ 2 := by rw [← h]
      _ = 2 * (8 * N ^ 2) := by ring
  exact (mul_left_inj' (show (2 : ℤ) ≠ 0 by norm_num)).mp h2

/--
The classified even leg is positive, hence `m*n` is positive; with `0 ≤ m`
from `coprime_classification'`, both parameters are positive.
-/
private lemma q2627_params_positive
    {N m n : ℤ}
    (hNpos : 0 < N)
    (hleg : 16 * N ^ 2 = 2 * m * n)
    (hm_nonneg : 0 ≤ m) :
    0 < m ∧ 0 < n := by
  have hBigLegPos : 0 < 16 * N ^ 2 := by
    have hNne : N ≠ 0 := ne_of_gt hNpos
    have hsq : 0 < N ^ 2 := sq_pos_of_ne_zero hNne
    nlinarith

  have hmn_pos : 0 < m * n := by
    have h2mn_pos : 0 < 2 * (m * n) := by
      calc
        0 < 16 * N ^ 2 := hBigLegPos
        _ = 2 * (m * n) := by
          calc
            16 * N ^ 2 = 2 * m * n := hleg
            _ = 2 * (m * n) := by ring
    nlinarith

  have hmpos : 0 < m := by
    by_contra hm_not_pos
    have hm_nonpos : m ≤ 0 := le_of_not_gt hm_not_pos
    have hm0 : m = 0 := le_antisymm hm_nonpos hm_nonneg
    rw [hm0] at hmn_pos
    norm_num at hmn_pos

  have hnpos : 0 < n := by
    by_contra hn_not_pos
    have hn_nonpos : n ≤ 0 := le_of_not_gt hn_not_pos
    have hmn_nonpos : m * n ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hm_nonneg hn_nonpos
    exact (not_le_of_gt hmn_pos) hmn_nonpos

  exact ⟨hmpos, hnpos⟩

/--
Generic parity lemma for the `Even S.N` adapter.

Use this with any adjacent roots `p,q` whose squares differ by `4*N`.  Odd
squares are congruent modulo `8`, so `8 ∣ q^2 - p^2 = 4*N`, hence `Even N`.
-/
private lemma q2627_even_of_odd_square_gap
    {p q N : ℤ}
    (hp : Odd p) (hq : Odd q)
    (hgap : q ^ 2 - p ^ 2 = 4 * N) :
    Even N := by
  rcases hp with ⟨u, rfl⟩
  rcases hq with ⟨v, rfl⟩
  have h8dvd :
      (8 : ℤ) ∣ (2 * v + 1) ^ 2 - (2 * u + 1) ^ 2 := by
    refine ⟨(v - u) * (v + u + 1), ?_⟩
    ring
  rcases h8dvd with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  nlinarith [hgap, hk]

/-
Exact `Even S.N` adapter statement, if no wrapper is already present:

theorem primitiveCentered_N_even (S : PrimitiveCenteredFourSqAP) : Even S.N := by
  -- Instantiate `q2627_even_of_odd_square_gap` with the adjacent root names
  -- already in this file.  Schematic shape:
  --
  -- exact q2627_even_of_odd_square_gap
  --   (p := <left adjacent root>)
  --   (q := <right adjacent root>)
  --   (N := S.N)
  --   (<left root odd, from `primitiveCenteredRootProduct_mod_two S`>)
  --   (<right root odd, from `primitiveCenteredRootProduct_mod_two S`>)
  --   (<adjacent gap: right^2 - left^2 = 4 * S.N>)
-/

/-- `Z = m^2+n^2` after the split when `m = 8*A^2`, `n = D^2`. -/
private lemma q2627_hyp_eq_split_left
    {X N A D m n : ℤ}
    (hZ : X ^ 2 - 20 * N ^ 2 = m ^ 2 + n ^ 2)
    (hm : m = 8 * A ^ 2)
    (hn : n = D ^ 2) :
    X ^ 2 - 20 * N ^ 2 = 64 * A ^ 4 + D ^ 4 := by
  rw [hZ, hm, hn]
  ring

/-- `Z = m^2+n^2` after the split when `m = D^2`, `n = 8*A^2`. -/
private lemma q2627_hyp_eq_split_right
    {X N A D m n : ℤ}
    (hZ : X ^ 2 - 20 * N ^ 2 = m ^ 2 + n ^ 2)
    (hm : m = D ^ 2)
    (hn : n = 8 * A ^ 2) :
    X ^ 2 - 20 * N ^ 2 = 64 * A ^ 4 + D ^ 4 := by
  rw [hZ, hm, hn]
  ring

/--
Center cofactor product.

This is the requested non-residual algebra step: from

  X^2 - 20*N^2 = 64*A^4 + D^4
  N = A*D

prove

  X^2 = (16*A^2 + D^2) * (4*A^2 + D^2).
-/
private lemma q2627_center_cofactor_product
    {X N A D : ℤ}
    (hZAD : X ^ 2 - 20 * N ^ 2 = 64 * A ^ 4 + D ^ 4)
    (hNAD : N = A * D) :
    X ^ 2 =
      (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2) := by
  calc
    X ^ 2 = (X ^ 2 - 20 * N ^ 2) + 20 * N ^ 2 := by ring
    _ = (64 * A ^ 4 + D ^ 4) + 20 * (A * D) ^ 2 := by
      rw [hZAD, hNAD]
    _ = (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2) := by
      ring

/--
Field-name-independent payload theorem.

This is the exact assembly theorem I would add first.  It applies
`PythagoreanTriple.coprime_classification'` to the checked primitive centered
big triple, performs all bookkeeping algebra, and leaves only the two residual
interfaces above.

`hNpos` should be supplied by the positivity field/lemma already attached to a
`PrimitiveCenteredFourSqAP`.  `hNeven` is supplied either by an existing wrapper
such as `primitiveCentered_N_even S`, or by instantiating
`q2627_even_of_odd_square_gap` with the local adjacent root/gap names.
-/
theorem PrimitiveCenteredToEulerSquarePair_payload
    (S : PrimitiveCenteredFourSqAP)
    (hNpos : 0 < S.N)
    (hNeven : Even S.N) :
    ∃ A D B C : ℤ,
      0 < A ∧ 0 < D ∧
      Even A ∧ Odd D ∧ IsCoprime A D ∧
      B ^ 2 = 16 * A ^ 2 + D ^ 2 ∧
      C ^ 2 = 4 * A ^ 2 + D ^ 2 := by
  have hBigTriple :
      PythagoreanTriple
        (primitiveCenteredRootProduct S)
        (16 * S.N ^ 2)
        (S.X ^ 2 - 20 * S.N ^ 2) :=
    primitiveCentered_big_pyth_triple S

  have hBigGcd :
      Int.gcd (primitiveCenteredRootProduct S) (16 * S.N ^ 2) = 1 :=
    primitiveCentered_big_triple_coprime S

  have hRootProductOdd : primitiveCenteredRootProduct S % 2 = 1 :=
    primitiveCenteredRootProduct_mod_two S

  have hHypPos : 0 < S.X ^ 2 - 20 * S.N ^ 2 :=
    primitiveCentered_big_hyp_pos S

  obtain ⟨m, n,
      hRootProduct, hEvenLeg, hHyp,
      hmngcd, hmnParity, hm_nonneg⟩ :=
    PythagoreanTriple.coprime_classification'
      (x := primitiveCenteredRootProduct S)
      (y := 16 * S.N ^ 2)
      (z := S.X ^ 2 - 20 * S.N ^ 2)
      hBigTriple hBigGcd hRootProductOdd hHypPos

  -- From `16*S.N^2 = 2*m*n`, divide by `2`.
  have hmn8 : m * n = 8 * S.N ^ 2 :=
    q2627_mn_eq_eight_square hEvenLeg

  -- From the positive even leg and `0 ≤ m`, get `0 < m` and `0 < n`.
  obtain ⟨hmpos, hnpos⟩ :=
    q2627_params_positive hNpos hEvenLeg hm_nonneg

  -- Split the coprime product.  This is residual 1.
  obtain ⟨A, D,
      hApos, hDpos, hAeven, hDodd, hAD, hNAD, hsplit⟩ :=
    coprime_product_eq_eight_square_split_int
      (N := S.N) (m := m) (n := n)
      hNpos hNeven hmpos hnpos hmn8 hmngcd hmnParity

  -- The hypotenuse equation is symmetric in `m,n`, so either split branch gives
  -- `S.X^2 - 20*S.N^2 = 64*A^4 + D^4`.
  have hZAD :
      S.X ^ 2 - 20 * S.N ^ 2 = 64 * A ^ 4 + D ^ 4 := by
    rcases hsplit with hleft | hright
    · exact q2627_hyp_eq_split_left hHyp hleft.1 hleft.2
    · exact q2627_hyp_eq_split_right hHyp hright.1 hright.2

  -- Center-square cofactor product, fully algebraic.
  have hCenterCofactor :
      S.X ^ 2 =
        (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2) :=
    q2627_center_cofactor_product hZAD hNAD

  -- Extract the two Euler cofactor squares.  This is residual 2 / already checked.
  obtain ⟨B, C, hBsq, hCsq⟩ :=
    euler_cofactors_are_squares_of_center_square
      (S := S) (A := A) (D := D) hDodd hAD hCenterCofactor

  exact ⟨A, D, B, C,
    hApos, hDpos, hAeven, hDodd, hAD, hBsq, hCsq⟩

/--
Record-valued packaging theorem, with `0 < S.N` and `Even S.N` supplied
explicitly.  This avoids guessing the local positivity/evenness wrapper names.
-/
theorem PrimitiveCenteredToEulerSquarePair_of_N_pos_even
    (S : PrimitiveCenteredFourSqAP)
    (hNpos : 0 < S.N)
    (hNeven : Even S.N) :
    EulerSquarePair := by
  obtain ⟨A, D, B, C,
      hApos, hDpos, hAeven, hDodd, hAD, hBsq, hCsq⟩ :=
    PrimitiveCenteredToEulerSquarePair_payload S hNpos hNeven

  -- If `EulerSquarePair` field names differ, this final constructor line is the
  -- only local edit.  The payload theorem above is independent of record names.
  exact
    ⟨A, D, B, C,
      hApos, hDpos, hAeven, hDodd, hAD, hBsq, hCsq⟩

/-
If the intended downstream theorem has no extra arguments, wire it as follows
using the actual local positivity and evenness names:

theorem PrimitiveCenteredToEulerSquarePair
    (S : PrimitiveCenteredFourSqAP) :
    EulerSquarePair := by
  exact PrimitiveCenteredToEulerSquarePair_of_N_pos_even
    S
    (by
      -- replace by the actual field/lemma, e.g. `exact S.hNpos`
      exact <positive_N_fact_for_S>)
    (by
      -- use an existing wrapper if present:
      -- exact primitiveCentered_N_even S
      -- otherwise instantiate `q2627_even_of_odd_square_gap` as described above
      exact <even_N_fact_for_S>)
-/

end MazurProof.RationalPointsN12
```

---

## Why the algebra lines are the desired ones

The classification gives

```lean
hEvenLeg : 16 * S.N ^ 2 = 2 * m * n
hHyp     : S.X ^ 2 - 20 * S.N ^ 2 = m ^ 2 + n ^ 2
hmngcd   : Int.gcd m n = 1
hmnParity : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0)
hm_nonneg : 0 ≤ m
```

`q2627_mn_eq_eight_square` proves

```lean
m * n = 8 * S.N ^ 2
```

by multiplying the target by `2` and canceling the nonzero integer `2`.

`q2627_params_positive` proves both parameter positivities from `0 < S.N`, `hEvenLeg`, and `0 ≤ m`: first `0 < 16*S.N^2`, then `0 < 2*(m*n)`, then `0 < m*n`; `m = 0` contradicts this, and `n ≤ 0` contradicts it via `mul_nonpos_of_nonneg_of_nonpos`.

After residual 1 gives either

```lean
m = 8 * A ^ 2 ∧ n = D ^ 2
```

or

```lean
m = D ^ 2 ∧ n = 8 * A ^ 2
```

the symmetric square calculation gives

```lean
S.X ^ 2 - 20 * S.N ^ 2 = 64 * A ^ 4 + D ^ 4
```

and, using `S.N = A * D`, `q2627_center_cofactor_product` proves

```lean
S.X ^ 2 = (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2)
```

which is exactly the input needed by `euler_cofactors_are_squares_of_center_square` to produce the `B,C` fields for `EulerSquarePair`.
