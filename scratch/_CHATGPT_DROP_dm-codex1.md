# Q2623 (dm-codex1): assembly theorem for `PrimitiveCenteredToEulerSquarePair`

Target file: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`  
Namespace: `MazurProof.RationalPointsN12`

This is the assembly layer I would put around the checked lemmas.  The only mathematical gaps left as explicit theorem calls are exactly the two requested residuals:

1. `coprime_product_eq_eight_square_split_int`
2. `euler_cofactors_are_squares_of_center_square`

Everything else is bookkeeping/algebra around `PythagoreanTriple.coprime_classification'`.

The important point is that `PythagoreanTriple.coprime_classification'` has this shape in Mathlib:

```lean
PythagoreanTriple.coprime_classification'
  (h : PythagoreanTriple x y z)
  (h_coprime : x.gcd y = 1)
  (h_parity : x % 2 = 1)
  (h_pos : 0 < z) :
  ∃ m n : ℤ,
    x = m ^ 2 - n ^ 2 ∧
    y = 2 * m * n ∧
    z = m ^ 2 + n ^ 2 ∧
    m.gcd n = 1 ∧
    ((m % 2 = 0 ∧ n % 2 = 1) ∨
     (m % 2 = 1 ∧ n % 2 = 0)) ∧
    0 ≤ m
```

So for the big triple

```lean
primitiveCentered_big_pyth_triple S :
  PythagoreanTriple S.O (16 * S.N ^ 2) S.Z
```

we get

```lean
S.O = m ^ 2 - n ^ 2
16 * S.N ^ 2 = 2 * m * n
S.Z = m ^ 2 + n ^ 2
m.gcd n = 1
parity alternative for m,n
0 ≤ m
```

The assembly then derives `m * n = 8 * S.N ^ 2`, proves `0 < m` and `0 < n`, applies the split residual, proves the Euler cofactor product identity, and finally extracts the two cofactor squares.

---

## Code skeleton

The following is written so that all non-residual algebra is explicit.  If the local `EulerSquarePair` record uses slightly different field names, only the final record literal needs editing; the payload theorem immediately above it is field-name independent.

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/--
Residual 1.

This is the integer wrapper around the Nat split from Q2619.  It should be the
only place where the square-factor extraction for

`m * n = 8 * N ^ 2`

is proved.  The result is deliberately symmetric in the last line: depending on
which of `m,n` is the even parameter from the Pythagorean classification, the
`8 * A^2` factor can be on either side.  The downstream cofactor algebra is
symmetric, so the assembly just case-splits on this disjunction.
-/
theorem coprime_product_eq_eight_square_split_int
    {N m n : ℤ}
    (hNpos : 0 < N)
    (hNeven : Even N)
    (hmpos : 0 < m) (hnpos : 0 < n)
    (hmn : m * n = 8 * N ^ 2)
    (hmn_coprime : m.gcd n = 1)
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

/--
Residual 2.

This should use the already-proved cofactor coprimality lemma

`euler_cofactor_coprime :
  Odd D → IsCoprime A D →
  IsCoprime (16 * A ^ 2 + D ^ 2) (4 * A ^ 2 + D ^ 2)`

plus the fact that the left side `S.Z + 20 * S.N^2` is the relevant center
square in the primitive centered AP.
-/
theorem euler_cofactors_are_squares_of_center_square
    (S : PrimitiveCenteredFourSqAP) {A D : ℤ}
    (hDodd : Odd D)
    (hAD : IsCoprime A D)
    (hcenter :
      S.Z + 20 * S.N ^ 2 =
        (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2)) :
    ∃ B C : ℤ,
      B ^ 2 = 16 * A ^ 2 + D ^ 2 ∧
      C ^ 2 = 4 * A ^ 2 + D ^ 2 := by
  -- residual 2
  sorry

/-- Divide the classified even-leg equation by `2`. -/
private lemma q2623_mn_eq_eight_square
    {N m n : ℤ}
    (h : 16 * N ^ 2 = 2 * m * n) :
    m * n = 8 * N ^ 2 := by
  have h2 : 2 * (m * n) = 2 * (8 * N ^ 2) := by
    calc
      2 * (m * n) = 2 * m * n := by ring
      _ = 16 * N ^ 2 := by rw [← h]
      _ = 2 * (8 * N ^ 2) := by ring
  exact (mul_left_inj' (by norm_num : (2 : ℤ) ≠ 0)).mp h2

/-- Positivity of the even leg forces positivity of `m*n`. -/
private lemma q2623_mul_pos_of_big_leg
    {N m n : ℤ}
    (hleg : 0 < 16 * N ^ 2)
    (h : 16 * N ^ 2 = 2 * m * n) :
    0 < m * n := by
  have h2mn : 0 < 2 * (m * n) := by
    calc
      0 < 16 * N ^ 2 := hleg
      _ = 2 * (m * n) := by
        calc
          16 * N ^ 2 = 2 * m * n := h
          _ = 2 * (m * n) := by ring
  nlinarith

/-- From `0 ≤ m` and `0 < m*n`, get `0 < m`. -/
private lemma q2623_m_pos_of_nonneg_of_mul_pos
    {m n : ℤ}
    (hm_nonneg : 0 ≤ m)
    (hmn_pos : 0 < m * n) :
    0 < m := by
  by_contra hm_not_pos
  have hm_nonpos : m ≤ 0 := le_of_not_gt hm_not_pos
  have hm0 : m = 0 := le_antisymm hm_nonpos hm_nonneg
  rw [hm0] at hmn_pos
  norm_num at hmn_pos

/-- From `0 ≤ m` and `0 < m*n`, get `0 < n`. -/
private lemma q2623_n_pos_of_m_nonneg_of_mul_pos
    {m n : ℤ}
    (hm_nonneg : 0 ≤ m)
    (hmn_pos : 0 < m * n) :
    0 < n := by
  by_contra hn_not_pos
  have hn_nonpos : n ≤ 0 := le_of_not_gt hn_not_pos
  have hmn_nonpos : m * n ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hm_nonneg hn_nonpos
  exact (not_le_of_gt hmn_pos) hmn_nonpos

/-- `Z = m^2+n^2` after the split when `m = 8*A^2`, `n = D^2`. -/
private lemma q2623_z_eq_split_left
    {Z A D m n : ℤ}
    (hZ : Z = m ^ 2 + n ^ 2)
    (hm : m = 8 * A ^ 2)
    (hn : n = D ^ 2) :
    Z = 64 * A ^ 4 + D ^ 4 := by
  rw [hZ, hm, hn]
  ring

/-- `Z = m^2+n^2` after the split when `m = D^2`, `n = 8*A^2`. -/
private lemma q2623_z_eq_split_right
    {Z A D m n : ℤ}
    (hZ : Z = m ^ 2 + n ^ 2)
    (hm : m = D ^ 2)
    (hn : n = 8 * A ^ 2) :
    Z = 64 * A ^ 4 + D ^ 4 := by
  rw [hZ, hm, hn]
  ring

/--
The Euler cofactor product identity.

Once the split has produced `Z = 64*A^4 + D^4` and `N = A*D`, the product of
the two Euler cofactors is exactly the center-square expression
`Z + 20*N^2`.
-/
private lemma q2623_center_cofactor_product
    {Z N A D : ℤ}
    (hZAD : Z = 64 * A ^ 4 + D ^ 4)
    (hNAD : N = A * D) :
    Z + 20 * N ^ 2 =
      (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2) := by
  rw [hZAD, hNAD]
  ring

/--
Field-name-independent payload produced by the assembly theorem.

This is often the safest first theorem to add, because it avoids guessing the
constructor order of `EulerSquarePair` while still proving the whole arithmetic
payload needed to build it.
-/
theorem PrimitiveCenteredToEulerSquarePair_payload
    (S : PrimitiveCenteredFourSqAP) :
    ∃ A D B C : ℤ,
      0 < A ∧ 0 < D ∧
      Even A ∧ Odd D ∧ IsCoprime A D ∧
      B ^ 2 = 16 * A ^ 2 + D ^ 2 ∧
      C ^ 2 = 4 * A ^ 2 + D ^ 2 := by
  have hBigTriple : PythagoreanTriple S.O (16 * S.N ^ 2) S.Z :=
    primitiveCentered_big_pyth_triple S
  have hBigGcd : S.O.gcd (16 * S.N ^ 2) = 1 :=
    primitiveCentered_big_triple_coprime S
  have hOddLeg : S.O % 2 = 1 :=
    primitiveCenteredRootProduct_mod_two S
  have hHypPos : 0 < S.Z :=
    primitiveCentered_big_hyp_pos S

  obtain ⟨m, n, hO, hEvenLeg, hZmn, hmngcd, hmnParity, hm_nonneg⟩ :=
    PythagoreanTriple.coprime_classification'
      (x := S.O) (y := 16 * S.N ^ 2) (z := S.Z)
      hBigTriple hBigGcd hOddLeg hHypPos

  -- The classified even-leg equation is exactly `16*N^2 = 2*m*n`.
  have hmn8 : m * n = 8 * S.N ^ 2 :=
    q2623_mn_eq_eight_square hEvenLeg

  -- Positivity of the big even leg; use the existing local lemma if it is
  -- already named.  If not, this closes from the local positive/nonzero field
  -- for `S.N`.
  have hBigLegPos : 0 < 16 * S.N ^ 2 := by
    -- Preferred if already available from Q2622:
    -- exact primitiveCentered_big_leg_pos S
    have hNne : S.N ≠ 0 := by
      -- Replace `S.hNpos` by the local positivity field/lemma if it has a
      -- different name.
      exact ne_of_gt S.hNpos
    nlinarith [sq_pos_of_ne_zero hNne]

  have hmn_pos : 0 < m * n :=
    q2623_mul_pos_of_big_leg hBigLegPos hEvenLeg
  have hmpos : 0 < m :=
    q2623_m_pos_of_nonneg_of_mul_pos hm_nonneg hmn_pos
  have hnpos : 0 < n :=
    q2623_n_pos_of_m_nonneg_of_mul_pos hm_nonneg hmn_pos

  -- The split theorem wants positive/even `N`.  Positivity is structural; the
  -- evenness follows from the checked root-product parity and the AP gap.
  have hNpos : 0 < S.N := S.hNpos
  have hNeven : Even S.N := by
    -- If the parity wrapper has already been named, this should be just:
    -- exact primitiveCentered_N_even S
    --
    -- Otherwise prove it locally from:
    --   * `primitiveCenteredRootProduct_mod_two S`, giving odd roots/root product;
    --   * one adjacent gap, e.g. `primitiveCentered_gap_pq S :
    --       S.q ^ 2 - S.p ^ 2 = 4 * S.N`;
    --   * odd squares are congruent to `1` modulo `8`, so `8 ∣ 4*S.N`.
    exact primitiveCentered_N_even S

  obtain ⟨A, D, hApos, hDpos, hAeven, hDodd, hAD, hNAD, hsplit⟩ :=
    coprime_product_eq_eight_square_split_int
      (N := S.N) (m := m) (n := n)
      hNpos hNeven hmpos hnpos hmn8 hmngcd hmnParity

  -- This is the key post-split algebra.  The disjunction is harmless because
  -- `m^2+n^2` is symmetric.
  have hZAD : S.Z = 64 * A ^ 4 + D ^ 4 := by
    rcases hsplit with hleft | hright
    · exact q2623_z_eq_split_left hZmn hleft.1 hleft.2
    · exact q2623_z_eq_split_right hZmn hright.1 hright.2

  -- Cofactor product for the center-square expression.
  have hCenterCofactor :
      S.Z + 20 * S.N ^ 2 =
        (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2) :=
    q2623_center_cofactor_product hZAD hNAD

  obtain ⟨B, C, hBsq, hCsq⟩ :=
    euler_cofactors_are_squares_of_center_square
      (S := S) (A := A) (D := D) hDodd hAD hCenterCofactor

  exact ⟨A, D, B, C,
    hApos, hDpos, hAeven, hDodd, hAD, hBsq, hCsq⟩

/--
Record-valued wrapper.  Keep this theorem name if downstream code expects
`PrimitiveCenteredToEulerSquarePair` as the constructor of an `EulerSquarePair`.

Only the final record field names may need adjustment to match the local
structure declaration.
-/
theorem PrimitiveCenteredToEulerSquarePair
    (S : PrimitiveCenteredFourSqAP) :
    EulerSquarePair := by
  obtain ⟨A, D, B, C,
    hApos, hDpos, hAeven, hDodd, hAD, hBsq, hCsq⟩ :=
    PrimitiveCenteredToEulerSquarePair_payload S

  exact
    { A := A
      D := D
      B := B
      C := C
      A_pos := hApos
      D_pos := hDpos
      A_even := hAeven
      D_odd := hDodd
      AD_coprime := hAD
      left_square := hBsq
      right_square := hCsq }

end MazurProof.RationalPointsN12
```

---

## Notes for wiring into the current file

The proof intentionally uses the names you listed:

```lean
primitiveCentered_big_pyth_triple
primitiveCentered_big_triple_coprime
primitiveCenteredRootProduct_mod_two
primitiveCentered_big_hyp_pos
```

Two small local-name adapters may be needed, depending on what Q2622 called them:

```lean
primitiveCentered_big_leg_pos S : 0 < 16 * S.N ^ 2
primitiveCentered_N_even S : Even S.N
```

If those wrappers do not yet exist, they are not new mathematical residuals.  `primitiveCentered_big_leg_pos` closes from the positive/nonzero field for `S.N`; `primitiveCentered_N_even` closes from the checked root-product parity plus an adjacent AP gap, as described in the comment in the proof.

The only serious unresolved facts should remain exactly:

```lean
coprime_product_eq_eight_square_split_int
 euler_cofactors_are_squares_of_center_square
```
