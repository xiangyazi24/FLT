```lean
theorem primitiveCentered_gap_pq (S : PrimitiveCenteredFourSqAP) :
    S.q ^ 2 - S.p ^ 2 = 4 * S.N := by
  simpa using S.hpq

theorem primitiveCentered_gap_qr (S : PrimitiveCenteredFourSqAP) :
    S.r ^ 2 - S.q ^ 2 = 4 * S.N := by
  simpa using S.hqr

theorem primitiveCentered_gap_rs (S : PrimitiveCenteredFourSqAP) :
    S.s ^ 2 - S.r ^ 2 = 4 * S.N := by
  simpa using S.hrs

theorem primitiveCentered_three_left (S : PrimitiveCenteredFourSqAP) :
    S.p ^ 2 + S.r ^ 2 = 2 * S.q ^ 2 := by
  nlinarith [primitiveCentered_gap_pq S, primitiveCentered_gap_qr S]

theorem primitiveCentered_three_right (S : PrimitiveCenteredFourSqAP) :
    S.q ^ 2 + S.s ^ 2 = 2 * S.r ^ 2 := by
  nlinarith [primitiveCentered_gap_qr S, primitiveCentered_gap_rs S]

theorem primitiveCentered_outer_inner_sum (S : PrimitiveCenteredFourSqAP) :
    S.p ^ 2 + S.s ^ 2 = S.q ^ 2 + S.r ^ 2 := by
  nlinarith [primitiveCentered_gap_pq S, primitiveCentered_gap_rs S]

theorem primitiveCentered_halfsum_left_num (S : PrimitiveCenteredFourSqAP) :
    (S.r - S.p) ^ 2 + (S.r + S.p) ^ 2 = (2 * S.q) ^ 2 := by
  calc
    (S.r - S.p) ^ 2 + (S.r + S.p) ^ 2 = 2 * S.p ^ 2 + 2 * S.r ^ 2 := by
      ring
    _ = (2 * S.q) ^ 2 := by
      nlinarith [primitiveCentered_three_left S]

theorem primitiveCentered_halfsum_right_num (S : PrimitiveCenteredFourSqAP) :
    (S.s - S.q) ^ 2 + (S.s + S.q) ^ 2 = (2 * S.r) ^ 2 := by
  calc
    (S.s - S.q) ^ 2 + (S.s + S.q) ^ 2 = 2 * S.q ^ 2 + 2 * S.s ^ 2 := by
      ring
    _ = (2 * S.r) ^ 2 := by
      nlinarith [primitiveCentered_three_right S]

theorem primitiveCentered_halfsum_left_area_num (S : PrimitiveCenteredFourSqAP) :
    (S.r - S.p) * (S.r + S.p) = 8 * S.N := by
  calc
    (S.r - S.p) * (S.r + S.p) = S.r ^ 2 - S.p ^ 2 := by
      ring
    _ = 8 * S.N := by
      nlinarith [primitiveCentered_gap_pq S, primitiveCentered_gap_qr S]

theorem primitiveCentered_halfsum_right_area_num (S : PrimitiveCenteredFourSqAP) :
    (S.s - S.q) * (S.s + S.q) = 8 * S.N := by
  calc
    (S.s - S.q) * (S.s + S.q) = S.s ^ 2 - S.q ^ 2 := by
      ring
    _ = 8 * S.N := by
      nlinarith [primitiveCentered_gap_qr S, primitiveCentered_gap_rs S]

theorem primitiveCentered_q4_pyth (S : PrimitiveCenteredFourSqAP) :
    S.q ^ 4 = (S.p * S.r) ^ 2 + (4 * S.N) ^ 2 := by
  have hp : S.p ^ 2 = S.q ^ 2 - 4 * S.N := by
    nlinarith [primitiveCentered_gap_pq S]
  have hr : S.r ^ 2 = S.q ^ 2 + 4 * S.N := by
    nlinarith [primitiveCentered_gap_qr S]
  calc
    S.q ^ 4 = (S.q ^ 2 - 4 * S.N) * (S.q ^ 2 + 4 * S.N) + (4 * S.N) ^ 2 := by
      ring
    _ = S.p ^ 2 * S.r ^ 2 + (4 * S.N) ^ 2 := by
      rw [← hp, ← hr]
    _ = (S.p * S.r) ^ 2 + (4 * S.N) ^ 2 := by
      ring

theorem primitiveCentered_r4_pyth (S : PrimitiveCenteredFourSqAP) :
    S.r ^ 4 = (S.q * S.s) ^ 2 + (4 * S.N) ^ 2 := by
  have hq : S.q ^ 2 = S.r ^ 2 - 4 * S.N := by
    nlinarith [primitiveCentered_gap_qr S]
  have hs : S.s ^ 2 = S.r ^ 2 + 4 * S.N := by
    nlinarith [primitiveCentered_gap_rs S]
  calc
    S.r ^ 4 = (S.r ^ 2 - 4 * S.N) * (S.r ^ 2 + 4 * S.N) + (4 * S.N) ^ 2 := by
      ring
    _ = S.q ^ 2 * S.s ^ 2 + (4 * S.N) ^ 2 := by
      rw [← hq, ← hs]
    _ = (S.q * S.s) ^ 2 + (4 * S.N) ^ 2 := by
      ring
```
