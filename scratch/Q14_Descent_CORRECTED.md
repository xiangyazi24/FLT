# Q14 obstruction — CORRECTED complete design (Xiang-pasted, authoritative; SUPERSEDES the disc-480 version)

CORRECTION: disc(v²+22v−7) = 22²+28 = 512 = 2⁹ (NOT 480). Quadratic-factor disc squareclass = 2.
Factor-split constant = 128 = 2⁷ (the analogue of 20a4's 48). Quartic descent disc = −7.
Only rational 2-torsion on Q14: z²=v³+22v²−7v = v(v²+22v−7) is (0,0).

## obstruction_Q14 (v z:ℚ)(h:z²=v³+22v²−7v) : v ∈ {-7,0,1}  — port 20a4/N10, do NOT one-shot integer box.
Route: rational pt → v=A/B², z=C/B³ → C²=A(A²+22AB²−7B⁴), gcd(A, A²+22AB²−7B⁴)∣7 (since ≡−7B⁴ mod A)
→ squareclass A = d·M², d∈{1,−1,7,−7} → 4 quartic cases:
  d=1:  Y² = M⁴+22M²N²−7N⁴ = (M²+11N²)² − 128N⁴   → (M²+11N²−Y)(M²+11N²+Y)=128N⁴ → M²=N² → v=1
  d=−7: Y² = −7M⁴+22M²N²+N⁴ = (N²+11M²)² − 128M⁴  → (N²+11M²−Y)(N²+11M²+Y)=128M⁴ → M=0∨M²=N² → v=0∨−7
  d=−1: Y² = −M⁴+22M²N²+7N⁴   → IMPOSSIBLE mod 16 (finite ZMod 16 decide on primitive M,N)
  d=7:  Y² = 7M⁴+22M²N²−N⁴    → IMPOSSIBLE mod 16 (decide)

## Lemma DAG:
- Q14DescentDatum (v z) : d M N Y, d∈{1,-1,7,-7}, N>0, IsCoprime M N, v=d(M/N)², d·Y²=d²M⁴+22dM²N²−7N⁴
- Q14_squareclass_descent (hv:v≠0)(h) : ∃ D, True  ← FIRST lemma to port (N10 denom-normalization, gcd∣7)
- Q14_quartic_d_neg_one_no_solution / Q14_quartic_d_pos_seven_no_solution : False  ← mod-16 `decide` (EASY)
- Q14_quartic_d_one_descent_tail (h) : M²=N²  ← HARD, port N10 fourth_power_split + Nat.strong_induction, constant 128, midpoint M²+11N², use coprime_product_eq_fourth_power
- Q14_quartic_d_neg_seven_descent_tail (h) : M=0∨M²=N²  ← HARD, same tail, midpoint N²+11M², split 128M⁴
- obstruction_Q14 := by_cases v=0; squareclass_descent; rcases d; 4 cases (full proof in paste, nlinarith for the d-division casts)

## VERDICT: NOT harder conceptually than 20a4, but a real descent grind. Cleaner (128=2⁷) and messier (−7 disc).
## decide box is AFTER descent (define finite bad Finset, prove empty by decide) — NOT on unbounded V,Z.
## FIRST DISPATCH: Q14_squareclass_descent (validates constants), then the 2 hard tails (the genuine grind).
