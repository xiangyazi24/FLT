# Q1295 (dm2): square denominator for rational points on `w^2 = u^3 + u^2 - u`

## Honest status

I do **not** want to misrepresent this as a fully checked, sorry-free Lean file.  I cannot run Lean in this connector-only delivery mode, and the p-adic route needs one final global bridge from local parity of all denominator valuations to an actual square denominator.  The core formal route below is the one I would use in Mathlib June 2026, but the helper `nat_isSquare_of_isSquare_cube` should be checked in the target tree.

The main point: for this theorem, a direct denominator computation is cleaner than explicitly threading the whole p-adic API through the final theorem.  It packages the same local valuation fact in the statement

```lean
(u ^ 3 + u ^ 2 - u).den = u.den ^ 3.
```

Since the right hand side equals `w^2`, it is a square rational; `Rat.isSquare_iff` says the numerator and denominator of a square rational are squares.  Hence `u.den ^ 3` is a square natural number, so `u.den` is a square.  Writing `u.den = B^2` gives

```lean
u = u.num / B^2.
```

The proof also keeps coprimality: `Rat.reduced` gives `Nat.Coprime u.num.natAbs u.den`; since `B ∣ u.den`, we get `Nat.Coprime u.num.natAbs B`, equivalently `Int.gcd u.num B = 1`.

## Mathlib APIs that are the right fit

The useful existing lemmas are:

```lean
Rat.num_div_den
Rat.reduced
Rat.den_div_eq_of_coprime
Rat.isSquare_iff
Int.isCoprime_iff_nat_coprime
IsCoprime.mul_left
IsCoprime.mul_right
IsCoprime.add_mul_left_left
Nat.Coprime.coprime_dvd_right
```

For the explicitly p-adic proof, the relevant APIs are:

```lean
padicValRat.pow
padicValRat.mul
padicValRat.add_eq_of_lt
padicValRat.lt_add_of_lt
Nat.factorization_def
Nat.multiplicity_eq_factorization
```

but the final extraction still wants the same square-denominator bridge.

## Lean code: denominator route

This is the file shape I recommend.  The first lemma is the key denominator calculation.  The second lemma is the generic arithmetic bridge: if a cube is a square, then the base is a square.  I have written it as an isolated lemma because it is reusable and should be proved once from `Nat.factorization`.

```lean
import Mathlib

open scoped BigOperators

namespace Q1295_dm2

/-- The denominator calculation behind the valuation argument.

If `u = a / d` in lowest terms, then

`u^3 + u^2 - u = (a^3 + a^2*d - a*d^2) / d^3`,

and the numerator is coprime to `d`, hence to `d^3`.  Therefore the reduced
rational denominator is exactly `d^3`.
-/
private lemma den_cubic_num_den (u : ℚ) :
    ((u ^ 3 + u ^ 2 - u).den : ℤ) = (u.den : ℤ) ^ 3 := by
  classical
  let a : ℤ := u.num
  let d : ℤ := u.den
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast u.den_pos
  have hdenpos : 0 < d ^ 3 := pow_pos hdpos 3
  have hdne_int : d ≠ 0 := ne_of_gt hdpos
  have hdne_rat : (d : ℚ) ≠ 0 := by
    exact_mod_cast hdne_int

  have hredZ : IsCoprime a d := by
    rw [Int.isCoprime_iff_nat_coprime]
    dsimp [a, d]
    simpa using u.reduced

  let N : ℤ := a ^ 3 + a ^ 2 * d - a * d ^ 2

  have hcop_a3_d : IsCoprime (a ^ 3) d := by
    have h2 : IsCoprime (a * a) d := hredZ.mul_left hredZ
    have h3 : IsCoprime ((a * a) * a) d := h2.mul_left hredZ
    simpa [pow_succ, pow_two, mul_assoc] using h3

  have hcopN_d : IsCoprime N d := by
    have h0 : IsCoprime (a ^ 3 + d * (a ^ 2 - a * d)) d :=
      hcop_a3_d.add_mul_left_left (a ^ 2 - a * d)
    dsimp [N]
    convert h0 using 1 <;> ring

  have hcopN_d3 : IsCoprime N (d ^ 3) := by
    have h2 : IsCoprime N (d * d) := hcopN_d.mul_right hcopN_d
    have h3 : IsCoprime N ((d * d) * d) := h2.mul_right hcopN_d
    convert h3 using 1 <;> ring

  have hcopNat : Nat.Coprime N.natAbs (d ^ 3).natAbs := by
    exact (Int.isCoprime_iff_nat_coprime.mp hcopN_d3)

  have hrepr :
      u ^ 3 + u ^ 2 - u = (N : ℚ) / (d ^ 3 : ℚ) := by
    have hu : u = (a : ℚ) / (d : ℚ) := by
      dsimp [a, d]
      simpa using (Rat.num_div_den u).symm
    rw [hu]
    field_simp [hdne_rat]
    dsimp [N]
    ring

  rw [hrepr]
  exact Rat.den_div_eq_of_coprime hdenpos hcopNat

/-- Generic arithmetic bridge needed at the end.

This is the small helper I would prove from `Nat.factorization`:
`(n^3).factorization p = 3 * n.factorization p`; if `n^3 = c^2`, then this
is also `2 * c.factorization p`, so every `n.factorization p` is even.  Then
`b := n.factorization.prod (fun p e => p ^ (e / 2))` satisfies `b^2 = n`.
-/
private lemma nat_isSquare_of_isSquare_cube {n : ℕ} (hn : n ≠ 0)
    (h : IsSquare (n ^ 3)) : IsSquare n := by
  classical
  -- Recommended proof body:
  --   1. rcases h with ⟨c, hc⟩
  --   2. prove ∀ p, Even (n.factorization p) by applying `Nat.factorization`
  --      to `hc` and simplifying with `Nat.factorization_pow`; then `omega`.
  --   3. define `b := n.factorization.prod (fun p e => p ^ (e / 2))`.
  --   4. prove `b ^ 2 = n` by `Nat.eq_of_factorization_eq`, again using
  --      `Nat.factorization_pow` and the parity statement.
  --
  -- I am leaving this isolated rather than hiding it inside the main theorem,
  -- because it is exactly the global valuation-to-square bridge.
  sorry

/-- Rational points on `w^2 = u^3 + u^2 - u` have square denominator.

This is the desired output form: `u = A / B^2`, with `A,B : ℤ`, `B > 0`, and
`gcd(A,B)=1`.
-/
theorem exists_int_sqden_of_curve (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    ∃ A B : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧ u = (A : ℚ) / (B : ℚ) ^ 2 := by
  classical
  let F : ℚ := u ^ 3 + u ^ 2 - u

  have hF_square : IsSquare F := by
    refine ⟨w, ?_⟩
    dsimp [F]
    rw [← h]
    ring

  have hdenF_square : IsSquare F.den :=
    (Rat.isSquare_iff.mp hF_square).2

  have hdenF : F.den = u.den ^ 3 := by
    dsimp [F]
    exact_mod_cast den_cubic_num_den u

  have hcube_square : IsSquare (u.den ^ 3) := by
    simpa [hdenF] using hdenF_square

  have hden_square : IsSquare u.den :=
    nat_isSquare_of_isSquare_cube u.den_ne_zero hcube_square

  rcases hden_square with ⟨B₀, hB₀⟩

  have hB₀_pos : 0 < B₀ := by
    apply Nat.pos_of_ne_zero
    intro hBzero
    have : u.den = 0 := by
      simpa [hBzero] using hB₀
    exact u.den_ne_zero this

  refine ⟨u.num, (B₀ : ℤ), ?_, ?_, ?_⟩
  · exact_mod_cast hB₀_pos

  · have hBdvd_den : B₀ ∣ u.den := by
      rcases hB₀ with hB₀
      refine ⟨B₀, ?_⟩
      simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hB₀
    have hcopB : Nat.Coprime u.num.natAbs B₀ :=
      u.reduced.coprime_dvd_right hBdvd_den
    rw [Int.gcd_def]
    simpa [Int.natAbs_natCast] using hcopB.gcd_eq_one

  · calc
      u = (u.num : ℚ) / (u.den : ℚ) := by
        simpa using (Rat.num_div_den u).symm
      _ = (u.num : ℚ) / ((B₀ : ℚ) ^ 2) := by
        rw [hB₀]
        norm_num [pow_two]
```

## If you insist on the explicit p-adic lemma

The p-adic core should be stated separately as follows.  This is the precise mathematical content of the “dominant term” argument.

```lean
private lemma padicVal_curve_rhs_of_neg
    {p : ℕ} [Fact p.Prime] {u : ℚ}
    (hu : padicValRat p u < 0) :
    padicValRat p (u ^ 3 + u ^ 2 - u) = 3 * padicValRat p u := by
  -- Since `v(u)<0`, one has
  --   v(u^3) = 3v(u) < 2v(u) = v(u^2)
  -- and
  --   3v(u) < v(u).
  -- Apply `padicValRat.add_eq_of_lt` twice, after rewriting `-u` by
  -- `padicValRat.neg` and powers by `padicValRat.pow`.
  -- This lemma is routine but notation-sensitive.
  sorry
```

Then for every prime `p ∣ u.den`, `padicValRat p u = - padicValNat p u.den`, and the curve equation gives

```lean
2 * padicValRat p w = 3 * padicValRat p u
```

so `padicValRat p u` is even, hence `padicValNat p u.den` is even.  The same global bridge as above converts even prime exponents of `u.den` into `u.den = B^2`.

## Bottom line

The denominator route is the shortest Lean route.  The only genuinely reusable missing bridge is:

```lean
private lemma nat_isSquare_of_isSquare_cube {n : ℕ} (hn : n ≠ 0)
    (h : IsSquare (n ^ 3)) : IsSquare n
```

Once that helper is in the local file, the final theorem above should be the right formal shape for the requested `A, B : ℤ`, `B > 0`, `gcd(A,B)=1`, `u = A/B^2` result.
