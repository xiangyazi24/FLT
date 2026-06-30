# Q2555 easy `EulerSquarePair` helper layer

I could not fetch `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean` through the connector on either `scratch` or the default branch, so this is keyed to the self-contained structure excerpt in the prompt.  The snippets below use the fields exactly as given:

```lean
structure EulerSquarePair where
  A D B C : ℤ
  hApos : 0 < A
  hDpos : 0 < D
  hDodd : Odd D
  hAeven : Even A
  hADcop : IsCoprime A D
  hBpos : 0 < B
  hCpos : 0 < C
  hB : B ^ 2 = 16 * A ^ 2 + D ^ 2
  hC : C ^ 2 = 4 * A ^ 2 + D ^ 2
```

For the layer requested here, `hADcop` is intentionally unused.  It starts mattering for `centerX_coprime_stepN` and the later factor-gcd lemmas.

## Imports/API

If the file already imports the project’s usual Mathlib/tactic bundle, no new import should be needed.  For a standalone scratch check, this is enough:

```lean
import Mathlib.Tactic
```

The first three helper lemmas use only `mul_pos`, explicit `Even` witnesses, and `ring`.

## Pasteable basic layer

```lean
namespace EulerSquarePair

/-- Center of the reconstructed four-square AP. -/
def centerX (E : EulerSquarePair) : ℤ :=
  E.B * E.C

/-- Step parameter of the reconstructed four-square AP. -/
def stepN (E : EulerSquarePair) : ℤ :=
  E.A * E.D

/-- Candidate value `X - 6N`. -/
def fm6 (E : EulerSquarePair) : ℤ :=
  E.centerX - 6 * E.stepN

/-- Candidate value `X - 2N`. -/
def fm2 (E : EulerSquarePair) : ℤ :=
  E.centerX - 2 * E.stepN

/-- Candidate value `X + 2N`. -/
def fp2 (E : EulerSquarePair) : ℤ :=
  E.centerX + 2 * E.stepN

/-- Candidate value `X + 6N`. -/
def fp6 (E : EulerSquarePair) : ℤ :=
  E.centerX + 6 * E.stepN

theorem stepN_pos (E : EulerSquarePair) : 0 < E.stepN := by
  simpa [stepN] using mul_pos E.hApos E.hDpos

theorem stepN_even (E : EulerSquarePair) : Even E.stepN := by
  rcases E.hAeven with ⟨a, ha⟩
  refine ⟨a * E.D, ?_⟩
  dsimp [stepN]
  rw [ha]
  ring

theorem centerX_pos (E : EulerSquarePair) : 0 < E.centerX := by
  simpa [centerX] using mul_pos E.hBpos E.hCpos

end EulerSquarePair
```

This is the safest first patch.  It does not depend on parity API theorem names beyond destructing `Even`.

## Optional parity layer for `B_odd` and `C_odd`

The following is still local and does not require changing `EulerSquarePair`.  It avoids relying on lemma names like `Odd.of_pow`, `Odd.add_even`, or `Even.mul_left` by using explicit witnesses.  The only named parity splitter used is `Int.even_or_odd`.  Current Mathlib normally has this; if your snapshot names it differently, replace only that one line.

A useful observation: `hAeven` is **not** actually needed for `B_odd` or `C_odd`.  The terms `16 * A^2` and `4 * A^2` are even for every integer `A`; `hDodd` is the essential hypothesis.

```lean
namespace EulerSquarePair

private theorem even_four_mul_sq (a : ℤ) : Even (4 * a ^ 2) := by
  refine ⟨2 * a ^ 2, ?_⟩
  ring

private theorem even_sixteen_mul_sq (a : ℤ) : Even (16 * a ^ 2) := by
  refine ⟨8 * a ^ 2, ?_⟩
  ring

private theorem odd_sq_of_odd_int {a : ℤ} (ha : Odd a) : Odd (a ^ 2) := by
  rcases ha with ⟨k, hk⟩
  refine ⟨2 * k ^ 2 + 2 * k, ?_⟩
  rw [hk]
  ring

private theorem odd_add_of_even_of_odd {a b : ℤ}
    (ha : Even a) (hb : Odd b) : Odd (a + b) := by
  rcases ha with ⟨u, hu⟩
  rcases hb with ⟨v, hv⟩
  refine ⟨u + v, ?_⟩
  rw [hu, hv]
  ring

private theorem odd_of_sq_odd_int {a : ℤ} (ha : Odd (a ^ 2)) : Odd a := by
  rcases Int.even_or_odd a with ha_even | ha_odd
  · rcases ha_even with ⟨k, hk⟩
    rcases ha with ⟨t, ht⟩
    have hdiv : (2 : ℤ) ∣ 1 := by
      refine ⟨2 * k ^ 2 - t, ?_⟩
      rw [hk] at ht
      ring_nf at ht ⊢
      nlinarith
    norm_num at hdiv
  · exact ha_odd

theorem B_odd (E : EulerSquarePair) : Odd E.B := by
  apply odd_of_sq_odd_int
  have h_even : Even (16 * E.A ^ 2) := even_sixteen_mul_sq E.A
  have h_odd : Odd (E.D ^ 2) := odd_sq_of_odd_int E.hDodd
  have h_rhs : Odd (16 * E.A ^ 2 + E.D ^ 2) :=
    odd_add_of_even_of_odd h_even h_odd
  rw [E.hB]
  exact h_rhs

theorem C_odd (E : EulerSquarePair) : Odd E.C := by
  apply odd_of_sq_odd_int
  have h_even : Even (4 * E.A ^ 2) := even_four_mul_sq E.A
  have h_odd : Odd (E.D ^ 2) := odd_sq_of_odd_int E.hDodd
  have h_rhs : Odd (4 * E.A ^ 2 + E.D ^ 2) :=
    odd_add_of_even_of_odd h_even h_odd
  rw [E.hC]
  exact h_rhs

end EulerSquarePair
```

If `Int.even_or_odd` is unavailable in the exact Mathlib snapshot, keep the first basic layer and postpone `B_odd`/`C_odd`; the target statements are still correct:

```lean
theorem B_odd (E : EulerSquarePair) : Odd E.B := by
  -- `B^2 = even + odd`, so `B^2` is odd, hence `B` is odd.
  -- Needs the local replacement for `odd_of_sq_odd_int`.
  -- Do not use `hAeven`; it is unnecessary here.
  -- complete after locating the local parity-split lemma.
  admit

theorem C_odd (E : EulerSquarePair) : Odd E.C := by
  -- `C^2 = even + odd`, so `C^2` is odd, hence `C` is odd.
  -- Needs the same local replacement for `odd_of_sq_odd_int`.
  admit
```

Do not paste the last `admit` block into the file; it is only the fallback target if the optional parity code needs API adjustment.

## Suggested next local lemmas after this layer

Once the above compiles, the next no-surprise helpers are:

```lean
namespace EulerSquarePair

theorem centerX_odd (E : EulerSquarePair) : Odd E.centerX := by
  -- after `B_odd` and `C_odd`; use `Odd.mul`, or expand witnesses manually.
  -- target: Odd (E.B * E.C)
  -- proof should be a one-liner if `Odd.mul` is available.
  exact (B_odd E).mul (C_odd E)

theorem fm2_pos_of_fm6_pos (E : EulerSquarePair) (h : 0 < E.fm6) :
    0 < E.fm2 := by
  dsimp [fm2, fm6]
  nlinarith [h, E.stepN_pos]

end EulerSquarePair
```

The real arithmetic frontier begins only after this: `centerX_coprime_stepN`, `three_coprime_centerX`, and the six gcds among `fm6`, `fm2`, `fp2`, `fp6`.
