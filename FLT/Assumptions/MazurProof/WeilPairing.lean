import Mathlib
import FLT.Assumptions.MazurProof.Axioms

/-!
# Weil Pairing: Simplified via Determinant of Galois Representation

## Main result

`weil_pairing_gives_primitive_root`: If all m-torsion points of E/ℚ are
rational (`HasFullRationalTorsion E m`), then ℚ contains a primitive m-th
root of unity.

## Optimized proof strategy (Q1078)

**Key observation:** For m ≥ 3, `IsPrimitiveRoot ζ m` is impossible over ℚ
(Mathlib's `isPrimitiveRoot_rat_order_le_two`). So we prove that
`HasFullRationalTorsion E m → m ≤ 2`, then finish by casework on m ∈ {1,2}.

**Proof route:** Instead of formalizing the full Weil pairing (divisor theory,
non-degeneracy, Galois equivariance), use the determinant of the mod-m Galois
representation:

1. `hfull` gives m² rational m-torsion points.
2. In characteristic zero, geometric E[m] has exactly m² points.
3. Hence all geometric m-torsion is rational → mod-m Galois representation is trivial.
4. det(ρ_m) = cyclotomic character ε_m.
5. At complex conjugation, ε_m evaluates to -1.
6. Triviality → -1 = 1 mod m → m | 2 → m ≤ 2.

This avoids exposing Weil pairing internals; the obstruction is isolated in one
targeted lemma.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-! ## Base cases: m = 1 and m = 2 -/

private lemma primitive_root_one : IsPrimitiveRoot (1 : ℚ) 1 :=
  IsPrimitiveRoot.one

private lemma primitive_root_two : IsPrimitiveRoot (-1 : ℚ) 2 := by
  constructor
  · norm_num
  · intro l hl
    by_contra h
    have hodd : Odd l := by
      rcases Nat.even_or_odd l with ⟨k, hk⟩ | ho
      · exact absurd ⟨k, by omega⟩ h
      · exact ho
    have : l < 2 := by omega
    interval_cases l

/-! ## Core obstruction: HasFullRationalTorsion E m → m ≤ 2

This is the minimal hard lemma needed. It encapsulates the Galois-theoretic
argument without exposing the full Weil pairing machinery.

The proof outline uses determinant of mod-m Galois representation = cyclotomic
character evaluated at complex conjugation. Left as a sorry pending the Galois
representation infrastructure.
-/

theorem fullRationalTorsion_order_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 := by
  -- Core lemma: If E[m] ⊆ E(ℚ), the mod-m Galois representation is trivial.
  -- Its determinant equals the cyclotomic character.
  -- At complex conjugation (which acts on roots of unity by inversion),
  -- the cyclotomic character is -1.
  -- Triviality gives -1 = 1 mod m, so m | 2.
  -- With 0 < m, this gives m ≤ 2.
  sorry

theorem not_hasFullRationalTorsion_of_three_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm3 : 3 ≤ m) :
    ¬ HasFullRationalTorsion E m := by
  intro hfull
  have hm_pos : 0 < m := by omega
  have hm_le_two : m ≤ 2 :=
    fullRationalTorsion_order_le_two (E := E) (m := m) hm_pos hfull
  omega

/-! ## Main theorem: Direct casework on m ≤ 2 -/

theorem weil_pairing_gives_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  by_cases hm1 : m = 1
  · subst hm1
    exact ⟨1, primitive_root_one⟩
  by_cases hm2 : m = 2
  · subst hm2
    exact ⟨-1, primitive_root_two⟩
  have hm3 : 3 ≤ m := by omega
  exact False.elim (not_hasFullRationalTorsion_of_three_le (E := E) hm3 hfull)

end MazurProof
