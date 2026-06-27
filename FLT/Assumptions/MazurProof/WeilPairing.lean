import FLT.Assumptions.MazurProof.Axioms

/-!
# Weil Pairing: Full Rational Torsion Implies Primitive Root of Unity

## Main result

`weil_pairing_gives_primitive_root`: If all m-torsion points of E/ℚ are
rational (`HasFullRationalTorsion E m`), then ℚ contains a primitive m-th
root of unity.

## Proof structure

- **m = 1, 2**: Direct construction (ζ = 1 and ζ = -1). Fully proved, 0 sorry.
- **m ≥ 3**: Via the Weil pairing. One named sorry remains.

## The Weil pairing argument (m ≥ 3)

The Weil pairing e_m : E[m] × E[m] → μ_m is bilinear, alternating,
non-degenerate, and Galois-equivariant. If E[m] ⊆ E(ℚ), Galois acts
trivially on E[m], hence (by equivariance) on Im(e_m). Non-degeneracy
ensures Im(e_m) = μ_m, so μ_m ⊆ ℚ.

## Named sorry obstacle

`sorry_weil_pairing_galois_descent`: When E[m] ⊆ E(ℚ), the primitive
root descends from the algebraic closure to ℚ via the Weil pairing.
**Difficulty: Hard** — requires formalizing:
(a) Weil pairing construction (divisors on curves, not in Mathlib)
(b) Non-degeneracy (Tate module / duality)
(c) Galois equivariance (functoriality of Pic⁰)
(d) Galois descent (Gal-fixed elements are rational)

The existence of primitive roots in the algebraic closure is fully proved
via `HasEnoughRootsOfUnity.exists_primitiveRoot`.

Note: over ℚ, `IsPrimitiveRoot ζ m` for m ≥ 3 is impossible
(by `isPrimitiveRoot_rat_order_le_two`), so `HasFullRationalTorsion E m`
is vacuously false. The Weil pairing proves this vacuity.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-! ### Small order: direct construction of primitive roots -/

private lemma primitive_root_order_one : ∃ ζ : ℚ, IsPrimitiveRoot ζ 1 :=
  ⟨1, IsPrimitiveRoot.one⟩

private lemma neg_one_isPrimitiveRoot_two : IsPrimitiveRoot (-1 : ℚ) 2 := by
  constructor
  · norm_num
  · intro l hl
    by_contra h
    have hodd : Odd l := by
      rcases Nat.even_or_odd l with ⟨k, hk⟩ | ho
      · exact absurd ⟨k, by omega⟩ h
      · exact ho
    linarith [hodd.neg_one_pow (α := ℚ)]

private lemma primitive_root_order_two : ∃ ζ : ℚ, IsPrimitiveRoot ζ 2 :=
  ⟨-1, neg_one_isPrimitiveRoot_two⟩

/-! ### Weil pairing infrastructure (m ≥ 3) -/

/-- A primitive m-th root of unity exists in the algebraic closure of ℚ.
Uses `HasEnoughRootsOfUnity` from `Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`:
the algebraic closure is separably closed, so X^m - 1 splits with m distinct
roots forming a cyclic group that has a generator. -/
private lemma exists_primitive_root_in_algebraic_closure (m : ℕ) (hm : 0 < m) :
    ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ m := by
  haveI : NeZero (m : ℚ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) m

/--
**Sorry: Galois descent via Weil pairing**

If E[m] ⊆ E(ℚ) and a primitive m-th root ζ exists in ℚ̄, then ℚ contains
a primitive m-th root. The argument:

1. The Weil pairing e_m : E[m] × E[m] → μ_m is non-degenerate and
   Galois-equivariant: σ(e_m(P,Q)) = e_m(σP, σQ) for σ ∈ Gal(ℚ̄/ℚ).
2. If E[m] ⊆ E(ℚ), then σP = P for all P ∈ E[m], so σ(e_m(P,Q)) = e_m(P,Q).
3. By non-degeneracy, Im(e_m) = μ_m, so σ fixes all of μ_m.
4. Elements of ℚ̄ fixed by Gal(ℚ̄/ℚ) lie in ℚ (Galois descent).

**Obstacles** (all absent from Mathlib as of 2026-06):
- `weil_pairing_construction`: e_m via divisor theory on elliptic curves
- `weil_pairing_nondegeneracy`: non-degeneracy from Tate module theory
- `weil_pairing_galois_equivariance`: functoriality of Pic⁰ under base change
- `galois_fixed_point_theorem`: Gal(ℚ̄/ℚ)-fixed points of ℚ̄ equal ℚ
-/
private lemma sorry_weil_pairing_galois_descent
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} (hm : 2 < m)
    (hfull : HasFullRationalTorsion E m)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ m) :
    ∃ ζ' : ℚ, IsPrimitiveRoot ζ' m := by
  sorry

/-! ### Assembly: main theorem -/

/-- If all m-torsion of E/ℚ is rational, then ℚ contains a primitive m-th
root of unity. This theorem discharges the axiom `weil_pairing_primitive_root`
from `Axioms.lean`. -/
theorem weil_pairing_gives_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  by_cases hle : m ≤ 2
  · interval_cases m
    · exact primitive_root_order_one
    · exact primitive_root_order_two
  · have hgt : 2 < m := by omega
    obtain ⟨ζ, hζ⟩ := exists_primitive_root_in_algebraic_closure m (by omega)
    exact sorry_weil_pairing_galois_descent E hgt hfull ζ hζ

end MazurProof
