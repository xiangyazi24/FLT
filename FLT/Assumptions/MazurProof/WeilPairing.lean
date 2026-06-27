import FLT.Assumptions.MazurProof.Axioms

/-!
# Weil Pairing: Full Rational Torsion Implies Primitive Root of Unity

## Main result

`weil_pairing_gives_primitive_root`: If all m-torsion points of E/ℚ are
rational (`HasFullRationalTorsion E m`), then ℚ contains a primitive m-th
root of unity.

## Proof structure

- **m = 1, 2**: Direct construction (ζ = 1 and ζ = -1). Fully proved, 0 sorry.
- **m ≥ 3**: Via the Weil pairing. Two named sorries remain.

## The Weil pairing argument (m ≥ 3)

The Weil pairing e_m : E[m] × E[m] → μ_m is bilinear, alternating,
non-degenerate, and Galois-equivariant. If E[m] ⊆ E(ℚ), Galois acts
trivially on E[m], hence (by equivariance) on Im(e_m). Non-degeneracy
ensures Im(e_m) = μ_m, so μ_m ⊆ ℚ.

## Named sorry obstacles

1. `sorry_primitive_root_in_algebraic_closure`: A primitive m-th root of
   unity exists in the algebraic closure of ℚ. This follows from the
   splitting of X^m - 1 in an algebraically closed field of char 0.
   **Difficulty: Medium** — needs connecting Mathlib's cyclotomic and
   algebraic closure APIs.

2. `sorry_weil_pairing_galois_descent`: When E[m] ⊆ E(ℚ), the primitive
   root descends from ℚ̄ to ℚ via the Weil pairing. **Difficulty: Hard** —
   requires formalizing:
   (a) Weil pairing construction (divisors on curves, not in Mathlib)
   (b) Non-degeneracy (Tate module / duality)
   (c) Galois equivariance (functoriality of Pic⁰)
   (d) Galois descent (Gal-fixed elements are rational)

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

/--
**Sorry 1: Primitive root exists in algebraic closure**

In any algebraically closed field of characteristic 0, a primitive m-th root
of unity exists for m ≥ 1. This follows from:
- X^m - 1 splits completely in the algebraic closure
- char = 0 implies X^m - 1 is separable (m distinct roots)
- The roots form a cyclic group of order m, which has a generator

**Mathlib path**: Connect `IsAlgClosed` (AlgebraicClosure ℚ) with
`Polynomial.roots` of X^m - 1 and extract a generator of the cyclic
root group. Key lemmas: `IsAlgClosed.exists_aeval_eq_zero`,
`Polynomial.separable_X_pow_sub_one`, `IsCyclic` for finite subgroups
of a field's multiplicative group.
-/
private lemma sorry_primitive_root_in_algebraic_closure (m : ℕ) (hm : 0 < m) :
    ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ m := by
  sorry

/--
**Sorry 2: Galois descent via Weil pairing**

If E[m] ⊆ E(ℚ) and a primitive m-th root ζ exists in ℚ̄, then ℚ contains
a primitive m-th root. The argument:

1. The Weil pairing e_m : E[m] × E[m] → μ_m is non-degenerate and
   Galois-equivariant: σ(e_m(P,Q)) = e_m(σP, σQ) for σ ∈ Gal(ℚ̄/ℚ).
2. If E[m] ⊆ E(ℚ), then σP = P for all P ∈ E[m], so σ(e_m(P,Q)) = e_m(P,Q).
3. By non-degeneracy, Im(e_m) = μ_m, so σ fixes all of μ_m.
4. Elements of ℚ̄ fixed by Gal(ℚ̄/ℚ) lie in ℚ (Galois descent).

**Obstacles** (all absent from Mathlib as of 2026-06):
- `weil_pairing_construction`: e_m via divisor theory
- `weil_pairing_nondegeneracy`: non-degeneracy from Tate module
- `weil_pairing_galois_equivariance`: functoriality of Pic⁰
- `galois_fixed_point_theorem`: Gal-fixed points of ℚ̄ = ℚ
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
  rcases le_or_lt m 2 with hle | hgt
  · interval_cases m
    · exact primitive_root_order_one
    · exact primitive_root_order_two
  · obtain ⟨ζ, hζ⟩ := sorry_primitive_root_in_algebraic_closure m (by omega)
    exact sorry_weil_pairing_galois_descent E hgt hfull ζ hζ

end MazurProof
