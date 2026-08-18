import FLT.Assumptions.MazurProof.RationalPointsN49

/-!
# N49 composition shortcut: preΨ'₄₉(0) via preΨ'₇(x(7P))

The division polynomial composition identity gives, in the function field of E:

  ψ₄₉(P) = ψ₇(7P) · ψ₇(P)⁴⁹

At the Tate origin P = (0,0), with `ψ₇(P) = b¹⁶ · F₇` where `F₇ = c³+bc-b²`:

  preΨ'₄₉(0) = preΨ'₇(x(7P)) · (b¹⁶ · F₇)⁴⁹

where `x(7P) = Φ₇(0) / (b¹⁶ · F₇)² = bc(c²-b+c)(bc²-2b²+3bc-c²) / F₇²`.

This avoids the full 48-level recursion and expresses preΨ'₄₉(0) via one
degree-24 evaluation of the known polynomial `preΨ'₇` at a rational function
of `(b,c)`.

## Consequence for H₄₉

Since `preΨ'₄₉(0) = b⁸⁰⁰ · F₇ · H₄₉`, comparing with the composition gives:

  H₄₉ = preΨ'₇(x(7P)) · b¹⁶ⁱ⁴⁹⁻⁸⁰⁰ · F₇⁴⁸ / (denominator clearing)

The denominator-free form uses the degree-24 homogenization of preΨ'₇.

## References

- ChatGPT Q5276 (2026-08-18): exact composition formula and correction
- Sage verification: x(7P) numerator has 8 terms, denominator is F₇²
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsN49Composition

open MazurProof.TateOriginDivision
open MazurProof.RationalPointsN49
open Scratch.TateZ2xZ10Reduction

noncomputable section

/-- The x-coordinate numerator of 7P on the Tate curve at origin (0,0).
Sage: `(7 * E(0,0))[0].numerator()` with E over Q(b,c). -/
def xNum7P (b c : ℚ) : ℚ :=
  2 * b ^ 4 * c - 5 * b ^ 3 * c ^ 2 - 3 * b ^ 3 * c ^ 3 +
    4 * b ^ 2 * c ^ 3 + 4 * b ^ 2 * c ^ 4 + b ^ 2 * c ^ 5 -
    b * c ^ 4 - b * c ^ 5

/-- The x-coordinate denominator of 7P, which equals F₇². -/
def xDen7P (b c : ℚ) : ℚ :=
  (F7 b c) ^ 2

/-- The x-coordinate of 7P = 7·(0,0) on the Tate curve, as a rational
function of the Tate parameters. Well-defined when F₇ ≠ 0 (i.e., when
the origin does not have order dividing 7). -/
def x7P (b c : ℚ) (_hF : F7 b c ≠ 0) : ℚ :=
  xNum7P b c / xDen7P b c

/-- The factored form: `xNum7P = b·c·(c²-b+c)·(bc²-2b²+3bc-c²)`. -/
theorem xNum7P_factor (b c : ℚ) :
    xNum7P b c = b * c * (c ^ 2 - b + c) * (b * c ^ 2 - 2 * b ^ 2 + 3 * b * c - c ^ 2) := by
  unfold xNum7P; ring

/-- `Φ₇(0) = b³² · xNum7P`, relating Mathlib's Φ polynomial to the
x-coordinate of 7P. -/
def phi7_at_origin (b c : ℚ) : ℚ :=
  b ^ 32 * xNum7P b c

/-- `ΨSq₇(0) = (preΨ'₇(0))² = b³² · F₇²`, the square of the
7-division polynomial at origin. -/
theorem psiSq7_at_origin (b c : ℚ) :
    (b ^ 16 * F7 b c) ^ 2 = b ^ 32 * (F7 b c) ^ 2 := by
  ring

/-- The composition identity for preΨ'₄₉ at the Tate origin, expressed via
`preΨ'₇` evaluated at `x(7P)`. This is the key structural lemma.

In the function field of E(b,c):
  preΨ'₄₉(0) = preΨ'₇(x(7P)) · (preΨ'₇(0))⁴⁹

where x(7P) = xNum7P / F₇².

This holds when F₇ ≠ 0 and b ≠ 0 (so 7P is an affine point distinct from O).

The denominator-free version (homogenized, polynomial in Z[b,c]) avoids
the F₇² denominator:
  preΨ'₄₉(0) · F₇⁴⁸ = D̂₇(Φ₇(0), ΨSq₇(0)) · (preΨ'₇(0))
where D̂₇ is the degree-24 homogenization of preΨ'₇. -/
theorem composition_identity_sorry (b c : ℚ) (_hb : b ≠ 0) (hF : F7 b c ≠ 0) :
    ((W b c).preΨ' 49).eval 0 =
      ((W b c).preΨ' 7).eval (x7P b c hF) *
        (((W b c).preΨ' 7).eval 0) ^ 49 := by
  sorry

end

end MazurProof.RationalPointsN49Composition
