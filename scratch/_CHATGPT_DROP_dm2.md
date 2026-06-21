# Q99: Round-2 scaffold for `preΨ'_separable`

This is a build-ready dependency plan for the most feasible route to

```lean
(W.preΨ' n).Separable
```

for a Weierstrass elliptic curve `W/k`, assuming `(n : k) ≠ 0`.

The recommended route is the **formal/local route**:

```text
Weierstrass formal group
→ linear coefficient of [n](T) is n
→ [n] is étale when (n : k) ≠ 0
→ E[n] is reduced
→ the x-coordinate map is unramified away from 2-torsion
→ the reduced/non-2 x-coordinate factor preΨ'_n has simple roots
→ preΨ'_n is separable.
```

The resultant/discriminant route is kept as a fallback interface, but it is not recommended unless one first proves the exact normalized `preΨ'` discriminant formula.

## Status legend

```text
CLOSEABLE-NOW
  Uses existing Mathlib polynomial / finite / root API, possibly with routine local glue.

MISSING-MATHLIB-API
  Requires genuinely new formal geometry / formal group / local ring / divisor-order API.

SEAM
  The narrow theorem downstream code should depend on while the missing API is being built.
```

## Dependency order

```text
0. Polynomial glue lemmas                                      CLOSEABLE-NOW
1. Weierstrass formal group construction                       MISSING-MATHLIB-API
2. Generic formal-group [n]-series linear coefficient          MISSING-MATHLIB-API, but algebraic and local
3. Specialize to Weierstrass: coeff_T([n]) = n                 MISSING-MATHLIB-API
4. [n] is étale when (n:k) ≠ 0                                 MISSING-MATHLIB-API
5. Geometric kernel E[n] is reduced                            MISSING-MATHLIB-API
6. x-map is unramified away from 2-torsion                     MISSING-MATHLIB-API
7. roots of preΨ'_n are exactly non-2 n-torsion x-coordinates  partially available / project seam
8. local multiplicity bridge: reduced kernel + unramified x    MISSING-MATHLIB-API
9. derivative nonzero at each preΨ'_n root                     MISSING-MATHLIB-API, follows from 4-8
10. preΨ'_n separable                                          CLOSEABLE-NOW after 9
```

The downstream theorem should depend only on the final seam:

```lean
WeierstrassCurve.preΨ'_separable
```

Everything above it is the implementation plan for discharging that seam.

---

# Lean scaffold

```lean
import Mathlib

noncomputable section

open Polynomial
open WeierstrassCurve

namespace Polynomial

universe u

/--
CLOSEABLE-NOW.

If the resultant of `f` and `f.derivative` is nonzero, then `f` is separable.
This is the clean generic bridge for a possible resultant proof.
-/
lemma separable_of_resultant_derivative_ne_zero
    {k : Type u} [Field k] {f : k[X]}
    (hf : f ≠ 0)
    (hres : f.resultant f.derivative ≠ 0) :
    f.Separable := by
  rw [Polynomial.separable_def]
  by_contra hcop
  have hz : f.resultant f.derivative = 0 := by
    rw [Polynomial.resultant_eq_zero_iff]
    exact ⟨Or.inl hf, hcop⟩
  exact hres hz

/--
CLOSEABLE-NOW, but may require minor API adaptation.

Over a separably closed / algebraically closed field, if every root of `f` has nonzero derivative,
then `f` is separable. This is often the most convenient final bridge for the formal route.

Implementation options:
* use `Polynomial.separable_def` and show `IsCoprime f f.derivative`;
* if `¬ IsCoprime`, take a common irreducible factor and use `IsSepClosed` to get a root;
* or use root multiplicities / `rootSet` API if the polynomial is known to split.
-/
lemma separable_of_forall_root_derivative_ne_zero
    {k : Type u} [Field k] [IsSepClosed k] {f : k[X]}
    (hf : f ≠ 0)
    (hroot : ∀ x : k, f.eval x = 0 → f.derivative.eval x ≠ 0) :
    f.Separable := by
  -- CLOSEABLE-NOW polynomial lemma.
  -- Suggested proof:
  -- 1. `rw [Polynomial.separable_def]`.
  -- 2. Suppose `¬ IsCoprime f f.derivative`.
  -- 3. Extract a common nonconstant factor over the field.
  -- 4. Since `k` is separably closed, get a root `x` of that factor.
  -- 5. Then `f.eval x = 0` and `f.derivative.eval x = 0`, contradiction.
  -- Exact low-level API names may vary; this is pure polynomial algebra, no EC geometry.
  sorry

end Polynomial

namespace WeierstrassCurve

universe u

variable {k : Type u} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

/-!
## 1. Formal group API
-/

/--
MISSING-MATHLIB-API.

The Weierstrass formal group of `W` at the identity, using the standard local parameter
`t = -x / y`.

Expected target declaration to add to Mathlib/FLT:

```lean
noncomputable def WeierstrassCurve.formalGroup
    {k : Type u} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic] : FormalGroup k
```

Current Mathlib has generic `FormalGroup`, but no `WeierstrassCurve.formalGroup`.
-/
-- noncomputable def formalGroup : FormalGroup k := ...

/--
MISSING-MATHLIB-API.

The formal parameter `t = -x/y` at `O`.  The final implementation may represent this as an element
of a completed local ring, not as a global rational function.

Expected declaration name:

```lean
noncomputable def WeierstrassCurve.formalParameter
    (W : WeierstrassCurve k) [W.IsElliptic] : ...
```
-/
-- noncomputable def formalParameter : ... := ...

/-!
## 2. Formal `[n]`-series
-/

/--
MISSING-MATHLIB-API, but algebraically straightforward once generic formal groups are usable.

For any one-dimensional commutative formal group law, the linear coefficient of its formal
`[n]`-series is `(n : k)`.

Expected generic declaration name:

```lean
theorem FormalGroup.linearCoeff_nsmul
    (F : FormalGroup k) (n : ℕ) :
    -- coeff of `T` in `[n]_F(T)` equals `(n : k)`
```

The exact coefficient expression depends on the power-series API chosen for formal groups.
-/
theorem formalGroup_linearCoeff_nsmul_placeholder
    (n : ℕ) : True := by
  -- Proof once API exists:
  -- induction on `n`; use that `F(X,Y) = X + Y + higher order terms`.
  trivial

/--
MISSING-MATHLIB-API.

Specialization of the generic formal-group statement to the Weierstrass formal group.

Expected final declaration:

```lean
theorem WeierstrassCurve.formal_nsmul_linearCoeff
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) :
    -- coeff_T ([n]_{W.formalGroup}) = (n : k)
```
-/
theorem formal_nsmul_linearCoeff_placeholder
    (n : ℕ) : True := by
  -- Use `FormalGroup.linearCoeff_nsmul W.formalGroup n`.
  trivial

/-!
## 3. Étaleness of multiplication by n
-/

/--
MISSING-MATHLIB-API.

Multiplication by `n` has invertible differential at the identity when `(n : k) ≠ 0`.

Expected declaration name:

```lean
theorem WeierstrassCurve.nsmul_differential_at_origin_isUnit
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    IsUnit (differential_of_[n]_at_O)
```

This is the local formal-group use of `formal_nsmul_linearCoeff`.
-/
theorem nsmul_differential_at_origin_isUnit_placeholder
    {n : ℕ} (hn : (n : k) ≠ 0) : True := by
  trivial

/--
MISSING-MATHLIB-API.

Multiplication by `n` is étale on the Weierstrass curve when `(n : k) ≠ 0`.

Expected declaration name:

```lean
theorem WeierstrassCurve.nsmul_etale_of_natCast_ne_zero
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    -- `[n] : E → E` is étale
```

Reason:
* at `O`, use the formal group linear coefficient;
* at any point, use translation to move the assertion to `O`.
-/
theorem nsmul_etale_of_natCast_ne_zero_placeholder
    {n : ℕ} (hn : (n : k) ≠ 0) : True := by
  trivial

/--
MISSING-MATHLIB-API.

The geometric kernel `E[n]` is reduced when `(n : k) ≠ 0`.

Expected declaration name:

```lean
theorem WeierstrassCurve.n_torsion_reduced_of_natCast_ne_zero
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    -- scheme-theoretic kernel of `[n]` is reduced
```

This follows from étaleness of `[n]` and stability under base change.
-/
theorem n_torsion_reduced_of_natCast_ne_zero_placeholder
    {n : ℕ} (hn : (n : k) ≠ 0) : True := by
  trivial

/-!
## 4. x-coordinate local behavior
-/

/--
MISSING-MATHLIB-API.

The x-coordinate map is unramified at a point that is not 2-torsion.

Concrete intended theorem, stated using Mathlib affine points.  The conclusion is schematic because
Mathlib currently lacks the needed local-ring/order-of-vanishing API for this curve model.
-/
theorem xCoord_unramified_of_two_nsmul_ne_zero
    {x y : k} (hxy : (W⁄k).Nonsingular x y)
    (h2 : (2 : ℕ) • Affine.Point.some x y hxy ≠ 0) :
    True := by
  -- Future proof:
  -- * The involution `P ↦ -P` fixes exactly 2-torsion.
  -- * The quotient by this involution is the x-line.
  -- * Therefore the quotient map is unramified away from fixed points.
  trivial

/--
PROJECT SEAM / partially closeable from existing division polynomial and coordinate formula work.

Root realization for `preΨ'`: over a separably closed field, a root of `preΨ'_n` is the x-coordinate
of a non-2-torsion `n`-torsion point.

This depends on the coordinate formula for `[n]P` and the non-circular coprimality
`preΨ'_n ⟂ Ψ₂Sq`.
-/
theorem preΨ'_root_realization_non_two_torsion
    [IsSepClosed k]
    {n : ℕ} (hn : (n : k) ≠ 0) {x : k}
    (hx : (W.preΨ' n).eval x = 0) :
    ∃ y (hxy : (W⁄k).Nonsingular x y),
      (2 : ℕ) • Affine.Point.some x y hxy ≠ 0 ∧
      n • Affine.Point.some x y hxy = 0 := by
  -- Status: PROJECT SEAM.
  -- Required dependencies:
  -- * x-coordinate formula for `[n]P` using `Φ` and `ΨSq`;
  -- * non-circular proof that `preΨ'_n` and `Ψ₂Sq` have no common root;
  -- * existence of a y-coordinate over `IsSepClosed k`.
  sorry

/-!
## 5. Local multiplicity bridge
-/

/--
MISSING-MATHLIB-API.

Local bridge: if `E[n]` is reduced at a non-2-torsion point and the x-map is unramified there,
then the corresponding x-coordinate root of `preΨ'_n` is simple.

This is the exact location where the naive dual-number/projective-addition proof degenerates.
It should be proved using local rings / completed local rings / order of vanishing.
-/
theorem derivative_preΨ'_eval_ne_zero_of_eval_eq_zero
    [IsSepClosed k]
    {n : ℕ} (hn : (n : k) ≠ 0) {x : k}
    (hx : (W.preΨ' n).eval x = 0) :
    (Polynomial.derivative (W.preΨ' n)).eval x ≠ 0 := by
  -- Dependency order inside this proof:
  -- 1. `preΨ'_root_realization_non_two_torsion W hn hx` gives a point `P` above `x`.
  -- 2. `n_torsion_reduced_of_natCast_ne_zero W hn` says the kernel is reduced at `P`.
  -- 3. `xCoord_unramified_of_two_nsmul_ne_zero W hxy h2` says x is an étale local parameter at P.
  -- 4. Therefore the local x-cut has multiplicity one.
  -- 5. Translate local multiplicity one into derivative nonzero of the x-polynomial `preΨ' n`.
  --
  -- Missing exact declarations:
  -- * `WeierstrassCurve.localRingAtPoint` or equivalent;
  -- * `WeierstrassCurve.completedLocalRingAtPoint`;
  -- * `WeierstrassCurve.orderOfVanishing_xMinus`;
  -- * `WeierstrassCurve.multiplicity_root_eq_local_length`;
  -- * `WeierstrassCurve.preΨ'_divisor_non_two_torsion`.
  sorry

/-!
## 6. Final separability theorem
-/

/--
CLOSEABLE-NOW after `derivative_preΨ'_eval_ne_zero_of_eval_eq_zero`.

Geometric separability over a separably closed field.
-/
theorem preΨ'_separable_geometric
    [IsSepClosed k]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  -- Use the polynomial helper above.
  refine Polynomial.separable_of_forall_root_derivative_ne_zero ?hf ?hroot
  · -- Existing degree/nonzero API should provide this as `WeierstrassCurve.preΨ'_ne_zero W hn`.
    exact WeierstrassCurve.preΨ'_ne_zero W hn
  · intro x hx
    exact W.derivative_preΨ'_eval_ne_zero_of_eval_eq_zero hn hx

/--
SEAM: final theorem downstream code should import/use.

For a general field, the final proof should base-change to a separable/algebraic closure, prove the
geometric statement, and descend separability.  If the consuming code only works over an algebraic
or separably closed field, use `preΨ'_separable_geometric` directly.
-/
theorem preΨ'_separable
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  -- Future proof plan:
  -- 1. Let `Kbar := AlgebraicClosure k`.
  -- 2. Use `map_preΨ'` to identify `(W.preΨ' n).map (algebraMap k Kbar)` with
  --    `(W.map (algebraMap k Kbar)).preΨ' n`.
  -- 3. Use `preΨ'_separable_geometric` over `Kbar`.
  -- 4. Descend separability along the injective field map.
  --
  -- Missing / to confirm exact API:
  -- * `WeierstrassCurve.map_preΨ'` for division polynomials under base change;
  -- * `Polynomial.Separable.of_map` or corresponding descent lemma.
  sorry

end WeierstrassCurve
```

---

# Resultant fallback scaffold

This route is formally possible but not recommended as the primary build target.

```lean
import Mathlib

noncomputable section

open Polynomial
open WeierstrassCurve

namespace WeierstrassCurve

universe u

variable {k : Type u} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

/--
MISSING-MATHLIB-API / MISSING-MATH.

Exact nonvanishing of the resultant of `preΨ'_n` and its derivative.
This would follow from a closed discriminant formula for Mathlib's exact normalized `preΨ'`.
-/
theorem resultant_preΨ'_derivative_ne_zero
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).resultant (Polynomial.derivative (W.preΨ' n)) ≠ 0 := by
  -- Needed formula shape:
  -- `resultant = unit * (n : k)^a * W.Δ^b * parity/leading-coeff factors`.
  -- Hard part: proving the exact formula for the reduced odd part `preΨ'`, whose normalization
  -- removes the `Ψ₂Sq` factor in even level.
  sorry

/--
CLOSEABLE-NOW after the resultant nonvanishing seam.
-/
theorem preΨ'_separable_via_resultant
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  exact Polynomial.separable_of_resultant_derivative_ne_zero
    (WeierstrassCurve.preΨ'_ne_zero W hn)
    (W.resultant_preΨ'_derivative_ne_zero hn)

end WeierstrassCurve
```

## Why the formal route is preferred

The resultant route depends on a large closed formula for the discriminant/resultant of Mathlib's exact `preΨ'` normalization. Proving that formula from the EDS recursion is likely brittle because it must track:

```text
* parity of n,
* the removed Ψ₂Sq factor for even n,
* leading coefficients of preΨ',
* powers of the curve discriminant Δ,
* small exceptional n,
* possible powers of 2.
```

The formal route proves the underlying reason directly: `[n]` is étale when `(n : k) ≠ 0`. It also supports future Weil pairing, torsion group scheme, and Galois-representation work.

## Exact missing declarations to create

```lean
-- Formal group and local parameter
WeierstrassCurve.formalGroup
WeierstrassCurve.formalParameter

-- Generic formal-group n-series API
FormalGroup.nsmulSeries
FormalGroup.linearCoeff_nsmul

-- Weierstrass specialization
WeierstrassCurve.formal_nsmul_linearCoeff
WeierstrassCurve.nsmul_differential_at_origin_isUnit
WeierstrassCurve.nsmul_etale_of_natCast_ne_zero
WeierstrassCurve.n_torsion_reduced_of_natCast_ne_zero

-- x-map local behavior
WeierstrassCurve.xCoord_unramified_of_two_nsmul_ne_zero

-- local ring / divisor / multiplicity bridge
WeierstrassCurve.localRingAtPoint
WeierstrassCurve.completedLocalRingAtPoint
WeierstrassCurve.orderOfVanishing_xMinus
WeierstrassCurve.preΨ'_divisor_non_two_torsion
WeierstrassCurve.multiplicity_root_eq_local_length
WeierstrassCurve.derivative_preΨ'_eval_ne_zero_of_eval_eq_zero

-- base change/descent convenience
WeierstrassCurve.map_preΨ'
Polynomial.Separable.of_injective_map   -- or equivalent existing/renamed lemma
```

## Minimal thing to implement first

The single most useful first new theorem is the local derivative statement:

```lean
theorem WeierstrassCurve.derivative_preΨ'_eval_ne_zero_of_eval_eq_zero
    {k : Type u} [Field k] [IsSepClosed k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) {x : k}
    (hx : (W.preΨ' n).eval x = 0) :
    (Polynomial.derivative (W.preΨ' n)).eval x ≠ 0
```

Once that theorem exists, the final separability proof is short and purely polynomial.
