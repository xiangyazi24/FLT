[ask-gpt dm1 tid=94e2dcee +0s] dispatched, waiting for answer
[ask-gpt dm1 tid=94e2dcee +90s] waiting (status=processing)
[ask-gpt dm1 tid=94e2dcee +180s] waiting (status=processing)
[ask-gpt dm1 tid=94e2dcee +270s] waiting (status=processing)
[ask-gpt dm1 tid=94e2dcee +360s] waiting (status=processing)
[ask-gpt dm1 tid=94e2dcee +450s] waiting (status=processing)
[ask-gpt dm1 tid=94e2dcee +540s] waiting (status=processing)
[ask-gpt dm1 tid=94e2dcee +578s] terminal: status=completed
The key correction: **the raw DualNumber/projective-formula proof does not work as stated**. For `Pₐ = [-aε,1,0]` and `P_b = [-bε,1,0]`, both have `Z = 0`; Mathlib’s projective `addX/addZ` formulas have a common vanishing factor at `(O,O)`. In particular, the documented `addX_of_Z_eq_zero_left` and `addZ_of_Z_eq_zero_left` reduce to expressions containing `Q 2`, hence vanish when both inputs are infinitesimal points over `O`. You must use a **regularized local chart / completed-local-ring primitive**, not raw `Projective.addX/addY/addZ`. Mathlib has `DualNumber`, `ε`, and `ε^2=0`, and projective addition formulas over commutative rings, but not the regularized formal-neighborhood group law. citeturn507049view0turn114469view0turn114469view1

So SEAM1’s buildable shape is:

```lean
DualNumber first jet theorem
  ⇒ local order theorem for [n] near a kernel point
  ⇒ order of ΨSqₙ is 2
  ⇒ order of preΨ'ₙ is 1
  ⇒ derivative nonzero at every root
  ⇒ Polynomial.Separable
```

The **new hard primitive** is not the induction `d[n]_O = n`; it is the local bridge

```lean
xCoord_nsmul_pole_order_two_at_non2_kernel
```

or equivalently

```lean
ΨSq_order_two_at_non2_kernel
```

SEAM2 gives the global `x`-coordinate formula, but to prove separability by orders you need its **formal-arc/local-field** version, not just pointwise equality over `k`.

---

## 1. DualNumber first jet

Use Mathlib’s dual numbers:

```lean
import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula

open scoped DualNumber
open TrivSqZeroExt

namespace WeierstrassCurve

variable {k : Type*} [Field k]
variable (W : WeierstrassCurve k)

abbrev KDual := DualNumber k

noncomputable def tangentOPoint (a : k) : Fin 3 → KDual k
| 0 => - algebraMap k (KDual k) a * DualNumber.eps
| 1 => 1
| 2 => 0
```

The curve-equation proof is genuinely easy:

```lean
theorem tangentOPoint_equation (a : k) :
    (W.baseChange (KDual k)).toProjective.Equation
      (W.tangentOPoint a) := by
  -- The projective Weierstrass equation at [X,Y,Z]=[-aε,1,0]
  -- has only terms involving ε² or Z, hence vanishes.
  simp [tangentOPoint, DualNumber.eps_mul_eps, DualNumber.eps_pow_two]
  ring
```

But the raw addition statement should **not** be written as:

```lean
-- BAD / not the right primitive:
theorem tangentOPoint_add_formula_bad (a b : k) :
    SameP2
      ((W.baseChange (KDual k)).toProjective.add
        (W.tangentOPoint a) (W.tangentOPoint b))
      (W.tangentOPoint (a + b)) := ...
```

The projective polynomial representative has a common zero factor at `(O,O)`; after quotienting/cancelling in the completed local chart, the answer is `a+b`, but the raw formula loses it.

Use this **regularized primitive** instead:

```lean
/--
First-order addition in the completed local chart at `O`.

Mathematically: if `t = -X/Y` is the local parameter at `O`, then
`t(P + Q) = t(P) + t(Q) + O((t(P),t(Q))^2)`.
Specializing `t(P)=aε`, `t(Q)=bε` gives `(a+b)ε`.
-/
axiom tangentOPoint_add_regularized
    (W : WeierstrassCurve k) [W.IsElliptic]
    (a b : k) :
    SameP2
      (regularizedProjectiveAddAtO W (W.tangentOPoint a) (W.tangentOPoint b))
      (W.tangentOPoint (a + b))
```

Then the induction is straightforward:

```lean
noncomputable def tangentONsmul
    (W : WeierstrassCurve k) [W.IsElliptic] :
    ℕ → k → Fin 3 → KDual k
| 0, _ => W.tangentOPoint 0
| n + 1, a =>
    regularizedProjectiveAddAtO W
      (tangentONsmul W n a)
      (W.tangentOPoint a)

theorem tangentOPoint_nsmul_formula
    (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℕ) (a : k) :
    SameP2
      (tangentONsmul W n a)
      (W.tangentOPoint ((n : k) * a)) := by
  induction n with
  | zero =>
      simp [tangentONsmul, tangentOPoint]
  | succ n ih =>
      -- regularized add:
      -- (n*a) + a = (n+1)*a
      refine SameP2.trans ?_ ?_
      · exact regularizedProjectiveAddAtO_congr_left_right W ih (SameP2.refl _)
      · simpa [tangentONsmul, Nat.cast_succ, add_mul] using
          tangentOPoint_add_regularized W ((n : k) * a) a
```

For SEAM1, package the only statement you actually need as:

```lean
/--
The differential of `[n]` at `O` is multiplication by `n`.
This is the reusable first-jet theorem.
-/
theorem d_nsmul_at_O
    (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℕ) :
    tangentMapAtO_nsmul W n = LinearMap.lsmul k k (n : k) := by
  ext a
  -- follows from `tangentOPoint_nsmul_formula`
  sorry
```

The hard step is **not** `eps^2=0`; Mathlib has `DualNumber.eps_mul_eps` and `DualNumber.eps_pow_two`. The hard step is proving `tangentOPoint_add_regularized`, i.e. doing the cancellation of the raw projective addition formula in the local chart at `O`. citeturn507049view0turn664221view2

---

## 2. Local-order bridge

You need a formal local theorem, not merely DualNumber.

At a non-2-torsion affine point `P = (x₀,y₀)`, the local parameter can be

\[
T = x - x_0
\]

because non-2-torsion means

\[
2y_0+a_1x_0+a_3\ne0,
\]

so the projection to the `x`-line is étale at `P`.

Define polynomial evaluation along this local `x`-parameter:

```lean
namespace Polynomial

open PowerSeries

variable {k : Type*} [Field k]

noncomputable def evalAtX (x₀ : k) (p : Polynomial k) : PowerSeries k :=
  Polynomial.aeval (PowerSeries.C x₀ + PowerSeries.X) p

lemma evalAtX_constCoeff (x₀ : k) (p : Polynomial k) :
    PowerSeries.constantCoeff (Polynomial.evalAtX x₀ p) = p.eval x₀ := by
  simp [evalAtX]

lemma order_evalAtX_zero_of_eval_ne_zero
    (x₀ : k) (p : Polynomial k)
    (hp : p.eval x₀ ≠ 0) :
    (Polynomial.evalAtX x₀ p).order = 0 := by
  rw [PowerSeries.order_eq_nat]
  constructor
  · simpa [evalAtX_constCoeff] using hp
  · intro i hi
    omega

lemma order_evalAtX_one_iff
    (x₀ : k) (p : Polynomial k) :
    (Polynomial.evalAtX x₀ p).order = 1 ↔
      p.eval x₀ = 0 ∧ p.derivative.eval x₀ ≠ 0 := by
  constructor
  · intro h
    have h0 :
        PowerSeries.constantCoeff (Polynomial.evalAtX x₀ p) = 0 := by
      have hcoeff0 :=
        (PowerSeries.order_eq_nat.mp h).2 0 (by omega)
      simpa using hcoeff0
    have h1 :
        PowerSeries.coeff 1 (Polynomial.evalAtX x₀ p) ≠ 0 := by
      exact (PowerSeries.order_eq_nat.mp h).1
    constructor
    · simpa [Polynomial.evalAtX_constCoeff] using h0
    · -- coeff of degree 1 in p(x₀+X) is p'(x₀)
      simpa [Polynomial.evalAtX, Polynomial.coeff_aeval_X_add_C_one]
        using h1
  · rintro ⟨hroot, hderiv⟩
    rw [PowerSeries.order_eq_nat]
    constructor
    · simpa [Polynomial.evalAtX, Polynomial.coeff_aeval_X_add_C_one]
        using hderiv
    · intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simpa [Polynomial.evalAtX_constCoeff] using hroot
```

The only helper you may need to add is the coefficient lemma:

```lean
lemma Polynomial.coeff_aeval_X_add_C_one
    {k : Type*} [Field k]
    (p : Polynomial k) (x₀ : k) :
    PowerSeries.coeff 1
      (Polynomial.aeval (PowerSeries.C x₀ + PowerSeries.X) p)
      =
    p.derivative.eval x₀ := by
  induction p using Polynomial.induction_on' with
  | monomial n a =>
      -- derivative of `a * X^n`; coefficient of X in `(x₀+X)^n`.
      simp [Polynomial.derivative_monomial]
      -- remaining binomial coefficient computation
      sorry
  | add p q hp hq =>
      simp [hp, hq]
```

Mathlib’s `PowerSeries.order` API gives `order_eq_nat`, `order_zero_of_unit`, `order_X`, `order_mul`, and `order_pow`; over a domain, `order_mul` and `order_pow` are exact equalities. citeturn906394view0

Now state the actual local bridge as a primitive:

```lean
namespace WeierstrassCurve

open Polynomial PowerSeries

variable {k : Type*} [Field k] [DecidableEq k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

/--
Local analytic content of the first-jet theorem.

At a non-2 point `P` killed by `[n]`, the function `x([n]R)` has a
double pole as `R → P`.

This is the real bridge from `d[n]_O = n ≠ 0` to division-polynomial
separability.
-/
axiom xCoord_nsmul_pole_order_two_at_non2_kernel
    {n : ℕ} (hn : (n : k) ≠ 0)
    {x₀ y₀ : k}
    {hP : W.toAffine.Nonsingular x₀ y₀}
    (hker :
      n • (W.toAffine.Point.some x₀ y₀ hP : W.toAffine.Point) = 0)
    (hnon2 :
      2 • (W.toAffine.Point.some x₀ y₀ hP : W.toAffine.Point) ≠ 0) :
    localPoleOrderAtP_of_xCoord_nsmul W n x₀ y₀ hP = 2
```

Using SEAM2, convert that pole-order statement into an order statement for `ΨSq`.

This is the exact lemma you want:

```lean
/--
SEAM2 plus the local pole-order theorem imply that `ΨSqₙ`
vanishes to order exactly `2` at the `x`-coordinate of every non-2
kernel point.
-/
axiom ΨSq_order_two_at_non2_kernel
    {n : ℕ} (hn : (n : k) ≠ 0)
    {x₀ y₀ : k}
    {hP : W.toAffine.Nonsingular x₀ y₀}
    (hker :
      n • (W.toAffine.Point.some x₀ y₀ hP : W.toAffine.Point) = 0)
    (hnon2 :
      2 • (W.toAffine.Point.some x₀ y₀ hP : W.toAffine.Point) ≠ 0) :
    (Polynomial.evalAtX x₀ (W.ΨSq (n : ℤ))).order = 2
```

That axiom should ultimately be proved as follows:

```lean
-- x([n]R) = Φₙ(x(R)) / ΨSqₙ(x(R))     -- SEAM2, local-field version
-- [n]P = O and d[n]_P ≠ 0              -- DualNumber/local theorem
-- x has pole order 2 at O              -- local parameter at O
-- Φₙ(x₀) ≠ 0                           -- projective x-pair nonzero
-- therefore ΨSqₙ(x₀+T) has order 2
```

Important: a **pointwise** theorem

```lean
xRep (n • P) ~ ![(W.Φ n).eval x, (W.ΨSq n).eval x]
```

is not enough for this order argument. You need the same formula over the fraction field of a formal branch, or a theorem that packages that local consequence.

Now derive the order-one statement for `preΨ'`.

```lean
theorem preΨ'_order_one_at_non2_kernel
    {n : ℕ} (hn : (n : k) ≠ 0)
    {x₀ y₀ : k}
    {hP : W.toAffine.Nonsingular x₀ y₀}
    (hker :
      n • (W.toAffine.Point.some x₀ y₀ hP : W.toAffine.Point) = 0)
    (hnon2 :
      2 • (W.toAffine.Point.some x₀ y₀ hP : W.toAffine.Point) ≠ 0) :
    (Polynomial.evalAtX x₀ (W.preΨ' n)).order = 1 := by
  classical

  have hΨ :
      (Polynomial.evalAtX x₀ (W.ΨSq (n : ℤ))).order = 2 :=
    ΨSq_order_two_at_non2_kernel W hn hker hnon2

  by_cases hnEven : Even n

  · -- ΨSqₙ = preΨ'ₙ^2 * Ψ₂Sq
    have hfactor_unit :
        (Polynomial.evalAtX x₀ W.Ψ₂Sq).order = 0 := by
      -- non-2 means Ψ₂Sq(x₀) ≠ 0
      have h2eval : W.Ψ₂Sq.eval x₀ ≠ 0 := by
        -- from `Ψ₂Sq_eq` + `2 • P ≠ 0`
        exact Ψ₂Sq_eval_ne_zero_of_two_nsmul_ne_zero W hP hnon2
      exact Polynomial.order_evalAtX_zero_of_eval_ne_zero x₀ W.Ψ₂Sq h2eval

    have hdecomp :
        W.ΨSq (n : ℤ) = (W.preΨ' n)^2 * W.Ψ₂Sq := by
      simpa [WeierstrassCurve.ΨSq_ofNat, hnEven]
        using W.ΨSq_even n hnEven

    have hsquare_order :
        (Polynomial.evalAtX x₀ ((W.preΨ' n)^2)).order = 2 := by
      -- order(ΨSq) = order(preΨ'^2) + order(Ψ₂Sq)
      calc
        (Polynomial.evalAtX x₀ ((W.preΨ' n)^2)).order
            =
          (Polynomial.evalAtX x₀ ((W.preΨ' n)^2)).order
            + (0 : ℕ∞) := by simp
        _ =
          (Polynomial.evalAtX x₀ ((W.preΨ' n)^2)).order
            + (Polynomial.evalAtX x₀ W.Ψ₂Sq).order := by
              rw [hfactor_unit]
        _ =
          (Polynomial.evalAtX x₀ (((W.preΨ' n)^2) * W.Ψ₂Sq)).order := by
              rw [PowerSeries.order_mul]
              simp [Polynomial.evalAtX]
        _ = 2 := by
              simpa [hdecomp, Polynomial.evalAtX] using hΨ

    have hpows :
        ((Polynomial.evalAtX x₀ (W.preΨ' n))^2).order = 2 := by
      simpa [Polynomial.evalAtX, map_mul, pow_two]
        using hsquare_order

    exact order_eq_one_of_square_order_two hpows

  · -- ΨSqₙ = preΨ'ₙ^2
    have hdecomp :
        W.ΨSq (n : ℤ) = (W.preΨ' n)^2 := by
      have hnOdd : Odd n := Nat.not_even_iff_odd.mp hnEven
      simpa [WeierstrassCurve.ΨSq_ofNat, hnOdd]
        using W.ΨSq_odd n hnOdd

    have hpows :
        ((Polynomial.evalAtX x₀ (W.preΨ' n))^2).order = 2 := by
      simpa [hdecomp, Polynomial.evalAtX, map_mul, pow_two]
        using hΨ

    exact order_eq_one_of_square_order_two hpows
```

You need this small `ℕ∞` arithmetic lemma:

```lean
lemma order_eq_one_of_square_order_two
    {k : Type*} [Field k]
    {f : PowerSeries k}
    (h : (f ^ 2).order = 2) :
    f.order = 1 := by
  have hpow : 2 • f.order = (2 : ℕ∞) := by
    simpa [PowerSeries.order_pow] using h
  exact enat_two_nsmul_eq_two.mp hpow

lemma enat_two_nsmul_eq_two {a : ℕ∞} :
    2 • a = (2 : ℕ∞) ↔ a = 1 := by
  -- `ℕ∞` is `WithTop ℕ`; split `a = ⊤` / `a = n`.
  -- The finite case is ordinary Nat arithmetic.
  sorry
```

The decomposition of `ΨSq` is exactly the Mathlib definition: for even `n`, `ΨSqₙ = preΨₙ² * Ψ₂Sq`; for odd `n`, `ΨSqₙ = preΨₙ²`. The docs list `ΨSq`, `ΨSq_ofNat`, `ΨSq_even`, `ΨSq_odd`, and explain this definition. citeturn755020view0

---

## 3. Derivative nonzero at every root

You need the root-characterization theorem from SEAM2:

```lean
/--
Root-characterization consequence of SEAM2.
Roots of `preΨ'ₙ` are exactly `x`-coordinates of nonzero non-2 `n`-torsion points.
-/
axiom preΨ'_root_iff_exists_non2_kernel_x
    {n : ℕ} {x₀ : k} :
    (W.preΨ' n).eval x₀ = 0 ↔
      ∃ y₀ (hP : W.toAffine.Nonsingular x₀ y₀),
        n • (W.toAffine.Point.some x₀ y₀ hP : W.toAffine.Point) = 0 ∧
        2 • (W.toAffine.Point.some x₀ y₀ hP : W.toAffine.Point) ≠ 0
```

Then:

```lean
theorem preΨ'_derivative_ne_zero_at_root
    {n : ℕ} (hn : (n : k) ≠ 0)
    {x₀ : k}
    (hx : (W.preΨ' n).eval x₀ = 0) :
    ((W.preΨ' n).derivative).eval x₀ ≠ 0 := by
  rcases
    (preΨ'_root_iff_exists_non2_kernel_x (W := W) (n := n) (x₀ := x₀)).mp hx
    with ⟨y₀, hP, hker, hnon2⟩

  have horder :
      (Polynomial.evalAtX x₀ (W.preΨ' n)).order = 1 :=
    preΨ'_order_one_at_non2_kernel W hn hker hnon2

  exact
    ((Polynomial.order_evalAtX_one_iff x₀ (W.preΨ' n)).mp horder).2
```

---

## 4. Separable from derivative nonzero at roots

Mathlib defines `Polynomial.Separable p` as coprimality with its derivative, and provides `Polynomial.Separable.map`, `Polynomial.separable_map`, `Polynomial.Separable.eval₂_derivative_ne_zero`, root-count/separability lemmas, and `Polynomial.separable_iff_derivative_ne_zero`. citeturn114469view4turn114469view5

Add this helper if the exact shape is not already present in your checkout:

```lean
namespace Polynomial

variable {K : Type*} [Field K]

theorem separable_of_derivative_ne_zero_at_roots
    {p : Polynomial K}
    (hp0 : p ≠ 0)
    (hderiv : ∀ x : K, p.eval x = 0 → p.derivative.eval x ≠ 0)
    (hsplit : p.Splits (RingHom.id K)) :
    p.Separable := by
  -- Proof route:
  -- 1. `p.Separable ↔ p.roots.Nodup` under `hsplit`.
  -- 2. repeated root implies derivative vanishes at that root.
  -- Mathlib has `nodup_roots`, `count_roots_le_one`,
  -- `rootMultiplicity_le_one_of_separable` in the forward direction;
  -- if reverse lemma is missing, prove it through gcd/coprimality.
  rw [Polynomial.separable_iff_derivative_ne_zero]
  exact hderiv
```

Depending on the exact Mathlib version, the last proof may instead be:

```lean
  rw [Polynomial.separable_def']
  -- prove `IsCoprime p p.derivative`
  -- by contradiction: a nonconstant gcd has a root in the splitting field,
  -- contradicting `hderiv`.
```

Now the final theorem:

```lean
theorem preΨ'_separable_of_natCast_ne_zero
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  classical

  -- Easiest if `k` is already algebraically/separably closed:
  -- prove every root has nonzero derivative.
  by_cases hp0 : W.preΨ' n = 0
  · -- This should be impossible under `(n:k) ≠ 0`;
    -- use your degree/nonzero theorem from DivisionPolynomial.Degree.
    exact (preΨ'_ne_zero_of_natCast_ne_zero W hn hp0).elim

  -- If working over a general field, pass to algebraic closure and pull back.
  -- Mathlib has `Polynomial.separable_map` / `Polynomial.Separable.map`.
  rw [← Polynomial.separable_map (algebraMap k (AlgebraicClosure k))]

  -- Rewrite mapped division polynomial to the base-changed curve.
  rw [WeierstrassCurve.baseChange_preΨ']

  apply Polynomial.separable_of_derivative_ne_zero_at_roots
  · exact preΨ'_ne_zero_of_natCast_ne_zero
      (W := W.baseChange (AlgebraicClosure k))
      (n := n)
      (by
        -- image of `(n:k) ≠ 0` in algebraic closure
        exact map_natCast_ne_zero hn)
  · intro x hx
    exact preΨ'_derivative_ne_zero_at_root
      (W := W.baseChange (AlgebraicClosure k))
      (n := n)
      (by exact map_natCast_ne_zero hn)
      hx
  · exact Polynomial.splits_of_isAlgClosed _
```

If your theorem is only needed over `[IsSepClosed k]`, replace `AlgebraicClosure k` by `k` and use the separably-closed splitting lemma for separable polynomials only after proving separability is circular, so algebraic closure is cleaner for the proof of separability itself.

---

## Minimal SEAM1 file plan

### File `Seam1/DualFirstJet.lean`

```lean
def tangentOPoint
theorem tangentOPoint_equation

axiom tangentOPoint_add_regularized

theorem tangentOPoint_nsmul_formula
theorem d_nsmul_at_O
```

Do **not** try raw `Projective.addX/addY/addZ` here. They vanish at `(O,O)` before cancellation.

### File `Seam1/LocalOrder.lean`

```lean
def Polynomial.evalAtX
lemma Polynomial.evalAtX_constCoeff
lemma Polynomial.order_evalAtX_zero_of_eval_ne_zero
lemma Polynomial.order_evalAtX_one_iff

axiom xCoord_nsmul_pole_order_two_at_non2_kernel
axiom ΨSq_order_two_at_non2_kernel

theorem preΨ'_order_one_at_non2_kernel
```

The axiom `ΨSq_order_two_at_non2_kernel` is the exact place where DualNumber first-jet + SEAM2 local x-coordinate formula meet.

### File `Seam1/Separable.lean`

```lean
theorem preΨ'_derivative_ne_zero_at_root
theorem preΨ'_separable_of_natCast_ne_zero
```

---

## Honest hard piece

The hardest missing primitive is:

```lean
axiom ΨSq_order_two_at_non2_kernel
    {n : ℕ} (hn : (n : k) ≠ 0)
    {x₀ y₀ : k}
    {hP : W.toAffine.Nonsingular x₀ y₀}
    (hker :
      n • (W.toAffine.Point.some x₀ y₀ hP : W.toAffine.Point) = 0)
    (hnon2 :
      2 • (W.toAffine.Point.some x₀ y₀ hP : W.toAffine.Point) ≠ 0) :
    (Polynomial.evalAtX x₀ (W.ΨSq (n : ℤ))).order = 2
```

The DualNumber first-jet proves only the **linear coefficient** of `[n]`. It does not by itself prove the full `PowerSeries.order` statement. To get the order statement, you still need a local formal-neighborhood theorem: nonzero differential of `[n]` at a kernel point plus the fact that `x` has a double pole at `O`.

Once `ΨSq_order_two_at_non2_kernel` exists, the rest of `preΨ'_separable_of_natCast_ne_zero` is a manageable `PowerSeries.order_mul/order_pow` plus polynomial derivative argument.
