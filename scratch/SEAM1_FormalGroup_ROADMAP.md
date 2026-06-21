[ask-gpt dm1 tid=7e98fb3b +0s] dispatched, waiting for answer
[ask-gpt dm1 tid=7e98fb3b +90s] waiting (status=processing)
[ask-gpt dm1 tid=7e98fb3b +180s] waiting (status=processing)
[ask-gpt dm1 tid=7e98fb3b +270s] waiting (status=processing)
[ask-gpt dm1 tid=7e98fb3b +360s] waiting (status=processing)
[ask-gpt dm1 tid=7e98fb3b +445s] terminal: status=completed
## Verdict

For `preΨ'_separable_of_natCast_ne_zero`, the **formal-group direction is mathematically right**, but the leanest implementation is **not** to start by proving a full bundled

```lean
def WeierstrassCurve.formalGroup : FormalGroup k
```

with associativity. That is reusable but large.

The shortest path to your seam is:

```text
generic formal-group linear coefficient lemma
+ local formal parameter/order bridge for x([n]P)
+ x-coordinate division-polynomial formula Φ/ΨSq
⇒ roots of preΨ' are simple
⇒ preΨ' is Separable
```

The full Weierstrass formal group law can be layered later. For this seam, you only need the **first-order/valuation consequence** of the formal group:

\[
[n](T)=nT+O(T^2).
\]

Mathlib has generic `FormalGroup`, `MvPowerSeries`, `PowerSeries.subst`, and `PowerSeries.order`, but no Weierstrass/elliptic formal group instance. The elliptic curve files have affine and projective group-law formulas, and division polynomials `preΨ'`, `ΨSq`, `Φ`, with `map_...`/`baseChange_...` lemmas, but not the formal-local bridge you need. citeturn805944view0turn678543view2turn295167view0turn901132view0

---

# 1. Weierstrass formal group: what exists and what you must build

Mathlib’s generic formal group law is:

```lean
structure FormalGroup (R : Type*) [CommRing R] where
  toPowerSeries : MvPowerSeries (Fin 2) R
  zero_constantCoeff : MvPowerSeries.constantCoeff toPowerSeries = 0
  lin_coeff_X :
    MvPowerSeries.coeff (Finsupp.single 0 1) toPowerSeries = 1
  lin_coeff_Y :
    MvPowerSeries.coeff (Finsupp.single 1 1) toPowerSeries = 1
  assoc : ...
```

It also has:

```lean
FormalGroup.IsComm
FormalGroup.Point
FormalGroup.instAddPoint
FormalGroup.ₐ
FormalGroup.ₘ
FormalGroup.map
```

But this is only the **abstract** formal-group API; there is no `WeierstrassCurve.formalGroup` in the elliptic-curve namespace. The docs explicitly show `FormalGroup.toPowerSeries`, the two linear coefficient fields, associativity, additive/multiplicative examples, and coefficientwise map. citeturn805944view0

For a Weierstrass curve

\[
y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6,
\]

use the standard local parameters at \(O\):

\[
t=-x/y,\qquad s=-1/y.
\]

Then

\[
x=t/s,\qquad y=-1/s,
\]

and \(s=s(t)\) is the unique power series satisfying

\[
s=t^3+a_1ts+a_2t^2s+a_3s^2+a_4ts^2+a_6s^3.
\]

In Lean, first build:

```lean
namespace WeierstrassCurve

open PowerSeries MvPowerSeries

variable {R : Type*} [CommRing R]

noncomputable def sigma (W : WeierstrassCurve R) : PowerSeries R :=
  -- unique σ satisfying:
  -- σ = X^3 + C W.a₁ * X * σ + C W.a₂ * X^2 * σ
  --       + C W.a₃ * σ^2 + C W.a₄ * X * σ^2 + C W.a₆ * σ^3
  sorry

theorem sigma_eq (W : WeierstrassCurve R) :
    W.sigma =
      PowerSeries.X ^ 3
      + PowerSeries.C W.a₁ * PowerSeries.X * W.sigma
      + PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * W.sigma
      + PowerSeries.C W.a₃ * W.sigma ^ 2
      + PowerSeries.C W.a₄ * PowerSeries.X * W.sigma ^ 2
      + PowerSeries.C W.a₆ * W.sigma ^ 3 := by
  sorry

theorem sigma_coeff_zero (W : WeierstrassCurve R) :
    PowerSeries.coeff 0 W.sigma = 0 := by
  sorry

theorem sigma_coeff_one (W : WeierstrassCurve R) :
    PowerSeries.coeff 1 W.sigma = 0 := by
  sorry

theorem sigma_coeff_two (W : WeierstrassCurve R) :
    PowerSeries.coeff 2 W.sigma = 0 := by
  sorry

theorem sigma_coeff_three (W : WeierstrassCurve R) :
    PowerSeries.coeff 3 W.sigma = 1 := by
  sorry
```

The construction of `sigma` is not currently supported by a canned “solve implicit power-series equation” theorem. The best Lean construction is coefficient recursion: the coefficient of `s` at degree `N` depends only on lower coefficients, because `s` starts in degree `3`. You will use `PowerSeries.coeff`, `PowerSeries.ext`, `PowerSeries.monomial`, `PowerSeries.coeff_mul`, and `PowerSeries.order`. Mathlib has the basic coefficient and extensionality API for power series, and `PowerSeries.order` has the expected order lemmas such as `order_mul` over domains. citeturn678543view0turn177737view0

Now define the formal point near \(O\) in projective coordinates. Since

\[
t=-X/Y,\qquad s=-Z/Y,
\]

you may use representative

\[
[-t:1:-s(t)].
\]

```lean
noncomputable def formalPointO (W : WeierstrassCurve R) :
    Fin 3 → PowerSeries R
| 0 => -PowerSeries.X
| 1 => 1
| 2 => -W.sigma

theorem formalPointO_equation (W : WeierstrassCurve R) :
    W.toProjective.Equation W.formalPointO := by
  -- unfold projective equation;
  -- use sigma_eq;
  -- ring
  sorry
```

For the full binary formal group law, you need a power series

\[
F_W(T_1,T_2)
\]

such that

\[
P(F_W(T_1,T_2))=P(T_1)+P(T_2).
\]

Mathlib has projective `addX`, `addY`, `addZ` as explicit homogeneous formulas, plus base-change lemmas. But it does **not** have the cancellation/local-chart theorem saying that applying those formulas to the formal point produces a representative whose `-X/Y` ratio is a genuine two-variable power series. The projective formula docs show `addX/addY/addZ`, and explicitly say these are large homogeneous formulas for point addition. citeturn295167view0turn295167view1

The full skeleton is:

```lean
abbrev FPS2 (R : Type*) [CommRing R] :=
  MvPowerSeries (Fin 2) R

noncomputable def substSigmaLeft (W : WeierstrassCurve R) : FPS2 R :=
  PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) W.sigma

noncomputable def substSigmaRight (W : WeierstrassCurve R) : FPS2 R :=
  PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) W.sigma

noncomputable def formalPointLeft (W : WeierstrassCurve R) : Fin 3 → FPS2 R
| 0 => -MvPowerSeries.X (0 : Fin 2)
| 1 => 1
| 2 => -W.substSigmaLeft

noncomputable def formalPointRight (W : WeierstrassCurve R) : Fin 3 → FPS2 R
| 0 => -MvPowerSeries.X (1 : Fin 2)
| 1 => 1
| 2 => -W.substSigmaRight

noncomputable def formalAddSeries (W : WeierstrassCurve R) : FPS2 R :=
  -- morally:
  -- - addX(P₁,P₂) / addY(P₁,P₂)
  -- after cancelling the common factor and proving the denominator is a unit
  sorry

noncomputable def formalGroup (W : WeierstrassCurve R) :
    FormalGroup R :=
{ toPowerSeries := W.formalAddSeries
  zero_constantCoeff := by sorry
  lin_coeff_X := by sorry
  lin_coeff_Y := by sorry
  assoc := by
    -- hardest part of the full construction
    sorry }
```

The `assoc` proof is the bulk if you insist on a bundled `FormalGroup`. You either prove it by comparing formal points and using the elliptic group law, or by a uniqueness theorem for the formal solution of the collinearity equations. Both routes require substantial local algebra.

For the separability seam, do **not** wait for this full structure.

---

# 2. Generic linear coefficient of formal `[n]`

This part is clean and should be developed generically for Mathlib’s `FormalGroup`.

Define formal addition of one-variable power series by substituting into the bivariate law:

```lean
namespace FormalGroup

open PowerSeries MvPowerSeries

variable {R : Type*} [CommRing R]

noncomputable def addSeries
    (F : FormalGroup R) (f g : PowerSeries R) : PowerSeries R :=
  MvPowerSeries.subst
    (fun i : Fin 2 =>
      Fin.cases f (fun _ => g) i)
    F.toPowerSeries

noncomputable def formalNsmul
    (F : FormalGroup R) : ℕ → PowerSeries R
| 0 => 0
| n + 1 => F.addSeries (formalNsmul F n) PowerSeries.X
```

Then prove the generic linear-coefficient lemma:

```lean
theorem addSeries_coeff_one
    (F : FormalGroup R)
    {f g : PowerSeries R}
    (hf0 : PowerSeries.coeff 0 f = 0)
    (hg0 : PowerSeries.coeff 0 g = 0) :
    PowerSeries.coeff 1 (F.addSeries f g)
      =
    PowerSeries.coeff 1 f + PowerSeries.coeff 1 g := by
  -- Use F.lin_coeff_X and F.lin_coeff_Y.
  -- All monomials of total degree ≥ 2 contribute zero to coefficient 1
  -- after substitution by series with zero constant term.
  sorry

theorem formalNsmul_coeff_zero
    (F : FormalGroup R) (n : ℕ) :
    PowerSeries.coeff 0 (F.formalNsmul n) = 0 := by
  induction n with
  | zero => simp [formalNsmul]
  | succ n ih =>
      -- needs constant term version of addSeries
      sorry

theorem formalNsmul_coeff_one
    (F : FormalGroup R) (n : ℕ) :
    PowerSeries.coeff 1 (F.formalNsmul n) = (n : R) := by
  induction n with
  | zero =>
      simp [formalNsmul]
  | succ n ih =>
      rw [formalNsmul]
      rw [addSeries_coeff_one F (formalNsmul_coeff_zero F n) (by simp)]
      simp [ih, Nat.cast_succ]
```

The hard step here is `addSeries_coeff_one`, not the induction. It is a coefficient-of-substitution lemma. Mathlib has `MvPowerSeries.subst`, `PowerSeries.subst`, `PowerSeries.coeff_subst`, and coefficient lemmas, but you will likely need a small custom lemma:

```lean
lemma coeff_one_subst_of_constantCoeff_zero
    (F : MvPowerSeries (Fin 2) R)
    {f g : PowerSeries R}
    (hf0 : PowerSeries.coeff 0 f = 0)
    (hg0 : PowerSeries.coeff 0 g = 0) :
    PowerSeries.coeff 1
      (MvPowerSeries.subst
        (fun i : Fin 2 => Fin.cases f (fun _ => g) i) F)
      =
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) F
      * PowerSeries.coeff 1 f
    + MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) F
      * PowerSeries.coeff 1 g := by
  sorry
```

Then `FormalGroup.formalNsmul_coeff_one` is reusable for every future formal group. Mathlib’s `FormalGroup` stores exactly the two linear coefficient fields you need. citeturn805944view0

---

# 3. Bridge from formal `[n]'(0)=n` to `preΨ'` separability

This is the real seam. The right bridge is **not** literally “étale schemes” in Lean. The leanest bridge is an order-of-power-series statement using the `x`-coordinate formula for multiplication.

You want this chain:

```text
formalNsmul_coeff_one = n ≠ 0
⇒ t([n]R) has order 1 near O
⇒ x([n]R) has pole order 2 near kernel points
⇒ ΨSq_n has zero order 2 at non-2 n-torsion points
⇒ preΨ'_n has zero order 1
⇒ derivative of preΨ'_n is nonzero at every root
⇒ preΨ'_n.Separable
```

Mathlib defines `Polynomial.Separable p` as `IsCoprime p p.derivative`, and has `Polynomial.separable_map`, `Polynomial.nodup_roots_iff_of_splits`, and derivative-at-root lemmas in the separability file. citeturn814551view0turn948497view0

## 3.1 Local order statement at `O`

First package the consequence of the formal group:

```lean
theorem formalNsmul_order_one
    {k : Type*} [Field k]
    (F : FormalGroup k) {n : ℕ}
    (hn : (n : k) ≠ 0) :
    PowerSeries.order (F.formalNsmul n) = 1 := by
  -- coeff 0 = 0, coeff 1 = n ≠ 0
  rw [PowerSeries.order_eq]
  constructor
  · intro i hi
    -- i = 1
    subst hi
    simpa [FormalGroup.formalNsmul_coeff_one] using hn
  · intro i hi
    -- i < 1, so i = 0
    have hi0 : i = 0 := by omega
    subst hi0
    exact FormalGroup.formalNsmul_coeff_zero F n
```

The exact proof syntax around `ℕ∞` may need adjustment, but the lemma shape is right. `PowerSeries.order_eq` is the relevant API: it characterizes the order by the first nonzero coefficient. citeturn177737view0

For the Weierstrass formal point,

\[
x(t)=t/s(t).
\]

Since \(s(t)=t^3+\cdots\),

\[
x(t)=t^{-2}\cdot \text{unit}.
\]

You should avoid Laurent series by phrasing the statement as an order identity for the denominator after substituting `[n]`.

```lean
theorem sigma_comp_formalNsmul_order_three
    {k : Type*} [Field k]
    (W : WeierstrassCurve k)
    {n : ℕ} (hn : (n : k) ≠ 0) :
    PowerSeries.order
      (PowerSeries.subst (W.formalGroup.formalNsmul n) W.sigma)
      = 3 := by
  -- sigma has order 3, formalNsmul has order 1.
  -- Need order_subst/order composition lemma.
  sorry
```

You may need to add:

```lean
lemma PowerSeries.order_subst_of_order_one
    {k : Type*} [Field k]
    {f g : PowerSeries k}
    (hf : f.order = d)
    (hg : g.order = 1) :
    (PowerSeries.subst g f).order = d := by
  sorry
```

Mathlib has substitution and order lemmas, but the exact “order of composition when inner order is one” lemma may not already exist. Power-series substitution and order APIs are present; the composition/order bridge is likely yours. citeturn865421view0turn177737view0

## 3.2 Use the `x([n]P)` division-polynomial formula

This is the crucial non-formal-group input.

You need a theorem of this shape, either already in `flt-ai` or to add next to the division-polynomial correctness work:

```lean
theorem xCoord_nsmul_eq_Φ_div_ΨSq
    {k : Type*} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℤ)
    {P : (W ⧸ k).Point}
    (hden : evalX W (W.ΨSq n) P ≠ 0) :
    xCoord (n • P)
      =
    evalX W (W.Φ n) P / evalX W (W.ΨSq n) P := by
  sorry
```

For the local-order proof you need the stronger pullback version:

```lean
theorem pullback_xCoord_nsmul_eq_Φ_div_ΨSq
    {k : Type*} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℕ)
    (Pser : FormalPointNear W) :
    -- in FractionRing (PowerSeries k):
    xSeries (n • Pser)
      =
    evalPolynomialSeries (W.Φ n) (xSeries Pser)
      / evalPolynomialSeries (W.ΨSq n) (xSeries Pser) := by
  sorry
```

Mathlib defines `Φ`, `ΨSq`, and `preΨ'`, and the docs state that these are designed so that `Φₙ` and `ΨSqₙ` are the univariate numerator/denominator data for the `x`-coordinate. But the docs do not expose a ready theorem giving the actual coordinate formula for `n • P`; if you do not already have it in `flt-ai`, this is a missing primitive. citeturn901132view0

Now let \(P\) be a non-2 \(n\)-torsion point. Since `[n]P=O`, the pullback `x([n](P + T))` has pole order exactly `2`, because near `O` we have \(x=t/s=t^{-2}\cdot \text{unit}\), and `[n](T)=nT+O(T^2)\).

Lean target:

```lean
theorem xCoord_nsmul_pole_order_two_at_kernel
    {k : Type*} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0)
    {P : (W ⧸ k).Point}
    (hP : n • P = 0) :
    poleOrderAt W P (fun R => xCoord (n • R)) = 2 := by
  -- formal group at O + translation by P
  sorry
```

This theorem is where “étale at `O`, then by translation étale at every kernel point” becomes a concrete local order statement. There is no Mathlib scheme-theoretic étaleness path here; this local theorem is the leanest substitute.

Then compare with the division-polynomial formula:

\[
x([n]R)=\frac{\Phi_n(x(R))}{\PsiSq_n(x(R))}.
\]

At a non-2-torsion kernel point, `Ψ₂Sq(x(P)) ≠ 0`, and

\[
\PsiSq_n=
\begin{cases}
(\operatorname{preΨ'}_n)^2, & n \text{ odd},\\
(\operatorname{preΨ'}_n)^2\Psi_2^2, & n \text{ even}.
\end{cases}
\]

So if the denominator has order `2`, then `preΨ'` has order `1`.

```lean
theorem preΨ'_order_one_at_non2_kernel
    {k : Type*} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0)
    {P : (W ⧸ k).Point}
    (hP : n • P = 0)
    (hP2 : 2 • P ≠ 0)
    (hPaff : P ≠ 0) :
    PowerSeries.order
      (evalPolynomialSeries
        (W.preΨ' n)
        (localXMinusXCoord W P))
      = 1 := by
  -- use:
  -- xCoord_nsmul_pole_order_two_at_kernel
  -- pullback_xCoord_nsmul_eq_Φ_div_ΨSq
  -- ΨSq_odd / ΨSq_even
  -- Ψ₂Sq nonzero at non-2 point
  -- PowerSeries.order_mul and order_pow
  sorry
```

Mathlib has `PowerSeries.order_mul`, `PowerSeries.order_pow`, and `PowerSeries.order_X`, which are exactly the order tools you want over a domain. citeturn177737view0

## 3.3 Convert order one to derivative nonzero

Add this polynomial lemma:

```lean
theorem Polynomial.order_eval_X_add_C_eq_one_iff
    {k : Type*} [Field k]
    (p : Polynomial k) (x₀ : k) :
    PowerSeries.order
      (Polynomial.aeval (PowerSeries.C x₀ + PowerSeries.X) p)
      = 1
    ↔
    p.eval x₀ = 0 ∧ p.derivative.eval x₀ ≠ 0 := by
  -- coeff 0 is p.eval x₀
  -- coeff 1 is p.derivative.eval x₀
  sorry
```

Then:

```lean
theorem preΨ'_derivative_ne_zero_at_root
    {k : Type*} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0)
    {x : k}
    (hx : (W.preΨ' n).eval x = 0) :
    ((W.preΨ' n).derivative).eval x ≠ 0 := by
  -- obtain a non-2 n-torsion point P over x
  -- from the root-characterization theorem already used in n_torsion_card
  rcases preΨ'_root_iff_exists_non2_nTorsion_x.mp hx with
    ⟨P, hPaff, hPn, hP2, hxP⟩

  have horder :
      PowerSeries.order
        (Polynomial.aeval (PowerSeries.C x + PowerSeries.X) (W.preΨ' n))
        = 1 := by
    -- rewrite x as xCoord P and use preΨ'_order_one_at_non2_kernel
    simpa [hxP] using
      preΨ'_order_one_at_non2_kernel W hn hPn hP2 hPaff

  exact
    (Polynomial.order_eval_X_add_C_eq_one_iff
      (W.preΨ' n) x).mp horder |>.2
```

The root-characterization theorem is another nontrivial dependency:

```lean
theorem preΨ'_root_iff_exists_non2_nTorsion_x
    {k : Type*} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} {x : k} :
    (W.preΨ' n).eval x = 0 ↔
      ∃ P : (W ⧸ k).Point,
        P ≠ 0 ∧ n • P = 0 ∧ 2 • P ≠ 0 ∧ xCoord P = x := by
  sorry
```

You said your `n_torsion_card` proof is done modulo separability, so you may already have essentially this theorem. If not, it is an equal-sized seam.

## 3.4 Final separability theorem

Use a splitting field or algebraic closure and `Polynomial.separable_map`.

```lean
theorem preΨ'_separable_of_natCast_ne_zero
    {k : Type*} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  -- It is often easier to prove after mapping to a splitting field K.
  -- Use Polynomial.separable_map to reduce to K.
  rw [← Polynomial.separable_map (algebraMap k (AlgebraicClosure k))]

  -- rewrite map of preΨ' as baseChange_preΨ'
  rw [WeierstrassCurve.baseChange_preΨ']

  -- prove separability over algebraically closed/splitting field by:
  -- every root has derivative nonzero
  apply Polynomial.separable_of_derivative_ne_zero_at_roots
  intro x hx
  exact preΨ'_derivative_ne_zero_at_root
    (W := W.baseChange (AlgebraicClosure k))
    (by simpa using map_natCast_ne_zero hn)
    hx
```

`Polynomial.separable_map` is an iff for mapping from a field into a nontrivial commutative semiring, and Mathlib has root-count/separability lemmas such as `nodup_roots_iff_of_splits`. You may need to add `Polynomial.separable_of_derivative_ne_zero_at_roots` if no exact theorem matches. citeturn948497view0

A useful implementation lemma:

```lean
theorem Polynomial.separable_of_derivative_ne_zero_at_roots
    {k : Type*} [Field k]
    {p : Polynomial k}
    (hsplit : p.Splits (RingHom.id k))
    (hderiv : ∀ x : k, p.eval x = 0 → p.derivative.eval x ≠ 0) :
    p.Separable := by
  -- Use Polynomial.nodup_roots_iff_of_splits.
  -- Show p.roots.Nodup by contradiction:
  -- duplicate root ⇒ derivative vanishes at that root.
  sorry
```

---

# 4. Shortcut: first jet instead of full formal group

There is a **much smaller** shortcut if your only immediate goal is `preΨ'_separable`.

Use dual numbers to prove only the tangent statement

\[
d[n]_O = n.
\]

Mathlib has `DualNumber R`, notation `R[ε]`, and `DualNumber.eps`; it is implemented as `TrivSqZeroExt R R`. citeturn720251search0

At \(O=[0:1:0]\), the infinitesimal point with tangent coefficient `a : k` is

\[
P_a=[-a\varepsilon:1:0].
\]

Since \(\varepsilon^2=0\), this lies on the projective Weierstrass curve.

Define:

```lean
import Mathlib.Algebra.DualNumber

open scoped DualNumber

namespace WeierstrassCurve

variable {k : Type*} [Field k]

def tangentOPoint
    (W : WeierstrassCurve k) (a : k) :
    Fin 3 → DualNumber k
| 0 => - algebraMap k (DualNumber k) a * DualNumber.eps
| 1 => 1
| 2 => 0

theorem tangentOPoint_equation
    (W : WeierstrassCurve k) (a : k) :
    (W.baseChange (DualNumber k)).toProjective.Equation
      (W.tangentOPoint a) := by
  -- ε² = 0, hence ε³ = 0
  simp [tangentOPoint]
  ring_nf
```

Then prove first-order addition:

```lean
theorem tangentOPoint_add_formula
    (W : WeierstrassCurve k) (a b : k) :
    projectiveAddFormula W (W.tangentOPoint a) (W.tangentOPoint b)
      ~ W.tangentOPoint (a + b) := by
  -- Use Projective.addX/addY/addZ formulas over DualNumber k.
  -- No field structure on DualNumber is needed if you stay at formula level.
  sorry
```

Then:

```lean
theorem tangentOPoint_nsmul_formula
    (W : WeierstrassCurve k) (n : ℕ) (a : k) :
    projectiveNsmulFormula W n (W.tangentOPoint a)
      ~ W.tangentOPoint ((n : k) * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
      -- use tangentOPoint_add_formula
      sorry
```

This gives \(d[n]_O(a)=na\) without constructing `sigma`, without building a full two-variable `formalAddSeries`, and without proving associativity of a `FormalGroup`.

The catch: this only proves the **first-order tangent statement**. You still need the local-order bridge from `[n]` to `preΨ'`. But it avoids the largest up-front construction.

For the seam, this is the best engineering route:

```text
DualNumber tangent calculation
⇒ d[n]_O = n
⇒ local order of x([n]) at kernel = 2
⇒ preΨ' roots simple
```

Keep the full `WeierstrassCurve.formalGroup` as a later reusable library artifact.

---

# 5. Minimal file architecture

## File A: `FormalGroup/LinearCoeff.lean`

Generic, independent of elliptic curves.

```lean
namespace FormalGroup

noncomputable def addSeries
    (F : FormalGroup R) (f g : PowerSeries R) : PowerSeries R := ...

noncomputable def formalNsmul
    (F : FormalGroup R) : ℕ → PowerSeries R := ...

theorem addSeries_coeff_one
    (F : FormalGroup R)
    {f g : PowerSeries R}
    (hf0 : PowerSeries.coeff 0 f = 0)
    (hg0 : PowerSeries.coeff 0 g = 0) :
    PowerSeries.coeff 1 (F.addSeries f g)
      =
    PowerSeries.coeff 1 f + PowerSeries.coeff 1 g := by
  sorry

theorem formalNsmul_coeff_one
    (F : FormalGroup R) (n : ℕ) :
    PowerSeries.coeff 1 (F.formalNsmul n) = (n : R) := by
  sorry

theorem formalNsmul_order_one
    {k : Type*} [Field k]
    (F : FormalGroup k)
    {n : ℕ} (hn : (n : k) ≠ 0) :
    PowerSeries.order (F.formalNsmul n) = 1 := by
  sorry
```

## File B: `EllipticCurve/Formal/Sigma.lean`

If doing full formal group:

```lean
noncomputable def WeierstrassCurve.sigma
    (W : WeierstrassCurve R) : PowerSeries R := sorry

theorem WeierstrassCurve.sigma_eq ... := by sorry
theorem WeierstrassCurve.sigma_order_three ... := by sorry
```

If using shortcut, skip this initially.

## File C: `EllipticCurve/Formal/FirstJet.lean`

Recommended for the seam.

```lean
def tangentOPoint
    (W : WeierstrassCurve k) (a : k) :
    Fin 3 → DualNumber k := ...

theorem tangentOPoint_equation ... := by sorry

theorem tangentOPoint_add_formula
    (W : WeierstrassCurve k) (a b : k) :
    projectiveAddFormula W (tangentOPoint W a) (tangentOPoint W b)
      ~ tangentOPoint W (a + b) := by
  sorry

theorem tangentOPoint_nsmul_formula
    (W : WeierstrassCurve k) (n : ℕ) (a : k) :
    projectiveNsmulFormula W n (tangentOPoint W a)
      ~ tangentOPoint W ((n : k) * a) := by
  sorry
```

## File D: `EllipticCurve/DivisionPolynomial/LocalOrder.lean`

This is the bridge.

```lean
theorem xCoord_nsmul_eq_Φ_div_ΨSq ... := by
  sorry

theorem xCoord_nsmul_pole_order_two_at_kernel
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0)
    {P : (W ⧸ k).Point}
    (hP : n • P = 0) :
    poleOrderAt W P (fun R => xCoord (n • R)) = 2 := by
  sorry

theorem preΨ'_order_one_at_non2_kernel
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0)
    {P : (W ⧸ k).Point}
    (hP : n • P = 0)
    (hP2 : 2 • P ≠ 0)
    (hPaff : P ≠ 0) :
    PowerSeries.order
      (Polynomial.aeval
        (PowerSeries.C (xCoord P) + PowerSeries.X)
        (W.preΨ' n))
      = 1 := by
  sorry
```

## File E: `EllipticCurve/DivisionPolynomial/Separable.lean`

```lean
theorem Polynomial.order_eval_X_add_C_eq_one_iff
    {k : Type*} [Field k]
    (p : Polynomial k) (x₀ : k) :
    PowerSeries.order
      (Polynomial.aeval (PowerSeries.C x₀ + PowerSeries.X) p)
      = 1
    ↔
    p.eval x₀ = 0 ∧ p.derivative.eval x₀ ≠ 0 := by
  sorry

theorem preΨ'_derivative_ne_zero_at_root
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0)
    {x : k}
    (hx : (W.preΨ' n).eval x = 0) :
    ((W.preΨ' n).derivative).eval x ≠ 0 := by
  sorry

theorem preΨ'_separable_of_natCast_ne_zero
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  sorry
```

---

# 6. Honest scope and hardest sub-step

The generic lemma

```lean
FormalGroup.formalNsmul_coeff_one
```

is short and reusable. Expect tens of lines plus one substitution-coefficient lemma.

The full construction

```lean
WeierstrassCurve.formalGroup : FormalGroup R
```

is the bulk. The hard parts are:

```lean
WeierstrassCurve.sigma
WeierstrassCurve.formalAddSeries
WeierstrassCurve.formalGroup.assoc
```

This is not a small patch. It is likely thousands of lines if done cleanly.

For the **specific separability seam**, the hardest primitive is not the generic formal-group lemma. It is this local bridge:

```lean
theorem preΨ'_order_one_at_non2_kernel
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0)
    {P : (W ⧸ k).Point}
    (hP : n • P = 0)
    (hP2 : 2 • P ≠ 0)
    (hPaff : P ≠ 0) :
    PowerSeries.order
      (Polynomial.aeval
        (PowerSeries.C (xCoord P) + PowerSeries.X)
        (W.preΨ' n))
      = 1
```

That theorem packages the real geometry:

```text
[n] has nonzero tangent map
+ x has a double pole at O
+ ΨSq is the denominator of x([n])
+ ΨSq = preΨ'^2 times a nonvanishing 2-torsion factor
⇒ preΨ' has simple zeros.
```

If your repo already has the `x([n]) = Φ/ΨSq` correctness theorem and the root-characterization of `preΨ'`, then the formal-group separability route is tractable. Without those, `preΨ'_separable` is not just a formal-group task; it also needs the missing division-polynomial correctness/local-order layer.

My recommendation: implement the **DualNumber first-jet shortcut** first to discharge the seam, while designing the full `WeierstrassCurve.formalGroup` as a later reusable development.
