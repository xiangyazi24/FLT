# Q597 / dm4 — FormalGroup API, `[n]` coefficient, and division-polynomial separability

## Executive answer

At the Mathlib revision pinned by this repo, the full chain is **not** already present.

Answers to the three API questions:

1. **Does Mathlib's `FormalGroup` have a formal multiplication-by-`n` map?**
   No. `Mathlib/RingTheory/FormalGroup/Basic.lean` defines the structure `FormalGroup`, a commutativity predicate, a `Point` type synonym, and an `Add` instance on `F.Point σ` by substitution. It does **not** define `Zero`, `SMul`, `Inv`, `nsmul`, or a named `formalNsmul`. The file even has:

   ```lean
   /- TODO : Zero, SMul, Inv instance. -/
   ```

2. **Is there a theorem that the first-order coefficient of `[n]_F` is `n`?**
   No, not in `RingTheory/FormalGroup/Basic.lean`. But this is a small local lemma you can build yourself once you have `F.zero_constantCoeff`, `F.lin_coeff_X`, and `F.lin_coeff_Y`.

3. **Does Mathlib connect this formal group to division polynomials / `preΨ'` separability?**
   No. `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` defines `preΨ'`, `preΨ`, `ΨSq`, `Ψ`, `Φ`, `ψ`, and `φ`, and proves some coordinate-ring congruences such as `mk_ψ` and `mk_φ`. I did not find a theorem connecting the Weierstrass formal group to these division polynomials, nor a theorem that `preΨ' n` is separable when `(n : K) ≠ 0`.

So the minimal path is:

```text
A. Build your own recursive formal `[n]` power series and prove coeff₁ = n.
B. Build the Weierstrass-local-coordinate bridge saying the projective group law near O is this formal group.
C. Build the division-polynomial correctness bridge identifying zeros of `preΨ' n` with nonzero n-torsion x-coordinates.
D. Use the tangent nonvanishing from A+B to rule out multiple roots of `preΨ' n` when `(n : K) ≠ 0`.
```

The easy part is A. The hard part is B+C, especially C.

## What Mathlib currently has

The repo pins Mathlib at:

```toml
rev = "96fd0fff3b8837985ae21dd02e712cb5df72ec05"
```

### `FormalGroup`

At that revision, `Mathlib/RingTheory/FormalGroup/Basic.lean` defines:

```lean
structure FormalGroup where
  toPowerSeries : MvPowerSeries (Fin 2) R
  zero_constantCoeff : toPowerSeries.constantCoeff = 0
  lin_coeff_X : toPowerSeries.coeff (single 0 1) = 1
  lin_coeff_Y : toPowerSeries.coeff (single 1 1) = 1
  assoc : toPowerSeries.subst ![toPowerSeries.subst ![Y₀, Y₁], Y₂]
    = toPowerSeries.subst ![Y₀, toPowerSeries.subst ![Y₁, Y₂]] (S := R)
```

It also defines:

```lean
class FormalGroup.IsComm (F : FormalGroup R) : Prop where
  comm : F = (F : MvPowerSeries (Fin 2) R).subst ![X₁, X₀]

def FormalGroup.Point (F : FormalGroup R) (σ : Type) := MvPowerSeries σ R

instance : Add (F.Point σ) where
  add x y := (F : MvPowerSeries (Fin 2) R).subst ![x, y]
```

But there is no `FormalGroup.nsmul`, `FormalGroup.formalNsmul`, or theorem about the linear coefficient of `[n]`.

### Division polynomials

`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` defines:

```lean
noncomputable def preΨ' (n : ℕ) : R[X] :=
  preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n

noncomputable def preΨ (n : ℤ) : R[X] :=
  preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n

protected noncomputable def Ψ (n : ℤ) : R[X][Y] :=
  C (W.preΨ n) * if Even n then W.ψ₂ else 1

protected noncomputable def Φ (n : ℤ) : R[X] :=
  X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) * if Even n then 1 else W.Ψ₂Sq

protected noncomputable def ψ (n : ℤ) : R[X][Y] :=
  normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

protected noncomputable def φ (n : ℤ) : R[X][Y] :=
  C X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)
```

It also proves coordinate-ring congruences:

```lean
lemma Affine.CoordinateRing.mk_ψ (n : ℤ) : mk W (W.ψ n) = mk W (W.Ψ n)
lemma Affine.CoordinateRing.mk_φ (n : ℤ) : mk W (W.φ n) = mk W (C <| W.Φ n)
```

But there is no built-in theorem of the form:

```lean
[n]P = [φₙ(P) : ωₙ(P) : ψₙ(P)]
```

nor a theorem:

```lean
(W.preΨ' n).Separable
```

under `(n : K) ≠ 0`.

### `Polynomial.Separable`

Mathlib does have the general separability notion:

```lean
def Polynomial.Separable (f : R[X]) : Prop :=
  IsCoprime f (derivative f)
```

and useful downstream lemmas such as:

```lean
theorem Polynomial.Separable.eval₂_derivative_ne_zero
    (h : p.Separable) (hx : p.eval₂ f x = 0) :
    (derivative p).eval₂ f x ≠ 0
```

So the final target should probably be phrased using `Polynomial.Separable`, but the elliptic-curve proof of separability is yours to build.

## Part A: build formal `[n]` yourself

Define recursive multiplication by `n` as a univariate power series. This does not require Mathlib to have a full formal-group `SMul` instance.

```lean
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution

open MvPowerSeries Finsupp

noncomputable section

namespace FormalGroup

variable {R : Type*} [CommRing R]

/-- The recursive formal multiplication-by-`n` series.
`formalNsmul F n` is `[n]_F(T)` as a univariate power series. -/
def formalNsmul (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => (F : MvPowerSeries (Fin 2) R).subst ![formalNsmul F n, PowerSeries.X]

end FormalGroup
```

This definition uses total `subst`. For proofs, you show the relevant substitutions are valid because both input series have zero constant term.

### Constant term lemma

```lean
namespace FormalGroup

variable {R : Type*} [CommRing R]

lemma formalNsmul_constantCoeff (F : FormalGroup R) :
    ∀ n, PowerSeries.constantCoeff (formalNsmul F n) = 0 := by
  intro n
  induction n with
  | zero => simp [formalNsmul]
  | succ n ih =>
      -- Use `MvPowerSeries.constantCoeff_subst_eq_zero`.
      -- Source has zero constant coefficient by `F.zero_constantCoeff`.
      -- Inputs have zero constant coefficients: IH and `PowerSeries.coeff_zero_X`.
      -- May need to unfold `PowerSeries.constantCoeff` as `MvPowerSeries.constantCoeff`.
      sorry

end FormalGroup
```

### The key linear-substitution lemma

Prove this once. It is the main algebraic work.

```lean
/-- If `G(X,Y) = X + Y + O(2)`, and `A(0)=B(0)=0`, then
`coeff₁ G(A(T),B(T)) = coeff₁ A + coeff₁ B`. -/
lemma coeff_one_subst_two_linear
    {R : Type*} [CommRing R]
    (G : MvPowerSeries (Fin 2) R)
    (hG0 : MvPowerSeries.constantCoeff G = 0)
    (hGX : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) G = 1)
    (hGY : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) G = 1)
    (A B : PowerSeries R)
    (hA0 : PowerSeries.constantCoeff A = 0)
    (hB0 : PowerSeries.constantCoeff B = 0) :
    PowerSeries.coeff 1 (G.subst ![A, B]) =
      PowerSeries.coeff 1 A + PowerSeries.coeff 1 B := by
  classical
  -- Proof outline:
  -- 1. Use `MvPowerSeries.coeff_subst` at exponent `single () 1`.
  -- 2. Only source monomials of total degree 0 or 1 can contribute to target degree 1.
  -- 3. Degree 0 contribution is killed by `hG0`.
  -- 4. Degree 1 monomials are `single 0 1` and `single 1 1`.
  -- 5. Use `hGX`, `hGY`, and `coeff_one_X`.
  -- 6. Degree ≥ 2 contributions vanish because `A` and `B` have zero constant coefficient.
  sorry
```

This lemma is independent of Weierstrass curves.

### First-order coefficient of `[n]_F`

Then the coefficient theorem is short:

```lean
namespace FormalGroup

variable {R : Type*} [CommRing R]

/-- `[n]_F(T) = n*T + O(T^2)`. -/
theorem formalNsmul_coeff_one (F : FormalGroup R) :
    ∀ n : ℕ, PowerSeries.coeff 1 (formalNsmul F n) = (n : R) := by
  intro n
  induction n with
  | zero => simp [formalNsmul]
  | succ n ih =>
      rw [formalNsmul]
      have hA0 := formalNsmul_constantCoeff F n
      have hB0 : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 := by simp
      rw [coeff_one_subst_two_linear
        (G := (F : MvPowerSeries (Fin 2) R))
        F.zero_constantCoeff F.lin_coeff_X F.lin_coeff_Y
        (formalNsmul F n) PowerSeries.X hA0 hB0]
      simp [ih, Nat.cast_succ]

end FormalGroup
```

This proves item 2 of your chain once `F : FormalGroup K` exists. Notice that commutativity is not needed for this coefficient theorem; associativity/commutativity are needed only to justify calling this recursive series *the* `[n]` map.

## Part B: what is still missing for division polynomials

The formal coefficient theorem says:

```text
[n]_F(T) = n*T + O(T^2).
```

This is a local statement at the identity `O`. To use it for `preΨ'`, you need at least two bridges.

### Bridge 1: Weierstrass formal group equals the elliptic curve group law near `O`

You need a theorem like:

```lean
/-- The local parameter of the projective group law equals the formal group law. -/
theorem localParameter_addXYZ_eq_formalGroupLaw
    (u v : PowerSeries K) :
    localT (Projective.addXYZ W (P u) (P v))
      = (W.formalGroup : MvPowerSeries (Fin 2) K).subst ![u, v] := by
  ...
```

or at least the iterated version:

```lean
theorem localParameter_nsmul_eq_formalNsmul
    (n : ℕ) :
    localT ([n] applied to P(T)) = FormalGroup.formalNsmul W.formalGroup n := by
  ...
```

This is not in Mathlib. This is essentially the bridge you are building in `FormalGroupW.lean`.

### Bridge 2: division-polynomial coordinates compute `[n]P`

You need a theorem that relates `ψ`, `φ`, and eventually `preΨ'` to the actual multiplication-by-`n` map. A typical target is:

```lean
/-- Projective coordinates for `[n]P`. Precise signs/powers depend on Mathlib's definitions. -/
theorem nsmul_projective_eq_division_polynomial_coords
    (P : W.Point) :
    projectiveRep (n • P) ~
      ![evalP (W.φ n), evalP (omega n), evalP (W.ψ n)] := by
  ...
```

Mathlib has `ψ` and `φ`, but the file explicitly still has:

```lean
* TODO: the bivariate polynomials `ωₙ`.
```

So the full coordinate formula is not packaged. For `preΨ'`, you may be able to avoid defining all of `ωₙ` if you only need the `Z`-coordinate/vanishing criterion, but you still need a correctness theorem:

```lean
W.preΨ' n x = 0  ↔  there is a point P over x with n • P = 0
```

with the usual parity and 2-torsion caveats.

## How to use the formal coefficient theorem for separability

The geometric argument is:

1. If `(n : K) ≠ 0`, then the tangent map of `[n]` at `O` is nonzero, because its local power series is `n*T + O(T^2)`.
2. By translation, the tangent map of `[n]` at any `n`-torsion point `P` is also nonzero:

   ```text
   [n](P + Q) = [n]P + [n]Q = [n]Q
   ```

   when `[n]P = O`.

3. A multiple root of the division polynomial would produce a nonzero tangent vector at an `n`-torsion point killed by the tangent map of `[n]`.
4. Contradiction.

In Lean, make this explicit with dual numbers or tangent-vector structures.

## Minimal theorem package to build

Here is the leanest dependency chain I would aim for.

### 1. Formal group coefficient package

```lean
namespace FormalGroup

def formalNsmul (F : FormalGroup K) : ℕ → PowerSeries K

theorem formalNsmul_constantCoeff
    (F : FormalGroup K) (n : ℕ) :
    PowerSeries.constantCoeff (formalNsmul F n) = 0

theorem formalNsmul_coeff_one
    (F : FormalGroup K) (n : ℕ) :
    PowerSeries.coeff 1 (formalNsmul F n) = (n : K)

end FormalGroup
```

This is the easy part.

### 2. Weierstrass formal group bridge

For your concrete `W.formalGroup`:

```lean
theorem weierstrass_local_nsmul_coeff_one
    (n : ℕ) :
    coeffε_of_local_parameter_of_nsmul_near_O W n = (n : K) := by
  -- reduce to `FormalGroup.formalNsmul_coeff_one W.formalGroup n`
  sorry
```

This is where `FormalGroupW.lean` should connect `addXYZ`/local parameter to `FormalGroup.formalNsmul`.

### 3. Translate tangent nonvanishing to any torsion point

You do not need the full formal group at every point. You need a theorem like:

```lean
theorem tangent_nsmul_at_torsion_is_nat
    {P : W.Point} (hP : n • P = 0) :
    tangentMapCoeff_at P (fun Q => n • Q) = (n : K) := by
  -- translate P to O and use the local theorem at O
  sorry
```

This can be proven either:

* abstractly from group translation and the local formal group at `O`; or
* by the finite-point tangent induction route discussed earlier.

The abstract translation proof is conceptually cleaner, but it requires enough infrastructure for tangent/local coordinates under translation.

### 4. Division-polynomial root/torsion bridge

You need a theorem that a root of `preΨ' n` corresponds to a point in the kernel of `[n]`, and that a multiple root gives a tangent vector killed by `[n]`.

A useful dual-number statement is:

```lean
theorem multiple_root_preΨ'_gives_dual_torsion
    {x : K} (hx : Polynomial.aeval x (W.preΨ' n) = 0)
    (hdx : Polynomial.aeval x (derivative (W.preΨ' n)) = 0) :
    ∃ (Pε : point over K[ε]),
      reduction Pε is an n-torsion point ∧
      tangent vector of Pε is nonzero ∧
      [n]Pε = Oε := by
  ...
```

Then combine with tangent nonvanishing:

```lean
theorem preΨ'_root_derivative_ne_zero
    (hn : (n : K) ≠ 0)
    {x : K} (hx : Polynomial.aeval x (W.preΨ' n) = 0) :
    Polynomial.aeval x (derivative (W.preΨ' n)) ≠ 0 := by
  intro hderiv
  obtain ⟨Pε, hred, hnonzero, hnPε⟩ :=
    multiple_root_preΨ'_gives_dual_torsion W n hx hderiv
  have htangent := tangent_nsmul_at_torsion_is_nat W hn hred
  -- `hnPε` says tangent is killed, `htangent` says multiplication by nonzero scalar.
  contradiction
```

Finally convert root-derivative nonvanishing into `Polynomial.Separable`. Depending on which Mathlib lemmas are convenient, either prove `IsCoprime f f.derivative` directly or prove no multiple roots over a splitting field and use an existing squarefree/separable criterion.

## Direct algebraic alternative

If the geometric bridge to `preΨ'` is too large, another possible route is purely algebraic:

```lean
theorem gcd_preΨ'_derivative_eq_one
    (hn : (n : K) ≠ 0) :
    IsCoprime (W.preΨ' n) (derivative (W.preΨ' n)) := by
  -- use EDS recurrences, degree computations, and identities among `preΨ'`, `ΨSq`, `Φ`.
```

But this is likely harder than the tangent-map proof, because the recurrence algebra for `preΨ'` is large.

## Important caveats for `preΨ'`

`preΨ'` is not exactly `ψₙ` in all parities.

Mathlib defines:

```lean
W.Ψ n = C (W.preΨ n) * if Even n then W.ψ₂ else 1
```

So for even `n`, `preΨ n` is the division polynomial with the `ψ₂` factor removed. This means the root/torsion bridge has a 2-torsion caveat:

* odd `n`: `preΨ n` corresponds directly to the usual `ψₙ` roots;
* even `n`: `Ψ n` has an extra `ψ₂` factor, and `preΨ n` excludes the 2-torsion factor.

For separability of `preΨ' n`, this is actually helpful, but the proof must know which torsion points are represented by `preΨ'` and which are represented by `ψ₂`.

## Recommended implementation order

1. **In a small formal-group utility file**, add:

   ```lean
   FormalGroup.formalNsmul
   FormalGroup.formalNsmul_constantCoeff
   FormalGroup.formalNsmul_coeff_one
   ```

   This is independent of elliptic curves and should be reusable.

2. **In `FormalGroupW.lean`**, after constructing `W.formalGroup`, prove:

   ```lean
   W.formalGroup_nsmul_local_coeff_one
   ```

   by reducing to `FormalGroup.formalNsmul_coeff_one`.

3. **For division polynomials**, first prove only the correctness theorem you need:

   ```lean
   preΨ'_root_iff_xcoord_n_torsion_non2
   ```

   Do not try to formalize all of `ωₙ` unless the projective-coordinate theorem forces you to.

4. **Then prove root derivative nonzero**, using dual numbers or tangent vectors.

5. **Then package as `Polynomial.Separable`**:

   ```lean
   theorem preΨ'_separable_of_natCast_ne_zero
       (hn : (n : K) ≠ 0) :
       (W.preΨ' n).Separable := by
     rw [Polynomial.separable_def]
     -- show coprime with derivative, e.g. by no common root / gcd argument
     sorry
   ```

## Bottom line

Mathlib gives you the formal-group *structure* and the division-polynomial *definitions*, but not the multiplication-by-`n` formal power series, not the coefficient theorem, and not the formal-group-to-division-polynomial separability bridge.

The minimum you should build yourself is:

```text
formalNsmul_coeff_one: [n]_F(T) = nT + O(T²)
local_nsmul_bridge: elliptic [n] near O agrees with formalNsmul
translation/tangent bridge: d[n] at torsion P is multiplication by n
preΨ'_torsion bridge: roots/multiple roots of preΨ' correspond to torsion/tangent-kernel data
```

The first item is small. The remaining three are the real content of the separability proof.
