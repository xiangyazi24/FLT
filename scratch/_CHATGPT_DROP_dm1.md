# Q1145 (dm1): Route 4B, real torsion bound `#E(ℝ)[m] ≤ 2m`

## Executive answer

The Route 4B reduction is a good way to avoid Weil pairing and elliptic Galois representations, but the hard theorem is now exactly the real-topological statement

```lean
Nat.card ((Eℝ).nTorsion m) ≤ 2 * m
```

for an elliptic curve over `ℝ`.  The base-change and group-theory reduction are comparatively small.  The shortest honest Lean plan is:

```text
1. Use the existing point-map infrastructure to send E(ℚ) → E(ℝ).
2. Compose the full rational torsion injection with this map.
3. Land in the real m-torsion subgroup.
4. Use the hard real theorem #E(ℝ)[m] ≤ 2m.
5. Compare cardinals: m² ≤ #E(ℝ)[m] ≤ 2m, hence m ≤ 2.
```

I would **not** try to prove `#E(ℝ)[m] ≤ 2m` from division polynomials.  The polynomial proof still needs the same real topology in disguise.  The clean target theorem to build is either the direct bound

```lean
real_nTorsion_card_le_two_mul
```

or a topological package saying that the real Lie group `E(ℝ)` has identity component a circle and component group of size at most `2`.

## Repository check

I checked the FLT repository through the GitHub connector.

Relevant findings:

* `FLT.lean` imports `FLT.EllipticCurve.Torsion` as the only visible `FLT.EllipticCurve.*` module in the root import list.
* `FLT/EllipticCurve/Torsion.lean` already defines

  ```lean
  abbrev WeierstrassCurve.nTorsion (n : ℕ) :=
    Submodule.torsionBy ℤ (E⁄k).Point n
  ```

  and also defines a point-map wrapper:

  ```lean
  noncomputable def WeierstrassCurve.Points.map
      {K L : Type u} [Field K] [Field L] [Algebra k K] [Algebra k L]
      [DecidableEq K] [DecidableEq L]
      (f : K →ₐ[k] L) : (E⁄K).Point →+ (E⁄L).Point :=
    WeierstrassCurve.Affine.Point.map f
  ```

* The same file has `Points.map_id`, `Points.map_comp`, `galoisRepresentationSmul`, and a `galoisRep` placeholder.
* Direct fetches of plausible real-point files such as

  ```text
  FLT/EllipticCurve/Real.lean
  FLT/EllipticCurve/RealTorsion.lean
  FLT/EllipticCurve/Point.lean
  ```

  returned `404`.

So the repo already has the **right base-change map on points**, but I did not find a real Lie-group / real torsion bound API.  Route 4B needs new real-topological infrastructure.

## 1. Base change `ℚ → ℝ`

For `E : WeierstrassCurve ℚ`, there are two equivalent ways to talk about real points.

### Preferred in this repo: use `E⁄ℝ`

The existing `Points.map` wrapper is already designed for this.  If `E` is over a base field `k`, and `K` and `L` are `k`-algebras, then

```lean
WeierstrassCurve.Points.map E (f : K →ₐ[k] L) :
  (E⁄K).Point →+ (E⁄L).Point
```

So for `k = ℚ`, `K = ℚ`, `L = ℝ`, the rational-to-real map should be:

```lean
import FLT.EllipticCurve.Torsion
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped Classical
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace FLT

namespace RealTorsionBound

/-- The canonical `ℚ`-algebra map `ℚ → ℝ`. -/
noncomputable abbrev ratToRealAlgHom : ℚ →ₐ[ℚ] ℝ :=
  IsScalarTower.toAlgHom ℚ ℚ ℝ

/-- The group homomorphism on points induced by `ℚ → ℝ`. -/
noncomputable def rationalPointToReal
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (E⁄ℚ).Point →+ (E⁄ℝ).Point :=
  WeierstrassCurve.Points.map E ratToRealAlgHom

end RealTorsionBound

end FLT
```

The exact spelling of `ratToRealAlgHom` may need adjustment.  If `IsScalarTower.toAlgHom ℚ ℚ ℝ` does not infer cleanly, use the equivalent explicit algebra hom built from `algebraMap ℚ ℝ`.  The point is that `Points.map` wants a `ℚ`-algebra hom `ℚ →ₐ[ℚ] ℝ`.

### If you need a curve object over `ℝ`

`FLT/EllipticCurve/Torsion.lean` already uses `E.map (algebraMap K (AlgebraicClosure K))` in the definition of `galoisRep`, so the corresponding real curve is:

```lean
import FLT.EllipticCurve.Torsion
import Mathlib.Data.Real.Basic

open scoped Classical

noncomputable section

namespace FLT

namespace RealTorsionBound

/-- The base change of a rational Weierstrass curve to `ℝ`. -/
noncomputable abbrev baseChangeReal
    (E : WeierstrassCurve ℚ) : WeierstrassCurve ℝ :=
  E.map (algebraMap ℚ ℝ)

end RealTorsionBound

end FLT
```

For most of Route 4B, however, you can stay with `(E⁄ℝ).Point` rather than manually rewriting everything through `baseChangeReal E`.

### Injectivity of the point map

You need one small lemma:

```lean
import FLT.EllipticCurve.Torsion
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped Classical
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace FLT

namespace RealTorsionBound

noncomputable abbrev ratToRealAlgHom : ℚ →ₐ[ℚ] ℝ :=
  IsScalarTower.toAlgHom ℚ ℚ ℝ

noncomputable def rationalPointToReal
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (E⁄ℚ).Point →+ (E⁄ℝ).Point :=
  WeierstrassCurve.Points.map E ratToRealAlgHom

/--
Target lemma: the map `E(ℚ) → E(ℝ)` is injective.

Proof idea: unfold `WeierstrassCurve.Affine.Point.map`; the point at infinity is
preserved, and affine coordinates are mapped by `ℚ → ℝ`, which is injective.
-/
theorem rationalPointToReal_injective
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Function.Injective (rationalPointToReal E) := by
  -- This should be a case split on points plus `Rat.cast_injective`.
  -- If Mathlib already has a lemma like `Affine.Point.map_injective`, use it.
  -- Otherwise prove it directly from the constructors of affine points.
  intro P Q hPQ
  -- sketch:
  -- cases P <;> cases Q <;> simp [rationalPointToReal, ratToRealAlgHom] at hPQ ⊢
  -- exact coordinate injectivity from `Rat.cast_injective`
  sorry

end RealTorsionBound

end FLT
```

This is a local algebraic lemma, not the hard part of Route 4B.

## 2. Why the elementary division-polynomial approaches are not good shortcuts

### 2(a). Bound real roots of `ψ_m` directly?

This is mathematically possible only after importing the same real geometry.  The division polynomial has degree roughly `m²/2`; a purely algebraic polynomial-degree argument gives the wrong bound.  To show it has only `O(m)` real roots, one must know how multiplication by `m` behaves on the real ovals of the curve.  That is already the real Lie-group/topology theorem in another form.

So this is not a shorter Lean path.

### 2(b). Use the x-coordinate fibers and real factorization?

The fiber size statement is easy:

```text
x : E(ℝ) → ℝ
```

has fibers of size at most `2`, away from the point at infinity and with the usual tangent/2-torsion edge cases.

But this only gives:

```text
#E(ℝ)[m] ≤ 2 * #(real roots of ψ_m) + 1.
```

It does not bound the number of real roots of `ψ_m` by `m`.  The statement that the relevant real roots are arranged along one or two real circles is again the topological theorem.

The factorization of a real polynomial into linear and irreducible quadratic factors is useless for the desired bound: a real polynomial of degree `~m²/2` can have `~m²/2` linear factors.

### 2(c). Any other elementary bound?

The only genuinely elementary-looking alternative is to parametrize real points by elliptic integrals and prove that multiplication by `m` on each real component has exactly `m` torsion points.  But formalizing elliptic integrals and period lattices is not shorter than using a packaged topological group theorem.

So the answer is: no known elementary polynomial route is shorter in Lean.

## 3. Minimal topological fact needed

You do **not** need the full global classification of real elliptic curves in all its analytic detail.  You need exactly this theorem:

```lean
import FLT.EllipticCurve.Torsion
import Mathlib.Data.Real.Basic

open scoped Classical

noncomputable section

namespace FLT

namespace RealTorsionBound

/--
Hard Route 4B theorem.
For every real elliptic curve, the `m`-torsion subgroup has at most `2m` points.
-/
theorem real_nTorsion_card_le_two_mul
    (E : WeierstrassCurve ℝ) [E.IsElliptic] (m : ℕ) :
    Nat.card (E.nTorsion m) ≤ 2 * m := by
  -- This is the new real-topology theorem Route 4B must supply.
  -- Preferred proof: `E(ℝ)` is a compact abelian Lie group with identity
  -- component a circle and component group of size at most 2.
  sorry

end RealTorsionBound

end FLT
```

Internally, the clean proof is:

```text
E(ℝ) has at most two connected components.
The identity component E(ℝ)^0 is isomorphic as a topological group to S¹.
The component group π₀(E(ℝ)) has size at most 2.
S¹[m] has exactly m points.
Therefore E(ℝ)[m] has at most 2m points.
```

The theorem can be weakened slightly.  You do not need to expose an isomorphism with `S¹`; it suffices to prove the following two facts:

```text
#(E(ℝ)^0[m]) ≤ m
#π₀(E(ℝ)) ≤ 2
```

Then use the exact sequence

```text
0 → E(ℝ)^0[m] → E(ℝ)[m] → π₀(E(ℝ))
```

to get `#E(ℝ)[m] ≤ m * 2`.

But note: proving `#(E(ℝ)^0[m]) ≤ m` is essentially the one-dimensional compact connected Lie group theorem.  Compactness plus “dimension one” plus “at most two components” is not enough as a bare topological-space statement; you need the **topological group / Lie group** structure, or an equivalent covering-map theorem for multiplication by `m` on a real oval.

Therefore the minimal honest package is one of:

```text
A. Direct theorem:       #E(ℝ)[m] ≤ 2m.
B. Component theorem:    E(ℝ)^0 ≃ S¹ and #π₀(E(ℝ)) ≤ 2.
C. Covering theorem:     [m] on each real oval has degree m, and there are ≤2 ovals.
```

For Lean, I recommend **A** as the public theorem and **B** or **C** as its private proof.

## 4. Group-theory/cardinality reduction

Here is the intended Lean shape of the reduction.  It deliberately assumes the two hard/local facts as theorem parameters:

* `rationalPointToReal_injective`, a small coordinate proof;
* `real_nTorsion_card_le_two_mul`, the real-topology theorem.

The rest is ordinary group theory and cardinal arithmetic.

```lean
import FLT.EllipticCurve.Torsion
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped Classical
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace FLT

namespace RealTorsionBound

/-- Project-local shape of full rational torsion.  Use the existing definition if present. -/
def HasFullRationalTorsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod m →+ (E⁄ℚ).Point, Function.Injective f

noncomputable abbrev ratToRealAlgHom : ℚ →ₐ[ℚ] ℝ :=
  IsScalarTower.toAlgHom ℚ ℚ ℝ

noncomputable def rationalPointToReal
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (E⁄ℚ).Point →+ (E⁄ℝ).Point :=
  WeierstrassCurve.Points.map E ratToRealAlgHom

/--
Lift an injection `(ZMod m × ZMod m) → E(ℚ)` to a hom into real `m`-torsion.
-/
noncomputable def fullTorsionToRealNTorsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ)
    (f : ZMod m × ZMod m →+ (E⁄ℚ).Point) :
    ZMod m × ZMod m →+ (E⁄ℝ).Point :=
  (rationalPointToReal E).comp f

/--
Target lemma: the image of `fullTorsionToRealNTorsion` lands in `m`-torsion.
The final implementation should package the codomain as `((E⁄ℝ).curve).nTorsion m`
or the repository's preferred equivalent.
-/
theorem fullTorsionToRealNTorsion_mem
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ)
    (f : ZMod m × ZMod m →+ (E⁄ℚ).Point)
    (a : ZMod m × ZMod m) :
    m • fullTorsionToRealNTorsion E m f a = 0 := by
  -- Since the domain is `ZMod m × ZMod m`, `m • a = 0`.
  -- Then use `map_nsmul`/`map_zsmul` for the additive hom.
  change m • ((rationalPointToReal E) (f a)) = 0
  rw [← map_nsmul]
  have ha : m • a = 0 := by
    ext <;> simp
  rw [← f.map_nsmul, ha, f.map_zero, map_zero]

/--
Cardinality reduction: if full rational `m`-torsion injects into real points and
real `m`-torsion has size at most `2m`, then `m ≤ 2`.

This is the part that should be routine once the real bound is available.
-/
theorem fullRationalTorsion_order_le_two_of_real_bound
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m)
    (hPointInj : Function.Injective (rationalPointToReal E))
    (hRealBound : Nat.card (Submodule.torsionBy ℤ (E⁄ℝ).Point m) ≤ 2 * m) :
    m ≤ 2 := by
  rcases hfull with ⟨f, hf⟩

  let g : ZMod m × ZMod m →+ (E⁄ℝ).Point :=
    (rationalPointToReal E).comp f

  have hg_inj : Function.Injective g := by
    intro a b hab
    apply hf
    apply hPointInj
    exact hab

  -- Package `g` as an injection into the `m`-torsion subgroup.
  let gt : ZMod m × ZMod m → Submodule.torsionBy ℤ (E⁄ℝ).Point m :=
    fun a => ⟨g a, by
      -- same proof as `fullTorsionToRealNTorsion_mem`
      change m • g a = 0
      rw [← map_nsmul]
      have ha : m • a = 0 := by
        ext <;> simp
      rw [← f.map_nsmul, ha, f.map_zero, map_zero]
    ⟩

  have hgt_inj : Function.Injective gt := by
    intro a b h
    apply hg_inj
    exact Subtype.ext_iff.mp h

  have hcard_lower : m * m ≤ Nat.card (Submodule.torsionBy ℤ (E⁄ℝ).Point m) := by
    calc
      m * m = Nat.card (ZMod m × ZMod m) := by
        -- Use the finite-cardinality lemmas for `ZMod` and products.
        -- Depending on imported simp lemmas, this is usually just `simp [hm.ne']`.
        simp [Nat.card_prod]
      _ ≤ Nat.card (Submodule.torsionBy ℤ (E⁄ℝ).Point m) :=
        Nat.card_le_card_of_injective gt hgt_inj

  have hsq : m * m ≤ 2 * m := le_trans hcard_lower hRealBound
  omega

end RealTorsionBound

end FLT
```

A few details may need local rewriting in the final file:

* `Submodule.torsionBy ℤ (E⁄ℝ).Point m` is definitionally the same pattern used by `WeierstrassCurve.nTorsion` in `FLT/EllipticCurve/Torsion.lean`.
* If the notation `(E⁄ℝ).Point` does not expose exactly the curve object expected by `nTorsion`, keep using `Submodule.torsionBy` directly, as above.
* The proof line `simp [Nat.card_prod]` may need the exact Mathlib lemma names for `Nat.card (ZMod m)` at this project's Mathlib revision.  The intended fact is simply

  ```lean
  Nat.card (ZMod m × ZMod m) = m * m
  ```

  under `hm : 0 < m`.

## 5. The final theorem shape

Once `rationalPointToReal_injective` and `real_nTorsion_card_le_two_mul` are proved, the desired theorem should be a small wrapper.

```lean
import FLT.EllipticCurve.Torsion
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped Classical
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace FLT

namespace RealTorsionBound

-- Use the actual project definition if it already exists.
def HasFullRationalTorsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod m →+ (E⁄ℚ).Point, Function.Injective f

/-- Final Route 4B theorem, after the real torsion bound has been supplied. -/
theorem fullRationalTorsion_order_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 := by
  apply fullRationalTorsion_order_le_two_of_real_bound
      (E := E) (m := m) hm hfull
  · exact rationalPointToReal_injective E
  · -- Apply the real theorem to the real points of `E`.
    -- Depending on definitional equality, this may be exactly:
    --   exact real_nTorsion_card_le_two_mul (baseChangeReal E) m
    -- or a small transport/rewrite from `(baseChangeReal E).nTorsion m`
    -- to `Submodule.torsionBy ℤ (E⁄ℝ).Point m`.
    sorry

end RealTorsionBound

end FLT
```

The remaining `sorry` in this sketch is not intended as a new axiom.  It marks the transport between the chosen statement of the real theorem and the torsion subgroup expression used in the cardinality reduction.  If you state the real theorem directly as

```lean
Nat.card (Submodule.torsionBy ℤ (E⁄ℝ).Point m) ≤ 2 * m
```

for rational `E`, then even this transport disappears.

## Practical recommendation

For Route 4B, do not start with division polynomials.  Add these files/lemmas in this order:

```text
1. FLT/EllipticCurve/RealBaseChange.lean
   - rationalPointToReal
   - rationalPointToReal_injective
   - compatibility with nsmul/torsion

2. FLT/EllipticCurve/RealTorsionBound.lean
   - theorem real_nTorsion_card_le_two_mul
     or the stronger/topological theorem from which it follows

3. A small wrapper proving
   - fullRationalTorsion_order_le_two
```

The base-change embedding is already supported by `WeierstrassCurve.Points.map`.  The group-theory cardinality comparison is routine.  The **only large missing theorem** is the real topological one:

```text
#E(ℝ)[m] ≤ 2m.
```

The minimal honest proof of that theorem still needs one-dimensional compact abelian Lie-group/topological-group input.  In Lean terms, the public API should hide that topology behind the direct real torsion bound, because that is exactly what the FLT argument needs.
