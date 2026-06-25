# Q541 (dm1): universal-ring transport for `formalAddZ_dvd_cube`

Yes: Mathlib already has the projective naturality lemmas you want, with the exact names
`WeierstrassCurve.Projective.map_addZ` and `WeierstrassCurve.Projective.map_addXYZ`; the important type correction is that the coefficient evaluation map must be lifted to power series as `MvPowerSeries.map (univEval W)`, not applied directly to `univWeierstrassCurve.formalAddZ`.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic

open MvPolynomial

namespace WeierstrassCurve

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The universal coefficient ring `ℤ[a₁,a₂,a₃,a₄,a₆]`. -/
abbrev UnivCoeff : Type := MvPolynomial (Fin 5) ℤ

/-- The universal Weierstrass curve over `ℤ[a₁,a₂,a₃,a₄,a₆]`. -/
def univWeierstrassCurve : WeierstrassCurve UnivCoeff where
  a₁ := MvPolynomial.X (0 : Fin 5)
  a₂ := MvPolynomial.X (1 : Fin 5)
  a₃ := MvPolynomial.X (2 : Fin 5)
  a₄ := MvPolynomial.X (3 : Fin 5)
  a₆ := MvPolynomial.X (4 : Fin 5)

/-- The five coefficient values of a curve `W`, used to evaluate the universal ring. -/
def univCoeffEval (W : WeierstrassCurve R) : Fin 5 → R :=
  ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

/-- Evaluation from the universal coefficient ring to the coefficient ring of `W`. -/
def univEval (W : WeierstrassCurve R) : UnivCoeff →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) (univCoeffEval W)

@[simp] lemma univEval_X0 (W : WeierstrassCurve R) :
    univEval W (MvPolynomial.X (0 : Fin 5)) = W.a₁ := by
  simp [univEval, univCoeffEval]

@[simp] lemma univEval_X1 (W : WeierstrassCurve R) :
    univEval W (MvPolynomial.X (1 : Fin 5)) = W.a₂ := by
  simp [univEval, univCoeffEval]

@[simp] lemma univEval_X2 (W : WeierstrassCurve R) :
    univEval W (MvPolynomial.X (2 : Fin 5)) = W.a₃ := by
  simp [univEval, univCoeffEval]

@[simp] lemma univEval_X3 (W : WeierstrassCurve R) :
    univEval W (MvPolynomial.X (3 : Fin 5)) = W.a₄ := by
  simp [univEval, univCoeffEval]

@[simp] lemma univEval_X4 (W : WeierstrassCurve R) :
    univEval W (MvPolynomial.X (4 : Fin 5)) = W.a₆ := by
  simp [univEval, univCoeffEval]

@[simp] lemma map_univWeierstrassCurve_univEval (W : WeierstrassCurve R) :
    univWeierstrassCurve.map (univEval W) = W := by
  ext <;> simp [univWeierstrassCurve]

/-!
The local naturality lemma for your formal addition construction.

If you already have this lemma, keep your existing one and skip this block.  If not, this is the
right statement.  Its proof is deliberately by unfolding the local formal point definitions and then
using Mathlib's existing projective formula lemma `WeierstrassCurve.Projective.map_addZ`.

The only project-local names in the proof are `formalPoint₀`, `formalPoint₁`, and the naturality
lemma for the formal parameter solution `formalW_map`/`w_map`; replace those three names by the
actual local names in your file if they differ.  The final theorem below is independent of those
names once this `[simp]` lemma exists.
-/
@[simp] lemma formalAddZ_map (f : R →+* S) (W : WeierstrassCurve R) :
    MvPowerSeries.map (σ := Fin 2) f W.formalAddZ = (W.map f).formalAddZ := by
  classical
  -- Expected local definition shape:
  --   W.formalAddZ = (W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)).addZ
  --       W.formalPoint₀ W.formalPoint₁
  -- where the formal points are `[X₀,-1,w(X₀)]` and `[X₁,-1,w(X₁)]`.
  -- After unfolding, `simp` uses:
  --   * `MvPowerSeries.map_X`
  --   * `MvPowerSeries.map_C`
  --   * your `formalW_map`/`w_map`
  --   * `WeierstrassCurve.Projective.map_addZ`
  -- Mathlib's exact lemma is:
  --   `WeierstrassCurve.Projective.map_addZ`.
  unfold WeierstrassCurve.formalAddZ
  simpa [WeierstrassCurve.map_map]
    using
      (WeierstrassCurve.Projective.map_addZ
        (W' := W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R))
        (f := MvPowerSeries.map (σ := Fin 2) f)
        (P := W.formalPoint₀)
        (Q := W.formalPoint₁)).symm

/-- Universal evaluation commutes with the formal `Z`-addition series. -/
@[simp] lemma univEval_formalAddZ (W : WeierstrassCurve R) :
    MvPowerSeries.map (σ := Fin 2) (univEval W) univWeierstrassCurve.formalAddZ =
      W.formalAddZ := by
  simpa [map_univWeierstrassCurve_univEval]
    using formalAddZ_map (R := UnivCoeff) (S := R) (univEval W) univWeierstrassCurve

/-- General-ring divisibility, transported from the universal domain case. -/
theorem formalAddZ_dvd_cube (W : WeierstrassCurve R) :
    (MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) ^ 3 ∣ W.formalAddZ := by
  classical
  -- `MvPolynomial (Fin 5) ℤ` is a domain, hence has no zero divisors.
  letI : NoZeroDivisors UnivCoeff := inferInstance
  rcases formalAddZ_dvd_cube_of_noZeroDivisors
      (R := UnivCoeff) univWeierstrassCurve with ⟨q, hq⟩
  refine ⟨MvPowerSeries.map (σ := Fin 2) (univEval W) q, ?_⟩
  have hmap := congrArg (MvPowerSeries.map (σ := Fin 2) (univEval W)) hq
  simpa [univEval_formalAddZ] using hmap

end

end WeierstrassCurve
```

If your local formal-point names are not `formalPoint₀`/`formalPoint₁`, the only edit should be in `formalAddZ_map`; the final transport theorem is exactly the `rcases`/`congrArg (MvPowerSeries.map ...)` proof above.
