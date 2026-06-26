# Q702 (dm1): `formalAddZ_dvd_cube` by universal-ring transport

```lean
import scratch.FormalGroupW

open MvPowerSeries Finsupp WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- The `Z`-coordinate naturality statement extracted from `formalAddXYZ_map`.
This is the only naturality fact needed for the universal-ring transport. -/
private theorem formalAddZ_map_from_formalAddXYZ
    {S T : Type*} [CommRing S] [CommRing T]
    (φ : S →+* T) (V : WeierstrassCurve S) :
    MvPowerSeries.map φ V.formalAddZ = (V.map φ).formalAddZ := by
  simpa using (formalAddXYZ_map φ V (2 : Fin 3))

/-- Divisibility of the formal `Z` addition coordinate by `(X₀ - X₁)^3`, transported
from the universal Weierstrass curve over `MvPolynomial (Fin 5) ℤ`. -/
theorem formalAddZ_dvd_cube (W : WeierstrassCurve R) :
    (((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) -
        MvPowerSeries.X (1 : Fin 2)) ^ 3) ∣ W.formalAddZ := by
  classical
  let A := MvPolynomial (Fin 5) ℤ
  let φ : A →+* R := univEval W
  let ΔA : MvPowerSeries (Fin 2) A :=
    (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) -
      MvPowerSeries.X (1 : Fin 2)
  let ΔR : MvPowerSeries (Fin 2) R :=
    (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) -
      MvPowerSeries.X (1 : Fin 2)

  -- 1. The universal coefficient ring is a domain, so the domain proof applies.
  have huniv : ΔA ^ 3 ∣ univWeierstrassCurve.formalAddZ := by
    simpa [A, ΔA] using
      (formalAddZ_dvd_cube_of_noZeroDivisors (V := univWeierstrassCurve))
  rcases huniv with ⟨q, hq⟩

  -- 2. Transport the universal witness through `MvPowerSeries.map φ`.
  refine ⟨MvPowerSeries.map φ q, ?_⟩
  change W.formalAddZ = ΔR ^ 3 * MvPowerSeries.map φ q

  -- 3. Naturality of `formalAddZ` under coefficient maps.
  have hZmap :
      MvPowerSeries.map φ univWeierstrassCurve.formalAddZ = W.formalAddZ := by
    simpa [A, φ, univEval_map W] using
      (formalAddZ_map_from_formalAddXYZ φ univWeierstrassCurve)

  -- 4. The factor `(X₀ - X₁)^3` is coefficient-free, so it is fixed by `map φ`.
  have hΔmap : MvPowerSeries.map φ (ΔA ^ 3) = ΔR ^ 3 := by
    simp [A, φ, ΔA, ΔR]

  calc
    W.formalAddZ
        = MvPowerSeries.map φ univWeierstrassCurve.formalAddZ := hZmap.symm
    _ = MvPowerSeries.map φ (ΔA ^ 3 * q) := by
        rw [hq]
    _ = MvPowerSeries.map φ (ΔA ^ 3) * MvPowerSeries.map φ q := by
        rw [map_mul]
    _ = ΔR ^ 3 * MvPowerSeries.map φ q := by
        rw [hΔmap]
```
