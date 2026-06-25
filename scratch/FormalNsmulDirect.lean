import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution

namespace FormalNsmulDirect

variable {R : Type*} [CommRing R]

noncomputable def addF (F : MvPowerSeries (Fin 2) R) (f g : PowerSeries R) : PowerSeries R :=
  MvPowerSeries.subst (fun i : Fin 2 => (![f, g] i : PowerSeries R)) F

noncomputable def formalNsmulF (F : MvPowerSeries (Fin 2) R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => addF F (formalNsmulF F n) PowerSeries.X

theorem formalNsmulF_coeff_one (F : MvPowerSeries (Fin 2) R)
    (hF : MvPowerSeries.constantCoeff (σ := Fin 2) F = 0)
    (hX : (MvPowerSeries.coeff (R := R) (Finsupp.single 0 1)) F = 1)
    (hY : (MvPowerSeries.coeff (R := R) (Finsupp.single 1 1)) F = 1)
    (n : ℕ) : PowerSeries.coeff (R := R) 1 (formalNsmulF F n) = (n : R) := by
  sorry

end FormalNsmulDirect
