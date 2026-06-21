import Mathlib
import FLT.EllipticCurve.Torsion
import scratch.A6TorsionFinite

/-!
# Torsion finiteness via Mordell-Weil finite generation

Reduces rational_torsion_finite to the Mordell-Weil axiom.
The group theory step uses Module.Finite over ℤ (a PID) + torsion structure theorem.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-- The torsion part of a finitely generated ℤ-module is finite.
This follows from the structure theorem for f.g. modules over PIDs. -/
theorem torsion_set_finite_of_fg
    (G : Type*) [AddCommGroup G] [AddGroup.FG G] :
    (AddCommGroup.torsion G : Set G).Finite := by
  haveI : Module.Finite ℤ G := Module.Finite.iff_addGroup_fg.mpr ‹_›
  let T : AddSubgroup G := AddCommGroup.torsion G
  let Tsub : Submodule ℤ G := T.toIntSubmodule
  have hTsub_fg : Tsub.FG := by
    exact Submodule.FG.of_le (T := (⊤ : Submodule ℤ G)) Module.Finite.fg_top
      (by intro x hx; trivial)
  haveI : Module.Finite ℤ Tsub := Module.Finite.iff_fg.mpr hTsub_fg
  have hTsub_eq : Tsub = Submodule.torsion ℤ G := by
    dsimp [Tsub, T]
    rw [← Submodule.torsion_int, Submodule.toAddSubgroup_toIntSubmodule]
  have hTorsion : Module.IsTorsion ℤ Tsub := by
    rw [hTsub_eq]
    exact Submodule.torsion_isTorsion
  haveI : Finite Tsub := Module.finite_of_fg_torsion (M := Tsub) hTorsion
  have hRange : Set.range (Subtype.val : Tsub → G) = (Tsub : Set G) := by
    ext x
    simp
  have hfin : (Set.range (Subtype.val : Tsub → G)).Finite := Set.finite_range _
  have hfinTsub : (Tsub : Set G).Finite := by
    simpa [hRange] using hfin
  rwa [AddSubgroup.coe_toIntSubmodule] at hfinTsub

theorem rational_torsion_finite_of_mw (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).Finite := by
  exact rational_torsion_finite_height E




/-- Alias for downstream use — same statement as Axioms.rational_torsion_finite. -/
theorem rational_torsion_finite_alias (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).Finite := by
  exact rational_torsion_finite_height E

end MazurProof
