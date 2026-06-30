import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace MazurProof.RationalPointsN12

theorem zmod3_endpoint_square_ap_forces_middle_zero
    (P Q R S Δ : ZMod 3)
    (hp : P = 0) (hs : S = 0)
    (hpq : Q ^ 2 - P ^ 2 = Δ)
    (hqr : R ^ 2 - Q ^ 2 = Δ)
    (hrs : S ^ 2 - R ^ 2 = Δ) :
    Q = 0 ∧ R = 0 := by
  revert hp hs hpq hqr hrs
  fin_cases P <;> fin_cases Q <;> fin_cases R <;>
    fin_cases S <;> fin_cases Δ <;> decide

end MazurProof.RationalPointsN12
