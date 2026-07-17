import Mathlib

/-!
Generated algebraic certificates for the two-stage 7-isogeny bridge to X₀(49).

This file is intentionally namespace-light and uses only rational-function identities.
-/

namespace MazurProof.X049BridgeFormulas

noncomputable section

def F5 (b c : ℚ) : ℚ := b - c
def F6 (b c : ℚ) : ℚ := b - c - c^2
def F7 (b c : ℚ) : ℚ := c^3 - b^2 + b*c
def F7std (b c : ℚ) : ℚ := b^2 - b*c - c^3
def F8 (b c : ℚ) : ℚ := 2*b^2 - b*c^2 - 3*b*c + c^2
def F9 (b c : ℚ) : ℚ :=
  b^3 - 3*b^2*c + b*c^3 + 3*b*c^2 - c^5 - c^4 - c^3

def x7 (b c : ℚ) : ℚ := b*c*F6 b c*F8 b c / (F7 b c)^2
def y7 (b c : ℚ) : ℚ := -b^2*(F6 b c)^2*F9 b c / (F7 b c)^3

def normD3 (a1 a3 r w : ℚ) : ℚ := a3 + r*a1 + 2*w

def normSlope (a1 a2 a3 a4 r w : ℚ) : ℚ :=
  (3*r^2 + 2*a2*r + a4 - a1*w) / normD3 a1 a3 r w

def normA1 (a1 a2 a3 a4 r w : ℚ) : ℚ :=
  a1 + 2*normSlope a1 a2 a3 a4 r w

def normA2 (a1 a2 a3 a4 r w : ℚ) : ℚ :=
  let l := normSlope a1 a2 a3 a4 r w
  a2 - l*a1 + 3*r - l^2

def dInvariant (a1 a2 a3 a4 r w : ℚ) : ℚ :=
  -(normA2 a1 a2 a3 a4 r w ^ 3) /
    (normD3 a1 a3 r w * (normD3 a1 a3 r w - normA1 a1 a2 a3 a4 r w * normA2 a1 a2 a3 a4 r w))

def T7 (d : ℚ) : ℚ :=
  49*d*(d - 1) / (d^3 - 8*d^2 + 5*d + 1)

def A7 (z : ℚ) : ℚ := z^2 + 13*z + 49
def B7 (z : ℚ) : ℚ := z^2 + 5*z + 1
def C7 (z : ℚ) : ℚ := z^2 + 245*z + 2401

def q49 (S T : ℚ) : ℚ :=
    T^7
  - 4018*S*T^6
  - 8624*(49*S*T^5 + S^2*T^6)
  - 5915*(49^2*S*T^4 + 49*S^2*T^5 + S^3*T^6)
  - 1904*(49^3*S*T^3 + 49^2*S^2*T^4 + 49*S^3*T^5 + S^4*T^6)
  - 322*(49^4*S*T^2 + 49^3*S^2*T^3 + 49^2*S^3*T^4
          + 49*S^4*T^5 + S^5*T^6)
  - 28*(49^5*S*T + 49^4*S^2*T^2 + 49^3*S^3*T^3
         + 49^2*S^4*T^4 + 49*S^5*T^5 + S^6*T^6)
  - (49^6*S + 49^5*S^2*T + 49^4*S^3*T^2 + 49^3*S^4*T^3
      + 49^2*S^5*T^4 + 49*S^6*T^5 + S^7*T^6)

theorem q49_factor_identity (S T : ℚ) :
    T^7 * A7 S * (B7 S)^3 - S * A7 T * (C7 T)^3
      = -(S*T - 49) * q49 S T := by
  simp only [A7, B7, C7, q49]
  ring

def uvAux (S T : ℚ) : ℚ :=
    98*S^4*T^3 - S^3*T^4 + 1617*S^3*T^3 + 7203*S^3*T^2
  - 14*S^2*T^4 + 9555*S^2*T^3 + 112847*S^2*T^2 + 352947*S^2*T
  - 56*S*T^4 + 18179*S*T^3 + 468195*S*T^2 + 3882417*S*T
  + 11529602*S - 35*T^4 - 2744*T^3 - 33614*T^2 - 117649*T

def uvDen (S T : ℚ) : ℚ :=
    28*S^4*T^4 + 490*S^3*T^4 + 2744*S^3*T^3
  + 3136*S^2*T^4 + 43218*S^2*T^3 + 134456*S^2*T^2
  + S*T^5 + 7644*S*T^4 + 218491*S*T^3 + 1882384*S*T^2
  + 5764801*S*T + 7*T^5 + 3577*T^4 + 175273*T^3
  + 2705927*T^2 + 17294403*T + 40353607

def uvNum (S T : ℚ) : ℚ := -T * uvAux S T

def uvD (S T : ℚ) : ℚ := uvNum S T / uvDen S T
def uvX (S T : ℚ) : ℚ := uvD S T + 2
def uvY (S T : ℚ) : ℚ :=
  let d := uvD S T
  (T - 4*d^3 - 22*d^2 - 35*d - 7) / (d^2 + 7*d + 7)

def x049CurveNumerator (d T : ℚ) : ℚ :=
    T^2 - d^7 - 7*d^6 - 21*d^5 - 49*d^4
  - 7*d^3*T - 147*d^3 - 35*d^2*T - 343*d^2
  - 49*d*T - 343*d

theorem x049_curve_cleared_identity (d T : ℚ) :
    let A := d^2 + 7*d + 7
    let Y := T - 4*d^3 - 22*d^2 - 35*d - 7
    Y^2 + (d+2)*Y*A
      - ((d+2)^3 - (d+2)^2 - 2*(d+2) - 1)*A^2
      = x049CurveNumerator d T := by
  dsimp
  simp only [x049CurveNumerator]
  ring

theorem x049_numerator_from_quartic_and_cubic (d S T : ℚ) :
    x049CurveNumerator d T =
      (T^2
        - (S*T + 7*T + 147)*d^3
        - (7*S*T + 35*T + 343)*d^2
        - (21*S*T + 49*T + 343)*d
        - 49*S*T)
      - (d^4 - S*T)*(d^3 + 7*d^2 + 21*d + 49) := by
  simp only [x049CurveNumerator]
  ring

end

end MazurProof.X049BridgeFormulas
