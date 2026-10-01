"""Independent exact polynomial checks; does not import or execute project code."""
import json
import sympy as S

s0, s1, x, y, t, a0, a1, b0, b1 = S.symbols("s0 s1 x y t a0 a1 b0 b1")
M = S.Matrix([[0, 0, 1, 0], [0, 0, 1, 1],
              [1, 0, s0, 1], [1, 1, s1, 1+s1]])
N = S.Matrix([[1-s0, -1, 1, 0], [s0, -s1, -1, 1],
              [1, 0, 0, 0], [-1, 1, 0, 0]])
assert (M*N-S.eye(4)).applyfunc(S.expand) == S.zeros(4)
U, A, b = x*x+x, x*x+a1*x+a0, b0+b1*x
H, T = x**3+x+1, x**3
F = U*A*A-A*b*H-b*b*T
C = y*y+H*y-U*T
Num, G = U*A+b*y, A*y-b*T
D = lambda p: S.diff(p, x)+t*S.diff(p, y)
assert S.expand(F*y-(G*Num-A*b*C)) == 0
rhs = G*D(Num)+D(G)*Num-t*F-(S.diff(A, x)*b+A*b1)*C-A*b*D(C)
assert S.expand(S.diff(F, x)*y-rhs) == 0
norm = (U*A)**2-(U*A)*b*H-b*b*(x**5+x**4)
assert S.expand(norm-U*F) == 0
assert S.expand(D(C)-((2*y+H)*t+(3*x*x+1)*y-(5*x**4+4*x**3))) == 0
print(json.dumps({"status": "PASS", "symbolic_identities": [
    "4x4 residue inverse product", "residual value identity",
    "residual derivative identity", "norm base factor",
    "implicit opposite-sheet slope relation"],
    "project_code_executed": False, "lean_executed": False}, indent=2))
