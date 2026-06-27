# Update

For odd m, top x exponent is (m^2 - 1)/2.
For even m, the non-2 factor has top x exponent (m^2 - 4)/2. Including the cubic 2-part gives (m^2 + 2)/2.
Using psi_m squared gives m^2 - 1 with multiplicities.

The elementary size estimate is quadratic in m, so it cannot prove the target linear estimate #E(R)[m] <= 2*m.

For odd m, the sharp theorem needed is: the number of real x-values satisfying the odd x-equation is at most m - 1.
For even m, the raw m - 1 statement is false at m = 2; split off the cubic 2-part and bound the non-2 part by m - 2.

Even count: 1 point at infinity, at most 3 affine 2-part points, and at most 2*(m - 2) other affine points, total 2*m.
