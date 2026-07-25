import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0

example
    (x y A B r : Rat)
    (hy : y != 0)
    (hd : x - r != 0)
    (he : (x - r)^2 - (3*r^2 + A) != 0)
    (hx3 : ((3*x^2 + A)/(2*y))^2 - 2*x - r != 0)
    (hc : y^2 = x^3 + A*x + B)
    (ht : r^3 + A*r + B = 0) :
    let t : Rat := 3*r^2 + A
    let ell : Rat := (3*x^2 + A)/(2*y)
    let x3 : Rat := ell^2 - 2*x
    let X : Rat := x + t/(x-r)
    let Y : Rat := y*((x-r)^2-t)/(x-r)^2
    let ellp : Rat := (3*X^2 + (A-5*t))/(2*Y)
    x3 + t/(x3-r) = ellp^2 - 2*X := by
  dsimp
  let t : Rat := 3*r^2 + A
  let d : Rat := x-r
  let e : Rat := d^2-t
  let u : Rat := 3*x^2+A
  let m : Rat := x*d+t
  let p : Rat := 3*m^2+(A-5*t)*d^2
  let h : Rat := 2*x+r
  let q : Rat := 2*t-d*h
  let f0 : Rat := x^3+A*x-r^3-A*r
  let C : Rat := d*h*p^2 + e^2*(u^2*q-12*t*(x+r)*(y^2+f0))
  field_simp [hy, hd, he, hx3]
  linear_combination (16*y^2*C)*hc + (16*y^2*C)*ht
