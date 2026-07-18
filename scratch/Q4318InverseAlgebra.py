import sympy as sp
x,a,h,y=sp.symbols('x a h y')
f=x**8-4*x**7-6*x**6-4*x**5-9*x**4+4*x**3-6*x**2+4*x+1
Pa=x**6-5*x**5+5*x**3-5*x-1
Qa=1+3*x-x**2
Ph=x**8-7*x**7+7*x**6+14*x**5+14*x**3-7*x**2-7*x-1
Qh=x**4-5*x**3+2*x**2+5*x+1
cross=sp.expand((2*a*x**5-Pa)*Qh-(2*h*x**7-Ph)*Qa)
print('cross factor=',sp.factor(cross))
print('cross degree=',sp.Poly(cross,x).degree())
F=h*(a**2+13*a+49)*(a**2+5*a+1)**3-a*(h**2+10*h+5)**3
# Groebner eliminate high powers using F doesn't involve x, so no direct simplification.
# Solve for h or a if cross linear in one parameter.
print('cross coefficients a,h:',sp.factor(sp.diff(cross,a)),sp.factor(sp.diff(cross,h)),sp.factor(cross.subs({a:0,h:0})))
# Resultant with hyperell condition after y=(2a x^5-Pa)/Qa.
rel=sp.together((2*a*x**5-Pa)**2-Qa**2*f).as_numer_denom()[0]
print('rel factor=',sp.factor(rel))
print('resultant cross,rel in x start')
res=sp.factor(sp.resultant(cross,rel,x))
print('resultant factor=',res)
