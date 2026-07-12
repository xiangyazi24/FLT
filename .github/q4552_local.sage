print('Q4552_LOCAL_BEGIN')
F.<g> = GF(2^6, modulus='primitive')
# Choose an element of exact order 9; conjugation over F8 is x |-> x^8.
z9 = next(x for x in F if x != 0 and x.multiplicative_order()==9)
z3 = z9^3
print('F64_GEN',g,'Z9',z9,'Z3',z3,'ZETA_REL',z3^2+z3+1)
for rr in [1,2]:
  alpha=z9^rr
  sols=[]
  for R in F:
    bar=R^8
    lhs=alpha*R^3-alpha^(-1)*bar^3
    rhs=(F(3))*(z3-z3^2)*(R*bar-F(3))
    if lhs==rhs: sols.append(R)
  print('FORWARD_COVER_MOD2',rr,'COUNT',len(sols),'SOLS',sols)
# Also record cube classes and the anti-invariant subgroup in F64^*/cubes.
cubes=set(x^3 for x in F if x!=0)
print('F64_CUBES',len(cubes),'QUOT',63//len(cubes),'Z9_CUBE',z9 in cubes,'Z9SQ_CUBE',z9^2 in cubes)
print('Q4552_LOCAL_END')
