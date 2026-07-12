E = EllipticCurve('49a1')
print('LABEL', E.cremona_label())
print('A_INVS', E.a_invariants())
print('DISC', E.discriminant())
print('J', E.j_invariant())
print('RANK', E.rank())
print('TORSION', E.torsion_subgroup())
print('TORSION_POINTS', E.torsion_points())
print('ISOGENY_CLASS', [(C.cremona_label(), C.a_invariants()) for C in E.isogeny_class()])
print('CM', E.has_cm(), E.cm_discriminant() if E.has_cm() else None)
Em = EllipticCurve([0,21,0,112,0])
print('SHIFTED', Em.cremona_label(), Em.a_invariants(), Em.rank(), Em.torsion_subgroup(), Em.torsion_points())
Eh = EllipticCurve([0,-42,0,-7,0])
print('TWO_ISOG', Eh.cremona_label(), Eh.a_invariants(), Eh.rank(), Eh.torsion_subgroup(), Eh.torsion_points())
print('E_2DESC_GENS', E.gens(proof=True))
print('GENUS_X1_49', Gamma1(49).genus())
print('GENUS_X0_49', Gamma0(49).genus())

def has_primitive_solution(d,A,B,m,p):
    e = ZZ(B//d)
    squares = {ZZ(w*w % m) for w in range(m)}
    for u in range(m):
        for v in range(m):
            if u % p == 0 and v % p == 0:
                continue
            rhs = (d*u^4 + A*u^2*v^2 + e*v^4) % m
            if rhs in squares:
                return True
    return False

cases = [('E',21,112,[1,-1,2,-2,7,-7,14,-14]), ('EHAT',-42,-7,[1,-1,7,-7])]
moduli = [(4,2),(8,2),(16,2),(32,2),(7,7),(49,7),(3,3),(9,3),(5,5),(11,11),(13,13)]
for name,A,B,ds in cases:
    print('LOCAL_TABLE',name)
    for d in ds:
        obs=[m for m,p in moduli if not has_primitive_solution(d,A,B,m,p)]
        print('D',d,'OBSTRUCTIONS',obs)
