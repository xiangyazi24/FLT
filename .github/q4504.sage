from sage.all import *

print('Q4504_BEGIN')
X0 = EllipticCurve(QQ,[0,1,1,-9,-15])
print('X0_AINVS',X0.ainvs())
print('X0_DISC',X0.discriminant(),'J',X0.j_invariant(),'RANK',X0.rank())
print('X0_TORSION',X0.torsion_subgroup())
print('X0_TORSION_POINTS',X0.torsion_points())
for sign in [1,-1]:
    try:
        ms=X0.modular_symbol(sign=sign)
        print('MODSYM',sign,'AT0',ms(0))
    except Exception as ex:
        print('MODSYM_ERR',sign,repr(ex))
try:
    L=X0.period_lattice()
    print('PERIOD_BASIS',L.basis())
    for P in X0.torsion_points():
        if not P.is_zero():
            try:
                print('ELLLOG',P,L.elliptic_logarithm(P))
            except Exception as ex:
                print('ELLLOG_ERR',P,repr(ex))
except Exception as ex:
    print('PERIOD_ERR',repr(ex))

for lab in ['361a1','361b1']:
    try:
        E=EllipticCurve(lab)
        cm=None
        try: cm=E.cm_discriminant()
        except Exception: cm='none'
        print('CURVE',lab,'AINVS',E.ainvs(),'DISC',E.discriminant(),'J',E.j_invariant(),'RANK',E.rank(),'CM',cm)
        print('ISOG_CLASS',[(C.cremona_label(),C.ainvs(),C.j_invariant()) for C in E.isogeny_class().curves])
        print('ISOG_MATRIX',E.isogeny_class().matrix())
        try:
            isogs=E.isogenies_prime_degree(19)
            print('ISOG19_COUNT',len(isogs))
            for i,phi in enumerate(isogs):
                print('ISOG19',i,'CODOMAIN',phi.codomain().ainvs())
                print('ISOG19_KERNEL_POLY',phi.kernel_polynomial())
                print('ISOG19_KERNEL_MOD2',phi.kernel_polynomial().change_ring(GF(2)))
        except Exception as ex:
            print('ISOG19_ERR',repr(ex))
    except Exception as ex:
        print('CURVE_ERR',lab,repr(ex))

try:
    CDB=CremonaDatabase()
    curves=CDB.allcurves(361)
    print('ALL361',curves)
except Exception as ex:
    print('ALL361_ERR',repr(ex))
print('Q4504_END')
