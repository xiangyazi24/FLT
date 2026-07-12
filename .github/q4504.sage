from sage.all import *

print('Q4504_BEGIN')
X0 = EllipticCurve(QQ,[0,1,1,-9,-15])
print('X0_AINVS',X0.ainvs())
print('X0_DISC',X0.discriminant(),'J',X0.j_invariant(),'RANK',X0.rank())
print('X0_TORSION',X0.torsion_subgroup())
print('X0_TORSION_POINTS',X0.torsion_points())

for lab in ['361a1','361b1']:
    try:
        E=EllipticCurve(lab)
        print('CURVE',lab,'AINVS',E.ainvs(),'DISC',E.discriminant(),'J',E.j_invariant(),'RANK',E.rank(),'CM',E.cm_discriminant())
        print('ISOG_CLASS',[(C.cremona_label(),C.ainvs(),C.j_invariant()) for C in E.isogeny_class().curves])
        print('ISOG_MATRIX',E.isogeny_class().matrix())
        try:
            isogs=E.isogenies_prime_degree(19)
            print('ISOG19_COUNT',len(isogs))
            for i,phi in enumerate(isogs):
                print('ISOG19',i,'CODOMAIN',phi.codomain().ainvs())
                print('ISOG19_KERNEL_POLY',phi.kernel_polynomial())
                print('ISOG19_MAPS',phi.rational_maps())
        except Exception as ex:
            print('ISOG19_ERR',repr(ex))
    except Exception as ex:
        print('CURVE_ERR',lab,repr(ex))

# Search all conductor-361 curves available in the local Cremona database.
try:
    CDB=CremonaDatabase()
    curves=CDB.allcurves(361)
    print('ALL361',curves)
except Exception as ex:
    print('ALL361_ERR',repr(ex))
print('Q4504_END')
