from sage.all import *

print('Q4518_BEGIN')
R.<T> = PolynomialRing(QQ)
L.<a> = NumberField(T^3-3*T-1)
E = EllipticCurve(L,[1,-1,1,-5,5])
T3 = E(1,0)

# Exact quotient constants from the verified Q4399 computation.
A  = -a-1
q  = a^2-1
rp = a^2-a-2
rm = -a^2-a
ku = 4*a^2+8*a+3
kv = a^2+a-1
lu = 8*a^2+16*a+6
f = lambda x: x^6+4*x^5+10*x^4+10*x^3+5*x^2+2*x+1

pts = E.torsion_points()
gens = [P for P in pts if P.order()==21 and 7*P==T3]
assert len(gens) > 0
G = sorted(gens, key=lambda P: (str(P[0]),str(P[1])))[0]
print('GENERATOR_G',G)
print('CHECK_7G',7*G)
print('SEVEN_TORSION_S_EQ_3G',3*G)
print('TORSION_CARD',len(pts))
print('TORSION_STRUCTURE',E.torsion_subgroup())

# Helpers.
def qstr(x):
    return str(L(x))

def is_Q(x):
    p=L(x).polynomial()
    return p.degree() <= 0

def cusp_label(x,y=None,inf=None):
    if inf == '+': return 'Q_CUSP_INFINITY_PLUS'
    if inf == '-': return 'Q_CUSP_INFINITY_MINUS'
    if is_Q(x) and is_Q(y):
        xx=QQ(L(x)); yy=QQ(L(y))
        if xx==0 and yy==1: return 'Q_CUSP_X0_Y1'
        if xx==0 and yy==-1: return 'Q_CUSP_X0_YM1'
        if xx==-1 and yy==1: return 'Q_CUSP_XM1_Y1'
        if xx==-1 and yy==-1: return 'Q_CUSP_XM1_YM1'
        return 'Q_RATIONAL_NONCUSP'
    return 'L_RATIONAL_NON_Q'

def qplus_finite(x,y):
    z=(x-rp)/(x-rm)
    u=z^2
    v=(z-1)^3*y
    X0=(ku*u+3)/2
    Y0=(kv*v-lu*u-10)/8
    return E(X0,Y0)

# Infinity images: z=1, v=-8 q^3 for + and +8 q^3 for -.
v_inf_plus=-8*q^3
v_inf_minus=8*q^3
P_inf_plus=E((ku+3)/2,(kv*v_inf_plus-lu-10)/8)
P_inf_minus=E((ku+3)/2,(kv*v_inf_minus-lu-10)/8)
print('INF_PLUS_IMAGE',P_inf_plus)
print('INF_MINUS_IMAGE',P_inf_minus)
print('INF_PLUS_K',next(k for k in range(21) if k*G==P_inf_plus))
print('INF_MINUS_K',next(k for k in range(21) if k*G==P_inf_minus))

# Print all 21 elliptic points and fibers.
distinct_count=0
q_rational=[]
l_rational=[]
non_l=[]
ramified=[]

for k in range(21):
    P=k*G
    print('ROW_BEGIN',k)
    print('P',P)
    print('ORDER',P.order())
    if P.is_zero():
        fr=f(rm)
        print('TYPE O_FIBER')
        print('X_RM',qstr(rm))
        print('F_RM',qstr(fr))
        sq=fr.is_square()
        print('F_RM_SQUARE_IN_L',sq)
        if sq:
            sy=fr.sqrt()
            for sign,yy in [('+',sy),('-',-sy)]:
                assert qplus_finite(rm,yy).is_zero()
                lab=cusp_label(rm,yy)
                print('FIBER',sign,'X',qstr(rm),'Y',qstr(yy),'MARK',lab)
                l_rational.append((k,sign,rm,yy,lab))
            distinct_count += 2
        else:
            print('FIBER +/- X',qstr(rm),'Y2',qstr(fr),'MARK QUADRATIC_OVER_L')
            non_l.extend([(k,'+'),(k,'-')])
            distinct_count += 2
        print('ROW_END',k)
        continue
    X0,Y0=P[0],P[1]
    u=(2*X0-3)/ku
    v=(8*Y0+lu*u+10)/kv
    # Verify quotient cubic indirectly from E equation and formulas by reconstruction where possible.
    print('U',qstr(u))
    print('V',qstr(v))
    if u==0:
        z=L(0); x=rp; y=-v
        assert y^2==f(x)
        assert qplus_finite(x,y)==P
        lab=cusp_label(x,y)
        print('TYPE RAMIFIED_U0')
        print('FIBER 0 X',qstr(x),'Y',qstr(y),'MARK',lab,'MULTIPLICITY 2')
        ramified.append(k)
        l_rational.append((k,'0',x,y,lab))
        if lab.startswith('Q_'): q_rational.append((k,'0',x,y,lab))
        distinct_count += 1
    elif u==1:
        print('TYPE U1_ONE_INFINITY_ONE_FINITE')
        # z=-1 finite point.
        z=L(-1); x=(z*rm-rp)/(z-1); y=v/(z-1)^3
        assert y^2==f(x)
        assert qplus_finite(x,y)==P
        lab=cusp_label(x,y)
        print('FIBER Z=-1 X',qstr(x),'Y',qstr(y),'MARK',lab)
        l_rational.append((k,'-1',x,y,lab))
        if lab.startswith('Q_'): q_rational.append((k,'-1',x,y,lab))
        # z=1 infinity; v selects sign.
        if v==v_inf_plus:
            lab2='Q_CUSP_INFINITY_PLUS'; inf='+'
        elif v==v_inf_minus:
            lab2='Q_CUSP_INFINITY_MINUS'; inf='-'
        else:
            lab2='INVALID_INFINITY_V'; inf='?'
        print('FIBER Z=1 INFINITY',inf,'MARK',lab2)
        q_rational.append((k,'inf'+inf,None,None,lab2))
        distinct_count += 2
    else:
        sq=u.is_square()
        print('TYPE REGULAR_U')
        print('U_SQUARE_IN_L',sq)
        if sq:
            s=L(u.sqrt())
            for sign,z in [('+',s),('-',-s)]:
                assert z != 1
                x=(z*rm-rp)/(z-1)
                y=v/(z-1)^3
                assert y^2==f(x)
                assert qplus_finite(x,y)==P
                lab=cusp_label(x,y)
                print('FIBER',sign,'Z',qstr(z),'X',qstr(x),'Y',qstr(y),'MARK',lab)
                l_rational.append((k,sign,x,y,lab))
                if lab.startswith('Q_'): q_rational.append((k,sign,x,y,lab))
            distinct_count += 2
        else:
            print('FIBER +/- Z2',qstr(u),
                  'X_FORMULA (z*rm-rp)/(z-1)',
                  'Y_FORMULA v/(z-1)^3',
                  'MARK QUADRATIC_OVER_L')
            non_l.extend([(k,'+'),(k,'-')])
            distinct_count += 2
    print('ROW_END',k)

print('DISTINCT_GEOMETRIC_FIBER_POINTS',distinct_count)
print('RAMIFIED_ROWS',ramified)
print('L_RATIONAL_ENTRY_COUNT',len(l_rational))
print('NON_L_ENTRY_COUNT',len(non_l))
print('Q_RATIONAL_ENTRY_COUNT',len(q_rational))
for e in q_rational:
    print('Q_ENTRY',e[0],e[1],e[4],'' if e[2] is None else qstr(e[2]),'' if e[3] is None else qstr(e[3]))
print('Q4518_END')
