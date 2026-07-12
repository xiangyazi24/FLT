J=JH(25,[1,7,18,24])
print('A4_BEGIN')
print('J',J,'DIM',J.dimension())
try:
    D=J.newform_decomposition('a')
    print('NEWFORM_DECOMP',D)
except Exception as e: print('NEWFORM_DECOMP_ERR',repr(e)); D=[]
try:
    dec=J.decomposition()
except Exception as e: print('DEC_ERR',repr(e)); dec=[]
for i,A in enumerate(dec):
    print('FACTOR',i,A,'DIM',A.dimension(),'LABEL',A.label() if hasattr(A,'label') else 'NA')
    for meth in ['newform','newform_label','newform_level','is_simple','endomorphism_ring','endomorphism_generators','rational_torsion_order','rational_cusp_subgroup','rational_cuspidal_subgroup']:
        if hasattr(A,meth):
            try:
                args=('a',) if meth=='newform' else ()
                x=getattr(A,meth)(*args)
                print(' METHOD',meth,x)
                if hasattr(x,'order'):
                    try: print('  ORDER',x.order())
                    except Exception as e: print('  ORDER_ERR',repr(e))
            except Exception as e: print(' METHOD_ERR',meth,repr(e))
    try:
        f=A.newform('a')
        print('NF',f)
        print('NF_LEVEL',f.level(),'CHAR',f.character(),'BASE',f.base_ring(),'DEG',f.base_ring().degree())
        print('NF_QEXP',f.q_expansion(20))
        print('NF_CM_METHODS',[s for s in dir(f) if 'cm' in s.lower() or 'twist' in s.lower() or 'rank' in s.lower() or 'lseries' in s.lower()])
        for meth in ['has_cm','cm_discriminant','analytic_rank','lseries']:
            if hasattr(f,meth):
                try: print(' NF_METHOD',meth,getattr(f,meth)())
                except Exception as e: print(' NF_METHOD_ERR',meth,repr(e))
    except Exception as e: print('NF_ERR',repr(e))
print('A4_END')
