Qx.<z>=PolynomialRing(QQ)
K.<a>=NumberField(z^3-3*z-1)
OK=K.ring_of_integers(); P3=K.ideal(a-1); P2=K.ideal(2)
print('QUOTIENT_BEGIN')
for name,I in [('P3_5',P3^5),('P2',P2)]:
  try:
    Q=OK.quotient(I,'r')
    print('Q',name,Q,'TYPE',type(Q),'CARD',Q.cardinality())
    print('METHODS',[s for s in dir(Q) if any(k in s.lower() for k in ['list','iter','lift','cover','map','unit','element'])][:120])
    red=Q.coerce_map_from(OK)
    print('RED',red,'A',red(OK(a)),'PI',red(OK(a-1)))
    els=None
    for meth in ['list','elements']:
      if hasattr(Q,meth):
        try:
          els=getattr(Q,meth)(); print('ELMETHOD',meth,'LEN',len(els)); break
        except Exception as ex: print('ELERR',meth,repr(ex))
    if els is None:
      try: els=[Q(i) for i in range(Q.cardinality())]; print('COERCE_RANGE_LEN',len(set(els)))
      except Exception as ex: print('COERCE_RANGE_ERR',repr(ex))
    if els is not None:
      try:
        units=[x for x in els if x.is_unit()]
        cubes=set(x^3 for x in units)
        print('COUNTS',len(els),len(units),len(cubes))
        print('CUBES',cubes)
      except Exception as ex: print('COUNT_ERR',repr(ex))
  except Exception as ex: print('QERR',name,repr(ex))
print('QUOTIENT_END')