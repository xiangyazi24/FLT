"""NEW 2026-10-30; exhaustive raw equation check, not smoothness or a Lean proof."""
from itertools import product
points = []
for x, y, z, w in product(range(2), repeat=4):
    if not (x or y or z or w):
        continue
    q = -x*z-x*w+y*y+y*z+z*w
    c = x*x*w+x*y*z-x*y*w-x*z*w+y*z*w+z*z*w-z*w*w
    if q % 2 == 0 and c % 2 == 0:
        points.append((x,y,z,w))
expected = [(0,0,0,1),(0,0,1,0),(0,1,1,0),(1,0,0,0),(1,1,0,1)]
assert points == expected
print('F2 projective points:', points)
print('count:', len(points))
print('PASS: all 15 nonzero binary quadruples checked; F2 has no nontrivial scaling.')
