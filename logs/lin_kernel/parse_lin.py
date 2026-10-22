"""Parse Lin's frozen Lean coefficient file (untrusted text; regex only, nothing executed) into our spec format."""
import re, sys, json
from fractions import Fraction
src = open(sys.argv[1], encoding='utf-8').read()
ent = re.findall(r'\(\s*(\d+)\s*,\s*(\d+)\s*,\s*\(\s*(-?\d+)\s*:\s*ℚ\s*\)\s*/\s*(\d+)\s*\)', src)
print('entries', len(ent))
a = {}
for I, J, num, den in ent:
    I, J = int(I), int(J)
    key = f'{max(I,J)},{min(I,J)}'
    if key in a:
        print('duplicate', key)
    a[key] = str(Fraction(int(num), int(den)))
imax = max(int(k.split(',')[0]) for k in a)
jgt = [k for k in a if int(k.split(',')[1]) > int(k.split(',')[0])]
print('max index', imax, 'J>I entries', len(jgt))
# other constants mentioned in the file
for pat in ['alpha', 'radius', 'singular', 'amp', 'coef', '11248245541992991']:
    for m in re.finditer(pat, src):
        s = src[max(0, m.start()-80): m.end()+80].replace('\n', ' ')
        print('...', s)
        break
spec = dict(alpha='6/5', R='7/4', h='1/16', N=imax + 0, c=str(Fraction(11248245541992991, 6250000000000000)), a=a,
            source='Lin partial-balayage-lean commit 0055cdf5 Coefficients.lean (via sentinel download)')
json.dump(spec, open(sys.argv[2], 'w'))
print('wrote', sys.argv[2])
