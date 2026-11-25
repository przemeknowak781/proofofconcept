"""Interval-arithmetic certificate (mpmath.iv, 60 digits) for the numerical lemma of the paper (the maxima F_2, F_d,
F*_d of the one-variable functions f_d) and for the constants of Case C of the edge-inequality lemma.
All evaluation points are rational, so every number below is an enclosure of an explicit expression in logarithms
of rationals.  The monotonicity pattern of f_d is proved in the paper from Q_d(r) = (8r-1)((d-2)r-1); here we only
evaluate f_d at the candidate points and compare enclosures.
  theta = sqrt(27/8), L := log(theta) = 1/2 log(27/8).
  f_d(r) = 9/16 log(1+r) + 1/16 log r - (1/d + 1/8) log(r + 1/d).
  R*_d = (9d-1)/(d(3d+1)).   Candidate maximisers on (0,R]: R and the first critical point (1/8 for d = 2,
  min(1/8, 1/(d-2)) for d >= 3) if it is <= R.
The script also checks k <= theta^(k-1) for 3 <= k <= 2000 in exact integers (the paper proves it for all k >= 3 by
induction) and the decay constants z0, alpha, beta of the comparison lemma as exact rationals.
Prints ALL CERTIFIED only if every comparison below holds."""
from fractions import Fraction as Fr
from mpmath import iv
iv.dps = 60
def I(q): q = Fr(q); return iv.mpf(q.numerator) / iv.mpf(q.denominator)
L = iv.log(I(Fr(27, 8))) / 2
def f(d, r):
    r = Fr(r); return I(Fr(9, 16)) * iv.log(I(1 + r)) + iv.log(I(r)) / 16 - I(Fr(1, d) + Fr(1, 8)) * iv.log(I(r + Fr(1, d)))
def cands(d, R):
    c = [Fr(R)]
    s = Fr(1, 8) if d == 2 else min(Fr(1, 8), Fr(1, d - 2))
    if s <= R: c.append(s)
    return c
def upper(d, R): return max(f(d, r).b for r in cands(d, R))        # certified upper bound of max f_d on (0,R]
ok = True
F2 = upper(2, 1)
Fp = {d: upper(d, Fr(9 * d - 1, d * (3 * d + 1))) for d in range(3, 120)}
F = {d: upper(d, Fr(3, d)) for d in range(3, 120)}
half = L / 2
# exact identity f_4(1/8) = L/2 (proved symbolically in the text); here: enclosures overlap
e4 = f(4, Fr(1, 8)); print('f_4(1/8) in [%s, %s],  L/2 in [%s, %s]' % (iv.nstr(e4.a, 20), iv.nstr(e4.b, 20), iv.nstr(half.a, 20), iv.nstr(half.b, 20)))
# Case A: F'_d < L/2 strictly for d != 4;  on (0, R'_4] the other candidate f_4(R'_4) < L/2
for d in range(3, 120):
    if d == 4:
        v = f(4, Fr(35, 52)); good = v.b < half.a; print("d=4: f_4(R*_4) <= %s < L/2: %s" % (iv.nstr(v.b, 12), good)); ok &= bool(good)
    else:
        good = Fp[d] < half.a; ok &= bool(good)
        if not good: print('FAIL d =', d)
worst = max((Fp[d], d) for d in Fp if d != 4)
print("Case A: max_{d != 4} F*_d <= %s (d = %d);  L/2 >= %s;  margin >= %s" % (iv.nstr(worst[0], 15), worst[1], iv.nstr(half.a, 15), iv.nstr(half.a - worst[0], 8)))
# thresholds quoted in the paper
T = lambda q: I(Fr(q))
ok &= bool(worst[0] < half.a - T('0.0014').b)                       # F*_d < L/2 - 0.0014 for d != 4
ok &= bool(max(Fp[d] for d in range(7, 120)) < T('0.2959').a)       # F*_d < 0.2959 for 7 <= d <= 119
# Case B: F_2 + max F_d < L
mx = max((F[d], d) for d in F)
print('Case B: F_2 <= %s, max F_d <= %s (d = %d), sum <= %s < L >= %s: %s' % (iv.nstr(F2, 12), iv.nstr(mx[0], 12), mx[1], iv.nstr(F2 + mx[0], 12), iv.nstr(L.a, 12), bool(F2 + mx[0] < L.a)))
ok &= bool(F2 + mx[0] < L.a) and bool(F2 < T('0.230041').a) and bool(mx[0] < T('0.304973').a)
# Case C: log(21/20) + (log 3)/3 + 1/16 + [(log 120)/120 + 27/(16*123) + 1/16] < L
tot = iv.log(I(Fr(21, 20))) + iv.log(I(3)) / 3 + I(Fr(1, 16)) + iv.log(I(120)) / 120 + I(Fr(27, 16 * 123)) + I(Fr(1, 16))
print('Case C: total <= %s < L: %s' % (iv.nstr(tot.b, 12), bool(tot.b < L.a))); ok &= bool(tot.b < L.a)
c1 = iv.log(I(Fr(21, 20))); c2 = iv.log(I(3)) / 3 + I(Fr(1, 16)); c3 = iv.log(I(120)) / 120 + I(Fr(27, 16 * 123)) + I(Fr(1, 16))
ok &= bool(c1.b < T('0.048791').a) and bool(c2.b < T('0.428705').a) and bool(c3.b < T('0.116116').a)
ok &= bool((T('0.048791') + T('0.428705') + T('0.116116')).b < L.a)
# sup H_d for 2 <= d <= 119 is max(H_d(0+), H_d(R_d)) (text); certify both are <= (log 3)/3 + 1/16
def H0(d): return iv.log(I(d)) / d + I(Fr(1, 16))
def HR(d):
    R = Fr(1) if d == 2 else Fr(3, d)
    return -iv.log(I(Fr(1, d) + R)) / d + I(Fr(9, 16)) * I(R / (1 + R)) + I(Fr(1, 16))
bound = iv.log(I(3)) / 3 + I(Fr(1, 16))
good = all(H0(d).b < bound.a for d in range(2, 120) if d != 3) and all(HR(d).b < bound.a for d in range(2, 120))   # H_3(0+) is the bound itself
print('Case C: H_d(0+) and H_d(R_d) <= (log 3)/3 + 1/16 for 2 <= d <= 119:', bool(good)); ok &= bool(good)
# chain inequality k <= theta^(k-1), i.e. k^2 * 8^(k-1) <= 27^(k-1), exact integers, 3 <= k <= 2000 (induction step (k+1)/k <= 4/3 < theta)
print('k^2 8^(k-1) <= 27^(k-1) for 3 <= k <= 2000:', all(k * k * 8 ** (k - 1) <= 27 ** (k - 1) for k in range(3, 2001)))
# decay constants, exact
z, al, be = Fr(101, 100), Fr(77, 100), Fr(83, 100)
dec = (be >= z / (2 - z * al), al >= z / (3 - 2 * z * be), al <= be, z * be < 1, 1 / (1 - z * be) < 7)
print('decay constants exact:', *dec, float(1 / (1 - z * be))); ok &= all(dec)
ok &= all(k * k * 8 ** (k - 1) <= 27 ** (k - 1) for k in range(3, 2001))
print('ALL CERTIFIED' if ok else 'SOME CHECK FAILED')
