"""Exact independent replay of the printed article's arithmetic.

Supplementary to the Lean proofs; uses the article's own logarithm remainder.
"""
import math
from fractions import Fraction as F

T = [0, 1, 3, 6, 10, 15, 21]
E = [0, 1, 3, 4, 8, 9, 11]


def poly(weights, x):
    return sum(x**j for j in weights)


def mean(weights, x):
    return sum(j*x**j for j in weights)/poly(weights, x)


def log_basic(x):
    eta = (x-1)/(x+1)
    mid = 2*sum(eta**(2*j+1)/F(2*j+1) for j in range(16))
    err = 2*abs(eta)**33/(33*(1-eta**2))
    return mid-err, mid+err


def scale_interval(k, interval):
    values = (k*interval[0], k*interval[1])
    return min(values), max(values)


def log_interval(x):
    assert x > 0
    y, k = x, 0
    while y < 1:
        y *= 2
        k -= 1
    while y >= 2:
        y /= 2
        k += 1
    lo, hi = log_basic(y)
    lo2, hi2 = scale_interval(k, log_basic(F(2)))
    return lo+lo2, hi+hi2


def rate_interval(weights, m, lo, hi):
    assert 0 < lo < hi < 1
    ml = mean(weights, lo)
    assert ml < m < mean(weights, hi)
    zl, zu = log_interval(poly(weights, lo))
    ll, lu = log_interval(lo)
    _, step_u = log_interval(hi/lo)
    return zl-m*lu-(m-ml)*step_u, zu-m*ll


def check_arithmetic():
    rows = [
        (6, 75, (112, 63, 21, 4, 0, 0), 75, 1850),
        (6, 100, (100, 64, 28, 7, 1, 0), 75, 4288),
        (7, 100, (100, 64, 28, 7, 1, 0, 0), 96, 1288),
        (7, 150, (86, 62, 33, 14, 4, 1, 0), 96, 1391),
    ]
    for q, k, counts, u, expected in rows:
        assert sum(counts) == 200
        assert sum(j*c for j, c in zip(T, counts)) == 2*k
        denominator = math.prod(c**c for c in counts)
        ratio = F(200**200)*F(u, 200)**k/(F(13, 10)**200*poly(E[:q], F(u, 200))**200*denominator)
        assert (1000*ratio).__floor__() == expected
        assert ratio > F(5, 4)
        print(f"PASS: printed M=200 row Q={q}, K={k}, u={u}; floor(1000R)={expected}.")
        if q == 6:
            amended = ratio*(poly(E[:6], F(u, 200))/poly(E, F(u, 200)))**200
            assert amended > F(5, 4)
            print(f"PASS: Lean alternative with Q=7 also has R>5/4 at K={k}.")
    t = F(131, 200)
    assert 1 < mean(T, t) < F(11, 10)
    assert poly(T, t) > F(203140, 100000) > F(329, 250)*F(154361, 100000) > F(329, 250)*poly(E, t*t)
    print("PASS: subsequence mean and the printed exact strict ratio chain.")
    for q, d, kt, ks, lower, upper in [
        (6, F(371979, 10**6), 562503, 342209, 269455401, 269455403),
        (7, F(743958, 10**6), 733755, 517230, 269455447, 269455448),
        (6, F(371980, 10**6), 562504, 342210, 269455480, 269455481),
        (7, F(743960, 10**6), 733755, 517231, 269455367, 269455368),
    ]:
        al, au = rate_interval(T[:q], 2*d, F(kt, 10**6), F(kt+1, 10**6))
        el, eu = rate_interval(E[:q], d, F(ks, 10**6), F(ks+1, 10**6))
        assert F(lower, 10**9) < al-eu <= au-el < F(upper, 10**9)
        print(f"PASS: printed crossing row Q={q}, delta={d}, using the article's own log rule.")
    assert log_interval(F(1309251, 10**6))[1] < F(269455219, 10**9)
    assert F(269455900, 10**9) < log_interval(F(1309252, 10**6))[0]
    print("PASS: both printed logarithmic bounds for C_*.")
    for index, (q, d, k, sl, su, lower) in enumerate([
        (6, F(21, 50), 595, F(342209, 10**6), F(342211, 10**6), 270365),
        (6, F(21, 50), 595, F(2, 5), F(2, 5), 270573),
        (6, F(11, 20), 665, F(2, 5), F(2, 5), 270652),
        (7, F(11, 20), 664, F(12, 25), F(12, 25), 270484),
        (7, F(17, 25), 714, F(12, 25), F(12, 25), 271274),
        (7, F(17, 25), 714, F(517230, 10**6), F(517232, 10**6), 270342),
    ], 1):
        al, _ = rate_interval(T[:q], 2*d, F(k, 1000), F(k+1, 1000))
        assert F(lower, 10**6) < al-log_interval(poly(E[:q], su))[1]+d*log_interval(sl)[0]
        print(f"PASS: printed interior endpoint row {index}, with the article's log rule.")


if __name__ == "__main__":
    check_arithmetic()
