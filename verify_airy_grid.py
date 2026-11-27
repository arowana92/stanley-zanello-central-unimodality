"""Rational residual bounds for sampling the Dirichlet Airy eigenfunction."""

from decimal import Decimal, localcontext
from fractions import Fraction as Q
from math import ceil, comb, floor

from verify_rising import PI_LO, decay, exp_small_upper, sqrt_hi, sqrt_lo


T = Q("1.12")
E = Q("2.81")
D = Q(".01")


def add(p, q):
    return [a+b for a, b in zip(p+[0]*len(q), q+[0]*len(p))][:max(len(p), len(q))]


def derivative(p):
    return [i*p[i] for i in range(1, len(p))]


def next_pair(pair):
    # Majorize the absolute polynomial coefficients in (P f + Q f')'.
    p, q = pair
    yq = add([E*v for v in q], [0]+[T*v for v in q])
    return add(derivative(p), yq), add(p, derivative(q))


def check_residual():
    assert Q("2.60")**3*T**2 < E**3
    moments = [Q(1)]
    for j in range(14):
        moments.append((1+E/Q(".88"))*moments[j]
                       + Q(j*j,4)/Q(".88")*moments[max(j-2,0)])
    f_bounds = [sqrt_hi(moments[2*k]) for k in range(8)]
    fp_bounds = [
        sqrt_hi(E*moments[2*k] + k*k*moments[max(2*k-2,0)])
        + k*f_bounds[max(k-1,0)] for k in range(8)
    ]

    def norm(pair):
        return sum(a*b for a,b in zip(pair[0],f_bounds)) + sum(
            a*b for a,b in zip(pair[1],fp_bounds))

    def bound(fn, order=0, potential=0, grid=False):
        pair = fn
        for _ in range(order):
            pair = next_pair(pair)
        pair = tuple([0]*potential+[T**potential*v for v in poly] for poly in pair)
        assert max(map(len,pair)) < len(f_bounds)
        value = norm(pair)
        if grid:
            differentiated = next_pair(pair)
            assert max(map(len,differentiated)) <= len(f_bounds)
            value += D*norm(differentiated)
        return value

    f = ([1], [])
    correction = ([0,2*T/15], [0,2*E/30,T/30])
    # Taylor remainder for B f through d^4, divided by d^6.
    airy = (bound(f,6)/120 + bound(f,potential=3,grid=True)/48
            + bound(f,2,2,True)/16 + bound(f,4,1,True)/48
            + T*bound(f,1,1,True)/8 + T*bound(f,3)/8 + Q(".07")*bound(f,grid=True))
    # Taylor remainder for B F through d^2, divided by d^4.
    corrected = (bound(correction,4)/6 + bound(correction,potential=2,grid=True)/8
                 + bound(correction,2,1,True)/4 + Q(".30")*bound(correction,1)
                 + Q(".07")*D**2*bound(correction,grid=True))
    F0 = bound(correction,grid=True)
    assert airy < 29 and corrected < 150
    assert F0 < 4
    assert airy+corrected+bound(f,grid=True)+Q("1.3")*F0 < 200
    assert (1-2*D*sqrt_hi(E))/sqrt_hi(2) - D**2*F0 > Q(".68")
    # Exponential shift and the cost of passing to the even two-step operator.
    assert exp_small_upper(3*T*D**3/4)*(2/Q(".68"))*200 < 600
    assert E**2/30 < Q(".264")
    b = E/2 + E**2*D**2/60
    assert b**3/6 + E**3/120 + E**4*D**2/7200 < 1
    assert b*b/2 + E**2/60 < Q("1.3")


def check_energy():
    h = 100
    ang = PI_LO/(Q("1.5")*h+1)
    assert h**2*(ang-ang**3/6)**2 > Q("4.3")
    assert (1-Q("2.60")/h**2)*(Q("1.5")-Q("1.5")**2/(2*h*h)) > Q("1.48")
    assert (Q("3.15")-Q("2.60"))*(1-Q("3.15")/h**2) > Q(".54")
    assert Q(600,h**4) < Q(".54")
    assert Q(".88")*Q("1.05")**3 > 1
    assert Q(".12")*(Q("2.60")*Q(2,3)*Q("1.05") + Q(3,2*h)
                      + Q(".264")*Q(4,3)*Q("1.05")/h**2) + Q(600,h**4) < Q(".24")
    projection = 1/(1-Q(".12")*Q("5.52"))
    assert projection < Q("2.97")
    lost = projection * 600 / (Q(".74")-Q(".24")) / h**4
    assert (1-Q(".01"))*(1-lost)*2000 > projection*600
    # The principal branch log differs by at most distance / .99 on the segment.
    assert Q(3,h*h)+Q(2000,h**6) < Q(".01")
    err = Q(2000,h**4)
    assert Q(2,9)*Q("1.65")-Q(".264")*Q(4,9)/h**2-2*err/Q(".12")**2 > Q(".35")
    assert Q(2,9)*Q("2.60")+2*err/Q(".12")**2 < Q(".60")
    for radius, bound in ((Q(".01"),1),(Q(".08"),3)):
        assert (Q(8,27)*Q("2.60")/(1-radius)**3
                + Q(8,27)*Q(".264")/(h*h*(1-radius)**3)
                + 6*err/(Q(".12")-radius)**3) < bound
    assert Q("1.65")*Q(".109")-Q(2,9)*Q(".264")/h**2-err/(Q(".12")**2-Q(".08")**2) > Q(".17")
    assert Q(3,2*h)+err/Q(".12") < Q(".016")


def check_warm_blocks():
    h = 110
    assert (Q(h,100))**3 > Q(6,5)
    b = Q(6,5)
    error = Q(2000,100**4)*(1+b)  # scaled errors in both real energies
    z = Q(".999")**3*Q("4.5")**2/16
    moment = (comb(24,12)+2*sum(comb(24,12+j)*decay(j*j*z)
                                 for j in range(1,13)))/Q(2**24)
    assert exp_small_upper(6*(Q("2.60")*Q(".059")+error))*moment < Q(".924")**6
    assert 12*9 < h*PI_LO and Q(1,2)*45 < h*PI_LO
    assert 100*exp_small_upper(Q("5.23")/4)**4 < 20000
    assert 1+(20000*decay(Q("1.48")*18))**2 < Q("1.001")
    assert Q(".996")*Q(".185")*(Q(9,54))**2 > Q(".005")
    assert (Q(".124")*Q("1.99")-Q(".04"))**3*45**2 > Q("2.61")**3
    assert (Q("1.99")/75-Q(1,80))**3*(10**4)**2 > Q("2.61")**3
    assert Q(h**3,64) > 10**4
    assert (Q(".92")**4)*(Q(".68")/Q(".60"))**3 > 1


def check_growth_integral():
    n = 100000
    dl = sqrt_lo(Q(".35")*(n-401))
    dh = sqrt_hi(Q(".60")*n)
    assert Q("1.001")*(Q("11.70")**2+2*Q("11.70")+2)/Q(".08")**2 < 26000
    assert Q(".999")*sqrt_lo(2*PI_LO)*(1-Q(26000,2)/dl**2) > Q("1.55")
    assert Q(".17")/Q(".60") > Q(".28")
    assert Q("1.001")*3/(6*Q(".35")*dl*Q(".28")**2) < Q(".10")
    assert Q("1.002")*Q("1.001")/(Q(".28")*dl) < Q(".020")
    assert Q(".08")*dl > 14
    assert (Q("1.001")*2*decay(Q(14**2,2))/14
            + 5*decay(Q(".16")*400-20)) < Q(".001")
    # The frequency integrals include the unit term and 1.001 |y|.
    for left, right, rate, target in ((".08",".2",".0034","1.27"),(".2","1",".00249",".002")):
        l, r, c = Q(left), Q(right), Q(rate)*(n-42)
        assert Q("1.01")*(1+Q("1.001")*r)*dh*decay(c*l*l)/(c*l) < Q(target)
    assert 2*Q("1.01")*45*dh*(1+Q("1.001")*45)*decay(Q(".00093")*(n-42)) < Q(".001")
    assert 2*Q("1.01")*45*dh*(1+Q("1.001")*45)*decay(Q(".005")*(n-42)) < Q(".001")
    assert 2*dh*(1+Q("1.001"))*Q(".08")*decay(Q(".16")*n-20) < Q(".001")
    assert Q("1.55")-Q(".10")-Q(".020")-Q("1.27")-Q(".002")-Q(".01") > 0
    assert 500**2*(Q("1.10")-Q(".016"))**2/(Q("2.001")**3*Q(".565")**2) > n


def finite_norm_bracket(h):
    """Enclose the infinite real Jacobi norm by two finite Sturm tests."""
    scale = 2**64
    size = 16*h
    # Bound exp(-1/(2 h^3)) between adjacent alternating Taylor sums.
    term = value = Q(1)
    for j in range(1, 13):
        term *= Q(-1, 2*h**3*j)
        value += term
    lower = value + term*Q(-1, 26*h**3)
    lo_q = floor(lower*scale)
    hi_q = ceil(value*scale)
    lo_edges, hi_edges = [scale], [scale]
    for _ in range(1, size):
        lo_edges.append(lo_edges[-1]*lo_q//scale)
        hi_edges.append(-(-hi_edges[-1]*hi_q//scale))

    def bracket(edges, final_diagonal):
        def above_root(x):
            last, previous = 1, 0
            for j in range(size):
                diag = final_diagonal if j == size-1 else 0
                minor = (x-diag)*last
                if j:
                    minor -= edges[j-1]**2*previous
                if minor <= 0:
                    return False
                previous, last = last, minor
            return True

        low, high = scale, 2*scale+1
        assert not above_root(low) and above_root(high)
        while high-low > 1:
            middle = (low+high)//2
            if above_root(middle):
                high = middle
            else:
                low = middle
        return low, high

    lo = bracket(lo_edges, 0)[0]
    hi = bracket(hi_edges, hi_edges[-1])[1]
    assert 2*hi_edges[-1] < lo  # Tail norm after cutting the last edge.
    assert 0 < hi-lo < 4096
    return lo, hi, scale


def finite_energy(h):
    lo, hi, scale = finite_norm_bracket(h)
    # Decimal exp/ln are correctly rounded to nearest in this context.
    # Only use the midpoint for displaying an estimate of the Airy zero.
    with localcontext() as ctx:
        ctx.prec = 40
        rho_over_two = Decimal(lo+hi)/(4*scale)
        target = -2*h*h*rho_over_two.ln() + Decimal(3)/(2*h)
        return 2*target/(1+(1+2*target/(15*h*h)).sqrt())


if __name__ == "__main__":
    check_residual()
    check_energy()
    check_warm_blocks()
    check_growth_integral()
    for h in (8,16,32):
        print(f"H = {h:2d}, corrected energy estimate of a = {finite_energy(h):.10f}")
    print("Verified the corrected Airy residual, complex energy disk and 100000-block growth saddle.")
