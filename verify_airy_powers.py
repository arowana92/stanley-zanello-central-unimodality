"""Rational constants for the large-height transfer powers and saddle inversion."""

from fractions import Fraction as Q

from verify_rising import PI_LO, decay, exp_small_upper, sqrt_hi, sqrt_lo


def check_samples():
    # Bounds for x^j f and x^j f' in continuous L2. Re t = 1.
    energy, tilt = Q("3.3"), Q("1.42")
    assert energy**3 > Q("2.60")**3 * tilt**2
    moments = [Q(1)]
    for j in range(6):
        moments.append((1+energy)*moments[j] + Q(j*j, 4)*moments[max(j-2, 0)])
    f = [sqrt_hi(moments[2*j]) for j in range(4)]
    fp = [sqrt_hi(energy*moments[2*j] + j*j*moments[max(2*j-2, 0)])
          + j*f[max(j-1, 0)] for j in range(4)]
    d = Q(1, 10000)
    grid = [f[j] + d*(j*f[max(j-1, 0)] + fp[j]) for j in range(3)]
    fourth = 2*tilt*fp[0] + tilt**2*f[2] + 2*energy*tilt*f[1] + energy**2
    residual = (fourth/6 + tilt**2*grid[2]/8
                + (tilt**2*grid[2]+tilt*energy*grid[1])/4
                + Q(".36")*fp[0] + Q(".2")*d**2*grid[0] + energy**2*grid[0]/8)
    even = (1-2*d*fp[0])/sqrt_hi(2)
    assert exp_small_upper(d**3)*2*residual/(even*(1-3*d*d)) < 400
    # L1 estimates use Cauchy-Schwarz with (1+x)^(-1), of unit L2 norm.
    assert fp[1] < 11 and f[2] < 21 and f[1]+fp[2] < 53
    assert sqrt_hi(2*fp[0]) < 2


def check_damping():
    d = Q(1, 10000)
    err = Q(".24")*d**2
    delta = 400*d**2
    assert Q("2.60")**2/30 + 2000*d**2 < Q(".24")
    # Difference of the right singular ground directions for A and A*.
    assert Q(2,3)*Q("2.60") + Q(4,3)*Q(".264")*d**2 + 2000*d**4/Q(".12") < Q("1.8")
    assert (2*Q("1.8")+d) < 4
    for end, weight, rate in ((Q(".2"),2,Q(".173")),(Q(1),4,Q(".12"))):
        loss = Q("2.60")*end**2/9 + err
        distance = sqrt_hi(2*(loss+delta)/Q("1.48"))+2*d
        assert loss < Q(".30")
        assert Q(".74")*(1-(distance+Q(1,weight))**2) > rate*end**2
        if weight == 2:
            low = Q("1.65")*(Q(1,9)-Q(56,81*24)*end**2)
        else:
            low = Q("1.65")*Q(".89")*Q(".98")*PI_LO/36
        left = Q(".08") if weight == 2 else Q(".2")
        assert (low-err/left**2)*(1-loss*d*d/2)-weight*delta/left**2 > rate
    assert Q(".89")**6*2 < 1
    assert 1-Q(".27")**2/6 > Q(".98")


def check_real_amplitude():
    d = Q(1, 9000)
    # Corrected real full-grid sample, its norm, and its spectral separation.
    assert (1-2*d-4*d*d) > Q(".999")
    assert Q("1.48")/2 - 600*d**4 > Q(".73")
    assert 201/Q(".999")/Q(".73")*sqrt_hi(2) < 400
    # Difference of the normalized sample from the true positive ground.
    # The correction costs 4 d^2; the normalized spectral residual costs 400 d^4.
    assert (4/Q(".999") + 400*d**2) < 5
    # Relative error of the terminal sum after multiplying by 2 sqrt(d).
    riemann = 22*d + d*d*(21+106*d)/4
    assert (1+2*riemann)/(1-2*d-4*d*d)+40*d < Q("1.010")
    assert (1-2*riemann)/(1+2*d+4*d*d)-40*d > Q(".9903")
    assert (1-d**3/4)*(1-Q("2.60")*d*d) > Q(".99999")
    assert (1-Q("1.30")*d*d)*Q(".99999")*Q(".9903") > Q(".99")
    assert Q("1.01")/Q(".99")*Q("1.03") < Q("1.06")
    assert Q("1.03")**3 > Q("1.08")


def check_high_saddle():
    n = 1450
    b = 201
    h = 10000
    lower = sqrt_lo(Q(".35")*(n-b))
    upper = sqrt_hi(Q(".60")*n)
    assert Q(8,27)*Q("2.60")/(1-Q(".08"))**3 + Q(8,27)*Q(".264")/(h*h*(1-Q(".08"))**3) + Q(12000,h**4)/Q(".04")**3 < 1
    assert Q(1,2)-Q(".08")/(6*Q(".35")) > Q(".46")
    assert Q("1.001")*Q("1.06")*exp_small_upper(Q(".34")*b*Q(".08")**2) < Q("1.65")
    z2 = 2*(Q("1.65")/Q(".999")-1)/Q(".08")**2
    assert z2 < 205
    main = sqrt_lo(2*PI_LO)*Q(".999")*(1-Q(205)/(2*lower**2))
    u = Q(".08")*lower
    tail = 2*Q("1.001")*decay(u*u/2)/u
    error = Q("1.001")/(6*Q(".35")*lower*Q(".46")**2)
    adjacent = Q("1.003")/(lower*Q(".46"))
    # The short complement is integrated with Gaussian decay.
    complement = 4*decay(Q(".16")*200-20) + 2*upper*decay(Q(".16")*n-20)
    assert complement < Q(".001")
    outside = 0
    for lo, hi, rate, factor in ((".08",".2",".173",2),(".2","1",".12",4)):
        l, r, c = Q(lo), Q(hi), Q(rate)*(n-42)
        outside += factor*Q("1.01")*(1+Q("1.001")*r)*upper*decay(c*l*l)/(c*l)
    for lo, hi, multiple in (("1","1.125",5),("1.125","1.5",4),("1.5","4.5",3),("4.5","45",1)):
        l, r = Q(lo), Q(hi)
        outside += 2*Q("1.01")*upper*(r-l)*(1+Q("1.001")*r)*decay(Q(".076")*(n-42)/multiple**2)
    assert 2*(1-Q(41,n)) > Q("1.94")
    assert (Q(".124")*Q("1.94")-Q(1,80))**3*45**2 > Q("2.61")**3
    assert (Q("1.94")/75-Q(1,80))**3*10**8 > Q("2.61")**3
    assert 100*upper*decay(Q(n*12,160)) < Q(".001")
    assert main - tail - error - adjacent - complement - outside - Q(".001") > Q(".20")


def check_bounded_height():
    y = Q(".0003")
    assert Q(".37")*y*y/(Q(".08")**4*(1-(y/Q(".08"))**2)) < Q(".10")*Q(".0084")
    assert y*(2+Q("2.60")/Q(".30")) < Q(".004")
    assert 2*Q(".844")*Q(".60")-Q(".60")**2/16-3*y*Q("3.20") > Q(".95")
    assert Q(".844")**2-Q(".95")/16 > 3*y
    assert Q(".95")*(1-Q(".005")**2)-3*y*Q("2.60")*Q(".005")**2 > Q(".80")
    assert 200*exp_small_upper(Q("1.65"))**4 < 1/decay(Q(13))
    # log mgf from Cauchy after removing the constant and linear terms.
    assert 13 + Q(".37")*Q(401,2) < 88
    assert Q(90)/Q(".04") < 2300
    n = Q(10**19,110**2)
    dl = sqrt_lo(Q(".0084")*(n-401))
    assert Q("1.001")*4600/(6*Q(".0084")*dl*Q(".40")**2) < Q(".23")
    assert Q(2300)/(Q(".40")*dl) < Q(".003")
    assert y*dl > 10
    for hmax, c in ((20, Q(".00000014")), (110, Q(".00004"))):
        pairs = Q(10**19,hmax**2)
        assert 2*(1+Q("1.01")*10000)*10000*sqrt_hi(116*pairs)*3**20*decay(c*pairs*y*y) < Q(".001")
    assert Q(".023")*200**2/110**4 > Q(".0000017")
    assert Q("1.084")**2/(Q(".01")**2*Q("2.001")**3) > 1450


if __name__ == "__main__":
    check_samples()
    check_damping()
    check_real_amplitude()
    check_high_saddle()
    check_bounded_height()
    print("Verified the transfer-power bounds, both saddle integrals and the 1/100 corank range.")
