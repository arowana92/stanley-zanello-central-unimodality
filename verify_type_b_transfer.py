"""Check the type B specialization, coefficient reflection, and peak overlap."""

from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations
from math import comb, gcd

from verify import ballot_ranks, direct_ranks
from verify_cubic_tilt import A_HI, A_LO, gaussian_even, gaussian_factor
from verify_folded_saddle import upper_exp
from verify_hit_tilts import exp_bound
from verify_rising import PI_LO, sqrt_hi, sqrt_lo


def endpoint_sums(n):
    """Prefix sums of the n cheapest entries for each of the three spectra."""
    sums = [[0], [0], [0]]
    degree = 0
    while any(len(row) <= n for row in sums):
        ordinary = degree+1
        odd = ordinary if degree % 2 else 0
        mixed = ordinary+(degree-1 if degree >= 3 and degree % 2 else 0)
        for row, multiplicity in zip(sums, (ordinary, odd, mixed)):
            for _ in range(min(multiplicity, n+1-len(row))):
                row.append(row[-1]+degree)
        degree += 1
    return sums


def check_reflections(counts, total):
    best = [0]
    for count in counts:
        best.append(max(best[-1], count))
    for j in range(1, total+1):
        last = min(j-1, total-j)
        assert best[last+1] <= (counts[j] if j < len(counts) else 0)


def primitive(row):
    """Remove a common integer factor from a sparse relation."""
    common = 0
    for entry in row.values():
        common = gcd(common, entry)
    if common > 1:
        return {col: value//common for col,value in row.items()}
    return row


def insert_relation(row, pivots):
    """Fraction-free row reduction. Each pivot has its smallest column first."""
    while row:
        col = min(row)
        if col not in pivots:
            pivots[col] = primitive(row)
            return
        basis = pivots[col]
        left, right = basis[col], row[col]
        divisor = gcd(left, right)
        left, right = left//divisor, right//divisor
        if left != 1:
            row = {j:left*v for j,v in row.items()}
        for j,v in basis.items():
            new = row.get(j,0)-right*v
            if new:
                row[j] = new
            else:
                row.pop(j, None)
        if left not in (-1,1):
            row = primitive(row)


def determinant_character(n):
    """Compute the type B sign quotient over Q with both bidegrees retained."""
    cap = 2*n
    cells = [(x,y) for x in range(cap) for y in range(cap) if (x+y)%2]
    shifts = [(a,b) for a in range(cap) for b in range(cap) if a+b and (a+b)%2==0]
    return alternating_character(n, cap, cells, shifts)


def alternating_character(n, cap, cells, shifts):
    """Quotient the alternating monomial basis by the given power sum shifts."""
    by_degree = defaultdict(list)
    for shape in combinations(cells,n):
        degree = sum(x for x,_ in shape), sum(y for _,y in shape)
        by_degree[degree].append(shape)
    result = Counter()
    for (x,y), target in by_degree.items():
        index = {shape:i for i,shape in enumerate(target)}
        pivots = {}
        for a,b in shifts:
            for src in by_degree.get((x-a,y-b), ()):
                row = {}
                for j,(u,v) in enumerate(src):
                    dest = u+a,v+b
                    if dest[0]>=cap or dest[1]>=cap or dest in src:
                        continue
                    right = j+1
                    while right<n and src[right]<dest:
                        right += 1
                    shape = src[:j]+src[j+1:right]+(dest,)+src[right:]
                    # Only the changed cell is new, so target rows are distinct.
                    row[index[shape]] = (-1)**(right-j-1)
                insert_relation(row,pivots)
            if len(pivots)==len(target):
                break
        multiplicity = len(target)-len(pivots)
        if multiplicity:
            result[x,y] = multiplicity
    return result


def check_characters():
    for n in range(1,5):
        character = determinant_character(n)
        marginal = Counter()
        for (x,y), count in character.items():
            marginal[x] += count
            assert count == character[y,x]
        counts = direct_ranks(range(2*n-1,0,-2))[::-1]
        assert marginal == Counter(dict(enumerate(counts)))
        assert sum(marginal.values()) == comb(2*n,n)
        lowest = endpoint_sums(n)[1][n]
        assert min(x+y for x,y in character) == lowest
        k = 0
        while (k+1)*(k+2) <= n:
            k += 1
        shift = sum(j*(2*j-1) for j in range(1,k+1))
        remaining = n-k*(k+1)
        expected = Counter(shift+sum(indices) for indices in combinations(range(2*k+2),remaining))
        assert expected == {x:v for (x,y),v in character.items() if x+y == lowest}
        print(f'Type B rank {n}: {sum(marginal.values())} dimensions, exact area specialization.')


def check_rows(max_n=96, recurrence_n=32):
    ordinary, odd, mixed = endpoint_sums(max_n)
    for n in range(max_n+1):
        assert mixed[n] == min(2*h+odd[h]+ordinary[n-h] for h in range(n+1))
    # Pack each row in digits large enough for either positive convolution.
    width = (2*recurrence_n+1)//8+1
    base = 1 << (8*width)
    dyck, even_length, odd_length = [1], [1], [1]
    for m,ranks in ballot_ranks(max_n):
        n, parity = divmod(m,2)
        counts = ranks[::-1]
        if n<=12:
            assert counts == direct_ranks(range(m-1,0,-2))[::-1]
        check_reflections(counts, (mixed if parity else odd)[n])
        if n>recurrence_n:
            continue
        packed = int.from_bytes(b''.join(v.to_bytes(width,'little') for v in counts),'little')
        if parity:
            odd_length.append(packed)
            assert packed == sum(base**h*even_length[h]*dyck[n-h] for h in range(n+1))
            source, inherited = odd_length, even_length[n]
        else:
            even_length.append(packed)
            dyck.append(sum(base**i*dyck[i]*dyck[n-i-1] for i in range(n)))
            source, inherited = even_length, odd_length[n-1]
        assert packed == (base**n*inherited
                          + sum(base**(n-i-1)*source[i]*dyck[n-i-1] for i in range(n)))
    print(f'Both comparison tests through {max_n}, recurrences through {recurrence_n}, direct parts through 12.')


def ground_integral_bounds():
    # f''=(x-a)f, f(0)=0 and f'(0)=1. Enclose the integral on [0,3].
    coeff = [(Q(0),Q(0)), (Q(1),Q(1))]
    for i in range(2,43):
        prev = coeff[i-3] if i>=3 else (Q(0),Q(0))
        prod = [v*a for v in coeff[i-2] for a in (A_LO,A_HI)]
        coeff.append(((prev[0]-max(prod))/(i*(i-1)), (prev[1]-min(prod))/(i*(i-1))))
    rem = max(max(abs(lo),abs(hi))*3**i for i,(lo,hi) in enumerate(coeff) if i>=40)
    # Successive blocks of three weighted Taylor coefficients lose at least a half.
    assert (27+9*A_HI)/(43*42) < Q(1,2)
    lower = sum(lo*Q(3**(i+1),i+1) for i,(lo,_) in enumerate(coeff))-9*rem
    integral = sum(hi*Q(3**(i+1),i+1) for i,(_,hi) in enumerate(coeff))+9*rem
    at_three = sum(hi*3**i for i,(_,hi) in enumerate(coeff))+3*rem
    assert lower > Q('1.57') and integral+at_three/sqrt_lo(3-A_HI) < Q('2.04')


def check_overlap():
    ground_integral_bounds()
    for left,right,target in [('.135','.145','.105'),('.14','.145','.18'),('.145','.25','.18')]:
        left, right = Q(left), Q(right)
        factor = gaussian_factor(6,A_LO**3/(18*right**2))-Q('.01')
        slope = (3*Q('1.57')*factor/(2*sqrt_hi(A_HI))*(A_LO/(3*left))**6
                 /upper_exp(A_HI*(A_HI/(3*left))**2/6))
        assert slope > Q(target)
    # Global maximizers and right flank at the smaller return threshold.
    m = 1500000
    shift = (1+Q(1,m))/sqrt_lo(m)
    assert Q('.6')+shift < Q('.601') and Q('.145')+shift < Q('.147')
    assert 300/(Q('.19')**3*PI_LO*m*sqrt_lo(m)) < Q('.001')
    assert Q('1.78')/upper_exp(6*Q('.601')**2) > Q('.20')
    assert Q('1.78')*(1-exp_bound(-6*(Q('.25')-Q('.147'))**2)) > Q('.10')
    n = 10**6
    # A descent at k < ceil(.135 s) gives 2k+1 below both lower bounds.
    needed = 2*Q('.135')*(2+Q(1,n))*sqrt_hi(2+Q(1,n))+Q(2,10**9)
    assert 4/(3*sqrt_hi(3))-Q(2,1000) > needed
    assert 2*sqrt_lo(2)/3*Q(7,8)*sqrt_lo(Q(7,8))-Q(2,1000) > needed
    print('Peak overlaps at 750000 and 1000000; an even descent requires h > n/8.')


def check_reflection_density():
    h = 125000
    s = 2*h*sqrt_lo(2*h)
    assert (Q(4,3)*h*sqrt_hi(h)+2*sqrt_hi(h)+3*h+1)/s < Q('.475')
    assert Q('1.31')/s < Q('.0001')
    for x, target in [(Q('.238'), Q('1.25')), (Q('.186'), Q('.18'))]:
        amin = A_LO**3/(18*x*x)
        gauss = sum(comb(3,i)*gaussian_even(2*i)/amin**i for i in range(4))
        bound = (3*Q('2.04')/(2*sqrt_lo(A_LO))*(gauss+Q('.01'))*(A_HI/(3*x))**3
                 *exp_bound(-A_LO*(A_LO/(3*x))**2/6))
        assert bound < target
    for end, upper in [(Q('.29'), Q('1.25')), (Q('.475'), Q('.18'))]:
        loss = 6*(end**2-Q('.25')**2+Q('.0001'))
        assert Q('1.78')/upper_exp(loss) > upper+2*Q('.069')
    print('At h >= 125000, unimodality of the odd row implies every required comparison.')


if __name__=='__main__':
    check_overlap()
    check_reflection_density()
    check_characters()
    check_rows()
