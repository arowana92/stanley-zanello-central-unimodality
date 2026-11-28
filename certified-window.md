# Finite verification of upper-half curvature

For the odd-part and even-part central staircases, all interior ranks $j\ge D/2$ satisfy $a_j^2>a_{j-1}a_{j+1}$ for $9\le n\le2048$. Together with weak growth up to $\lceil D/2\rceil$ and direct enumeration at smaller sizes, this proves unimodality of both shapes for $1\le n\le2048$. For every $n\ge9$ the same strict inequality also holds at upper-half coranks through 4096. [Lower-half inequality](monotonicity.md#1-lower-half-for-all-sizes) · [All-size corank certificate](#a-fixed-corank-range-at-every-size)

Write $m=2n$ or $2n+1$, $D=\lfloor m^2/4\rfloor$ and $b_k=a_{D-k}$. The [first-passage estimate](rising-window.md) proves strict log-concavity at $2m^{3/2}\le k\le D/2$ for both parities. Its small-size input is the earlier [exact check through 384 rows](README.md#exact-coefficient-checks). For the rest of the upper half we certify the sign at each integer
$$1\le k\le\min\{\lfloor D/2\rfloor,\lfloor 2m^{3/2}\rfloor\}.$$
The upper endpoint is computed by taking an integer square root of $4m^3$, with the resulting integer and its successor checked by squaring. The single-scale computation makes **150,138,442** such comparisons over both families at $9\le n\le1019$. The extension below uses a separate certificate for the first 4096 coranks.

## Fixed-point enclosures for adjacent ranks

For a partition with exactly $d$ parts, set $i=d(m-d)-j$, where $j$ is its rank. The largest $d$ allowed parts have sum $d(m-d)$. At a positive admissible length $d$, the two predecessor counts at time $m-1$ have indices $i$ and $i-(m-2d)$, respectively. Negative indices contribute zero. This gives an exact recurrence using only smaller or equal deficit indices. [Endpoint recurrence in Lean](CentralUnimodality/EndpointDeficit.lean)

Start the empty path with an integer weight $U$. At each step average the two stored predecessors and round down. A missing predecessor has weight zero. If the stored entry is $A$ and the true endpoint count is $v$, Lean proves
$$
2A\,2^m\le 2U v\le(2A+m)\,2^m .
$$
The average of two integers loses at most half a unit at each step. Summing over the $\lfloor m/2\rfloor+1$ endpoints gives an error allowance of $m(\lfloor m/2\rfloor+1)$ in doubled units. A difference between two stored rank sums larger than this allowance in doubled units proves a strict comparison of the true ranks. [Formal error and comparison theorems](CentralUnimodality/RoundedDeficit.lean)

At $U=2^{128}$, the integer implementation separates every adjacent pair on the finite induction interval from $\lfloor m^{3/2}/10\rfloor$ through $\lfloor D/2\rfloor$ in both shapes at $n=192$. The respective corank peaks are 2615 for $m=384$ and 2627 for $m=385$. This calculation checks 35,453 comparisons in Python. A separate, unrounded recurrence gives exact counts inside all 36,962 upper-half enclosures. Lean independently verifies the packed evaluation and its comparison with the true integer ranks, using the smaller unit $U=2^{100}$ for these two shapes. [Packed calculation in Lean](CentralUnimodality/RoundedBase.lean) The program also compares its enclosures with direct partition enumeration for both shapes through 12 rows at three precisions. [Reproducible integer check](verify_rounded_deficits.py)

~~~sh
lake build CentralUnimodality.RoundedBase
python3 -B verify_rounded_deficits.py --rows 192 --precision 128 --exact
~~~

## Truncated ballot recurrence

The [ballot bijection](README.md#exact-coefficient-checks) gives the missing-cell count of a word as $K=\sum_{v=1}^t\lfloor H_v/2\rfloor$, where $H_v$ is its height after step $v$. For endpoint $h$ the minimum area is $A(h)=\lfloor h^2/4\rfloor$. The path must visit each of the heights $1,\ldots,h$ and an alternating prefix followed by a straight climb attains their total contribution. With $d=(t-h)/2$ down steps, the greatest area is $D_t-d(d+1)/2$, $D_t=\lfloor t^2/4\rfloor$. Indeed the $d$ selected labels have sum at least $1+\cdots+d$, attained by putting all down steps last.

Let $v_{t,h}(i)$ count the paths with excess area $K-A(h)=i$. The last step adds $\lfloor h/2\rfloor$ to $K$. Substituting $A(h)$ gives
$$ v_{t,h}(i)=v_{t-1,h-1}(i)+v_{t-1,h+1}(i-h), $$
with zero at negative indices, negative heights or unreachable endpoints. The initial entry is $v_{0,0}(0)=1$. Summing over $h$ at $i=k-A(h)$ recovers $b_k$. For any cap on actual area, discarded paths can never return below the cap because every step has nonnegative cost. The cap includes the neighbor $k+1$ of every comparison and the complete support at every length at most 25. At fixed height the upper area bound increases between times $t-2$ and $t$, so entries beyond the updated range have always been zero. Alternating the parity of the destination height therefore permits in-place updates.

## Certifying the sign after rounding

The [checker](verify_window.cpp) uses positive additions in IEEE binary64 with round-to-nearest, and scales every count by the same exact power of two, $2^{-N}$, with $N$ the largest row count requested. Zero stays exact. Let $m\le2N+1$ and $u=2^{-53}$. Each positive computed row entry $\widehat b_k$ satisfies
$$ (1-u)^p\,2^{-N} b_k \ \le\ \widehat b_k\ \le\ (1+u)^p\,2^{-N} b_k,\qquad p=2m+1. $$
To see this, trace any contribution through at most $m$ additions in the walk recurrence and at most $m+1$ in the endpoint sum. Positive addition preserves any common relative error interval before the next rounding. Copies and index shifts are exact. There is no cancellation. For $N\le1019$ every positive term is at least $2^{-N}$ throughout the computation by monotonicity of rounded positive addition. The exact scaled total at any stage is at most $2^{m-N}\le2^{N+1}$. Even multiplied by $(1+u)^p$ it lies below $2^{N+2}$, within the normal exponent range. These bounds justify the per-operation relative error by induction.

Set $F=(1+u)/(1-u)$. For $R_{k-1}=\mathrm{fl}(\widehat b_k/\widehat b_{k-1})$ and $R_k=\mathrm{fl}(\widehat b_{k+1}/\widehat b_k)$, the quotient $R_{k-1}/R_k$ is at most $F^{2p+1}$ times the exact $b_k^2/(b_{k-1}b_{k+1})$. The divisions take place well inside the normal range. Indeed an ideal of the cell poset can add a cell below full size and remove one above size zero. Counting edges between two neighboring ranks puts every true adjacent ratio between $1/D$ and $D$. The computed coefficient ratios differ from these by at most a factor $F^p$ before rounding.

Here $2p+1\le8159$ and $\log F\le3u$, giving $F^{2p+1}<1+2^{-37}$. The program requires both ratios to be normal and tests
$$ R_{k-1}>\mathrm{fl}\big(R_k(1+2^{-36})\big). $$
The multiplier is exactly representable and $(1+2^{-36})(1-u)>1+2^{-37}$. Acceptance therefore implies a strictly positive **integer** determinant. If the separation is too small, the verifier stops and reports the word length and corank.

## Reproduction

Compile with binary64 arithmetic and round-to-nearest. The C++17 program checks the active rounding mode and refuses fast-math builds. On small shapes it enumerates the decreasing lists of parts recursively, compares every rank with the reversed ballot area counts and checks unimodality directly. These comparisons are exact because at $m\le25$ each scaled count has at most 26 significant bits. The independent Python check compares the complete ranks also with the Catalan recurrences.

~~~sh
python3 -B verify.py --max-n 12 --direct-n 12 --upper-curvature
python3 -B verify_rising.py
clang++ -std=c++17 -O3 -fno-fast-math -ffp-contract=off verify_window.cpp -o /tmp/sz_verify_window
/tmp/sz_verify_window 1019
~~~

The final line of the C++ run is

~~~text
Certified 150138442 strict determinants in both families for 9 <= n <= 1019. Direct counts agree through n = 12.
~~~

The fixed unit $2^{-N}$ in this first calculation limits the admissible size. The next two certificates use integer exponents and a scale that varies with word length, respectively.

## A fixed corank range at every size

Write $b_k=a_{D-k}$ and $L_k=b_k^2-b_{k-1}b_{k+1}$. For both staircases and **every $n\ge9$**,
$$
 L_k>0\quad(1\le k\le\min(4096,\lfloor D/2\rfloor)),\qquad
 L_k>b_k^2/(40k)\quad(1\le k\le\min(4096,2n)).
$$
For $k\le n/3$ this follows from the [paired-step estimate](paired-steps.md). Every remaining case with $k\le4096$ has $n<3\cdot4096$. The command below checks each integer $9\le n\le12288$ and $\lfloor n/3\rfloor<k\le\min(4096,\lfloor D/2\rfloor)$ in both families. It certifies 49,847,352 strictly positive determinants, including 41,951,106 with the stated relative margin.

~~~sh
/tmp/sz_verify_window --tail 4096
~~~

This run uses the same truncated ballot recurrence and represents each nonzero count by $M2^{e-47}$ with $2^{47}\le M<2^{48}$. To add, align the smaller mantissa by shifting right, dropping its low bits, then add and normalize. This rounds down to 48 significant bits. A dropped fractional part less than one before normalization cannot carry across the next integer after a further right shift. Each addition therefore retains a fraction between $1-v$ and one of its exact input sum, with $v=2^{-47}$. Zero stays exact. The exponents are signed integers and every exact count is at most $2^m$. Through the requested range $m\le24577$. At most $p=2m+1$ additions contribute to a row count along any path, giving
$$ (1-v)^p b_k\le\widehat b_k\le b_k,\qquad (1-v)^{-2p}<1+2^{-27}.$$
The second inequality follows from $-2p\log(1-v)\le2pv/(1-v)$. Thus it is sufficient to prove
$$ (s-l)\widehat b_k^2 > s(1+2^{-27})\widehat b_{k-1}\widehat b_{k+1} $$
with $(s,l)=(40k,1)$ for the relative margin or $(1,0)$ for strictness. The checker performs this comparison with integer mantissa products. It rounds the reserve on the right up, adding one even when the division by $2^{27}$ is exact. A difference of at least four between the left and right binary exponents already decides the comparison, since the ratio of the three mantissas in the determinant lies between $1/4$ and $4$ and $(s-l)/s\ge39/40$. For smaller differences the shifted products fit in an unsigned 128-bit integer ($s\le163840$). Direct enumeration checks all small counts through $n=12$. With corank limit 128, ordinary arbitrary-precision integer determinants also reproduce all 46,534 strict tests and 41,090 relative margins.

## Scaling by the length in the larger window

Above corank 4096, carry binary64 counts and multiply the active entries by $2^{-256}$ after every block of 256 steps. With $s_t=2^{t\bmod256}$, the ideal stored value divided by $s_t$ is the probability for the corresponding length-$t$ walk event under independent fair steps. All unscaled intermediate additions fit below $2^{257}$ by the bound below. The certificate includes a lower bound on the probabilities used in each comparison so that underflow in smaller intermediate entries is covered.

Let $u=2^{-53}$ and $\tau=2^{-1022}$. A rounded positive operation with exact result $x$ lies in $[(1-u)x-\tau,(1+u)x+\tau]$, including subnormal results. In probability units each step averages two predecessor entries, counting a missing predecessor as zero. There is at most one addition and one power-of-two rescaling. Their two relative factors are bounded by $(1\pm u)^2$, and the combined additive error in probability units is at most $3\tau$, as $s_t\ge1$. Induction bounds each endpoint error by relative factors $(1\pm u)^{2t}$ and additive error $3t(1+u)^{2t}\tau$. The true endpoint probability is at most one. This also verifies the intermediate upper bound inductively, including the addition just before rescaling.

Summing at most $t+1$ endpoint probabilities gives the following inequalities for the normalized computed coefficient $\widehat P$ and the true $P=2^{-t}b_k$, where $p=3t+1$ and $E=5(t+1)^2\tau$:
$$
 (1-u)^p P-E\le\widehat P\le(1+u)^pP+E .
$$
Here $t\le4097$. At every rank used in a determinant the checker requires the stored sum to be finite and at least $2^{-920}s_t$. Thus $E/\widehat P<2^{-75}$. Solving the two inequalities gives $|P/\widehat P-1|<v=2^{-38}$, using $p\le12292$. The sum and rank comparisons use the common stored scale without dividing by $s_t$.

At adjacent ranks the ratio of true counts lies between $1/D$ and $D$ by the order-ideal edge count. The two binary64 quotient calculations therefore lie within the normal range. A nonpositive exact determinant could make the ratio of the two computed quotients at most
$$
 \left(\frac{1+v}{1-v}\right)^2\frac{1+u}{1-u}
 <(1+2^{-35})(1-u).
$$
The checker requires the left quotient to exceed the rounded product of the right quotient and $1+2^{-35}$. This proves strictness whenever the comparison passes. The low-corank theorem above supplies the consecutive indices through 4096. The [first-passage estimate](rising-window.md) supplies strictness once $k\ge2m^{3/2}$ in the upper half.

~~~sh
/tmp/sz_verify_window --scaled 2048
~~~

The run certified **843,349,446** determinants. Its range is exactly $9\le n\le2048$ and $4097\le k\le\min(\lfloor D/2\rfloor,\lfloor2m^{3/2}\rfloor)$ for both shapes. The two commands with `--tail` and `--scaled`, together with the stated analytic estimates, reproduce the extended result. The [tilted pair-deletion argument](tilted-thinning.md) proves unimodality for every $n\ge10^{13}$, giving an earlier sufficient large-size bound. The [full proof](proof.md) uses the finite base case below.

## A shorter base case for induction

There is a second way to establish unimodality through 2048 which uses the [moment comparisons](moment-comparisons.md#induction-on-the-staircase-size) in place of the fixed-corank certificate. In the order odd-part then even-part at each $n$, assume that the odd-part rows used on the right of the recurrence are unimodal. The induction bound $2k+1\le M n^{3/2}-n-1$ yields weak increase through $k=\lfloor m^{3/2}/10\rfloor$ for $n\ge64$. Divide by $n^{3/2}$ and substitute $n=64$ as in the moment verifier.

Start with complete integer rank sequences through 63 rows. For $64\le n\le2048$ use the same positive ballot recurrence and binary64 rounding proof as in the scaled window above. The option below tests $L_k=b_k^2-b_{k-1}b_{k+1}>0$ starting at $k=\lfloor m^{3/2}/10\rfloor$. For $m<770$ it continues through $\lfloor D/2\rfloor$. For $m\ge770$ it continues through the smaller of $\lfloor D/2\rfloor$ and $\lfloor3\lfloor2m^{3/2}\rfloor/4\rfloor+2$, which covers the join at $3m^{3/2}/2$. Strict log-concavity gives a unimodal central sequence. The [first-passage first-difference estimate](rising-window.md) gives weak decrease in corank after the second endpoint up to the midpoint. Its analytic proof applies for $m\ge770$. Beyond the midpoint the [parabolic interval theorem](monotonicity.md#1-lower-half-for-all-sizes) gives weak decrease, including the central step for odd degree. This completes each induction step. The direct finite run certified **610,906,915 strict central determinants**. The positive addition and ratio error bounds above apply unchanged to these input lengths and to every tested coefficient.

~~~sh
python3 -B verify.py --max-n 64 --direct-n 12 --upper-curvature
python3 -B verify_moment_comparisons.py
clang++ -std=c++17 -O3 -fno-fast-math -ffp-contract=off verify_window.cpp -o /tmp/sz_verify_window
/tmp/sz_verify_window --central 2048
~~~
