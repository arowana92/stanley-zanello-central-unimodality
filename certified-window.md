# Finite verification of upper-half curvature

For the odd-part and even-part central staircases, all interior ranks $j\ge D/2$ satisfy $a_j^2>a_{j-1}a_{j+1}$ for $9\le n\le1000$. Together with weak growth up to $\lceil D/2\rceil$ and direct enumeration at smaller sizes, this proves unimodality of both shapes for $1\le n\le1000$. [Lower-half inequality](monotonicity.md#1-lower-half-for-all-sizes)

Write $m=2n$ or $2n+1$, $D=\lfloor m^2/4\rfloor$ and $b_k=a_{D-k}$. The [first-passage estimate](rising-window.md) proves strict log-concavity at $2m^{3/2}\le k\le D/2$ for both parities. Its small-size input is the earlier [exact check through 384 rows](README.md#exact-coefficient-checks). For the rest of the upper half we certify the sign at each integer
$$1\le k\le\min\{\lfloor D/2\rfloor,\lfloor 2m^{3/2}\rfloor\}.$$
The upper endpoint is computed by taking an integer square root of $4m^3$, with the resulting integer and its successor checked by squaring. There are **143,235,952** such comparisons over both families at $9\le n\le1000$.

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
/tmp/sz_verify_window 1000
~~~

The final line of the C++ run is

~~~text
Certified 143235952 strict determinants in both families for 9 <= n <= 1000. Direct counts agree through n = 12.
~~~

The sign test stops at $n=1000$ in this run. The [large-size argument](finite-reduction.md) begins at $10^{46}$, leaving $1001\le n<10^{46}$ unresolved.
