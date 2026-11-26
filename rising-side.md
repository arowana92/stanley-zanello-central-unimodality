# Growth up to the peak scale

Use $m,D,k=D-j$ as in the [tail estimates](monotonicity.md). We strengthen the rising-side estimate there by removing the logarithmic loss. For sequences of ranks in either family we prove the following implication.
$$j\ge D/2,\quad k/m^{3/2}\longrightarrow\infty
\quad\Longrightarrow\quad a_{j+1}>a_j\text{ eventually}.$$

Choose the independent Bernoulli tilt from §2 of the tail estimates so that the unrestricted mean of $S=\sum rX_r$ equals $j$. Write $E_t$ for ballot survival up to time $t$, $q_t=\Pr(E_t)$ under this tilt, and $\sigma^2=\sum r^2p_r(1-p_r)$. The same derivative bound gives $\alpha\sqrt m\to\infty$, $0<\alpha\le A$ and $\sigma\asymp m^{3/2}$. All step probabilities lie in a fixed compact subinterval of $(0,1)$. The up-step drift at label $r$ is $\tanh(\alpha r/(2m))$, at least $c_A\alpha$ during the first half.

**Survival estimates.** For a homogeneous walk with up probability $p\ge1/2$ and drift $d=2p-1$, the survival probability through $t$ is $O(d+t^{-1/2})$ and is at least $d$. For the upper bound condition on final height $x\ge0$. The fraction of nonnegative paths ending there is $(x+1)/((t+x)/2+1)$ by reflection, so the probability is at most $2\,\mathbb E[(H_t+1)_+]/t=O(d+t^{-1/2})$. The lower bound follows from the probability $1-(1-p)/p$ of surviving forever when $p>1/2$.

Set $L=\lceil\sqrt m/\alpha\rceil$ and $h=\lfloor m/2\rfloor$. Then $L=o(m)$ and $\alpha^2L\to\infty$. By comparison with homogeneous walks, $q_L\gg\alpha$ and $q_h\ll\alpha+h^{-1/2}\ll\alpha$.

In fact $q_m/q_L\to1$. Given $E_L$, the probability that $H_L<c_A\alpha L/2$ is $o(1)$ by Hoeffding and positive association of the increasing events $E_L$ and $\{H_L\ge c_A\alpha L/2\}$. Positive association here follows by conditioning on one coordinate at a time, since two increasing functions of a single variable have nonnegative covariance. From height at least $c_A\alpha L/2$ a walk of drift $c_A\alpha$ has probability at most $\exp(-c\alpha^2 L)$ of ever falling below zero by the ruin formula. Coupling applies until $h$. Also, conditional on $E_L$, we have $H_h\ge c_A\alpha h/2$ with probability $1-o(1)$ by the same positive association and Hoeffding estimate. Over the last $m-h$ steps all drifts are nonnegative. From this height the crossing probability is $O(m/(\alpha h)^2)=o(1)$ by comparison with a fair walk and the maximal variance inequality. These estimates bound the conditional probability of any later failure. In particular $q_h/q_m=O(1)$.

**The weighted prefix given survival.** Write $U=\sum_{r>m-L}rX_r$. Under $E_L$, $(U-\mathbb EU)/(m\sqrt L)$ is bounded in probability. To see this, multiply the independent product law by $e^{tU}$ and normalize, with $t=\pm1/(m\sqrt L)$. The changed log down/up odds for any prefix step differ by at most $1/\sqrt L$. All changed up-step drifts are bounded above by $O(\alpha+L^{-1/2})$, so the homogeneous survival upper bound gives $\Pr_t(E_L)=O(\alpha+L^{-1/2})=O(\alpha)$. The centered unrestricted moment $\mathbb E\exp(t(U-\mathbb E U))$ is bounded by an absolute constant by Hoeffding's exponential bound for independent bounded summands. Multiplying it by $\Pr_t(E_L)/q_L$ gives the conditional exponential moment, bounded for both signs. This proves the assertion.

The suffix is independent of this conditioning. Its centered weight divided by $\sigma$ tends in distribution to a standard normal by the Lindeberg theorem. The deleted variance is $O(m^2L)=o(\sigma^2)$ and each centered summand is bounded by $m=o(\sigma)$. The conditional prefix displacement is $O_{\Pr}(m\sqrt L)=o_{\Pr}(\sigma)$. Hence $(S-j)/\sigma$ given $E_L$ converges to that normal law. The same convergence holds under $E_m$, since $E_m\subset E_L$ and $q_m/q_L\to1$.

**Adjacent probabilities.** The [paired-label kernel estimate](peak-window.md#a-bound-on-the-characteristic-function) applies to this tilted product law. Its proof uses independence, uniformly bounded odds and the ratio $q_h/q_m=O(1)$ proved above. The conditional characteristic function of $S$ is therefore bounded in modulus by $C\exp(-c m|\theta|^{2/3})$ on $[-\pi,\pi]$. After the change $t=\sigma\theta$ this bound and its product with $|t|$ are integrable uniformly in $m$. Inverting with the preceding centered normal limit gives
$$\sigma\Pr(S=j\mid E_m)\longrightarrow(2\pi)^{-1/2}.$$
Inserting the factor $|1-e^{-i\theta}|\le|\theta|$ bounds the absolute adjacent probability difference by $O(\sigma^{-2})$. Finally
$$\frac{a_{j+1}}{a_j}
 = e^{\alpha/m}\frac{\Pr(S=j+1\mid E_m)}{\Pr(S=j\mid E_m)}
 = e^{\alpha/m}(1+O(\sigma^{-1})).$$
Here $\alpha/m\gg\sigma^{-1}$ in the limiting sense that their ratio tends to infinity. This proves the stated strict inequality.

## Reduction to intermediate small area

For every fixed $\epsilon>0$, all sufficiently large $m$ have increasing ranks on $D/2\le j\le D-(x_*+\epsilon)m^{3/2}$, where $x_*$ is the scaled mode in the peak-window theorem. Indeed, a sequence violating growth there either has an unbounded subsequence of scaled coranks tending to infinity, covered above, or a subsequence converging to a finite point strictly above $x_*$. In the latter case the first-difference limit and $(\log f)''\le-12$ give $f'<0$, i.e. growth in the rank direction. The lower half follows from Björner–Ekedahl. A compact window containing the global peak has strict log-concavity.

Consequently, if arbitrarily large counterexamples exist, one can choose a wrong-way step on the high-rank side (a strict decrease in corank order before the global peak in that order) along a subsequence with
$$k/n\longrightarrow\infty,\qquad k/m^{3/2}\longrightarrow0.$$
For precision, the fixed-linear tail theorem excludes bounded $k/n$, and the compact-window difference and log-concavity estimates exclude scaled coranks bounded away from zero up to and through the peak. On its far side the growth result above excludes a reversal. The same argument applies to both parities. The [block transfer argument](small-area.md) proves eventual growth in this last regime. The [effective argument](finite-reduction.md) gives a uniform finite-size cutoff.
