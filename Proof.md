# A scalar Fisher midpoint test for Gaussian and gamma factors

## Statement and normalization

Let $\mu$ be the law of a finite-dimensional sufficient statistic at one reference member of a regular minimal exponential family. An increment $v$ of the natural parameter tilts it by $\exp\langle v,y\rangle$. Work on one connected open Fisher-flat patch. Write $F$ for natural parameters and $G$ for expectation parameters as functions of a Euclidean Fisher coordinate $x$. Their differentials are invertible and satisfy

$$
\langle DG_x a,DF_x b\rangle=\langle a,b\rangle .
$$

This is the pullback of the Fisher metric since the derivative of the expectation in natural coordinates is the Hessian of the log-partition. In the formal statement $G(x)$ is the gradient of the actual log-Laplace transform of $\mu$ at $F(x)-F(p)$, where $p$ is the reference point. The hypotheses give the Fisher isometry chart and the regularity identities of a natural exponential family.

For endpoints $P,Q$ let $a,b$ be their arithmetic averages in $F,G$ coordinates, respectively, mapped back to the Fisher chart. The original Fisher midpoint is $(P+Q)/2$ and the updated midpoint is $(a+b)/2$. Exact agreement or equidistance of the updated midpoint from $P,Q$ suffices. On a chord $P=p-th/2$, $Q=p+th/2$ the weaker hypothesis is

$$
\left\langle h,\frac{a+b}{2}-p\right\rangle=o(t^4)
$$

for every center and direction in the patch. The conclusion identifies a fixed invertible affine statistic $Z$ and a fixed invertible linear parametrization $u$ of *all* original natural increments. There are real numbers $\lambda_i$. The exact domain is $1+\lambda_i u_i>0$ for all $i$. Under the tilt its transformed law is the product of the following ordinary probability measures.

| Axis | Law of $Z_i$ |
| --- | --- |
| $\lambda_i=0$ | $N(u_i,1)$ |
| $\lambda_i\ne0$ | $\operatorname{Gamma}(\lambda_i^{-2},\,\mathrm{rate}=1+\lambda_i u_i)$ |

Writing the gamma natural parameter as the negative rate gives $\mathbb R^a\times(-\infty,0)^b$. Either block may be empty. A restriction of the original parameter set inherits the corresponding restriction of this maximal family. Independence concerns the statistic under each member.

## Recovering a constant cubic

The flat Fisher connection is ordinary differentiation $D$. Differentiating the metric identity, using symmetry of the two chart Hessians, gives a fully symmetric lowered product $C(u,v,w)=\langle K(u,v),w\rangle$. The dual affine connections have coefficients $K$ and $-K$. Differentiating the two chart equations $D^2F=DF\,K$ and $D^2G=-DG\,K$ and exchanging derivatives proves $[K_u,K_v]=0$ and the full symmetry of $S=DC$. [Charts](FisherMidpoint/Charts.lean) · [Curvature equations](FisherMidpoint/Flat.lean)

The natural and expectation coordinates are affine along their respective short geodesics. Thus the averages defined above really are their midpoints. Comparing these two geodesics with their fourth-order expansions gives the longitudinal coefficient $S(h,h,h,K(h,h))/128$ for the half-sum displacement. The formal proof bounds the projected remainder on arbitrarily short actual curves. Equidistance annihilates the same scalar because the difference of the two squared distances is $2t$ times the longitudinal displacement. [Actual averages](FisherMidpoint/Midpoints.lean) · [Remainder argument](FisherMidpoint/Obstruction.lean) · [Equidistance](FisherMidpoint/Equidistance.lean)

At a point, the commuting self-adjoint maps $K_u$ have common orthonormal axes $e_i$ with $K(u,e_i)=\lambda_i u_i e_i$. For each $\lambda_i\ne0$, expand the zero scalar on $h=x+t e_i$. The coefficients of degrees five through two successively annihilate the entries of $S$ involving that axis. Polarization gives $S(a,b,c,e_i)=0$ for all $a,b,c$. [Common axes](FisherMidpoint/Axes.lean) · [Coefficient and polarization proof](FisherMidpoint/Quartic.lean)

This argument allows eigenvalues to vanish. The derivative of every $\|K_x(a,b)\|^2$ is zero since the derivative output is orthogonal to every product output. Thus the annihilator of multiplication at one point persists on the entire patch. If $w=(D_zK)(u,v)$, then $K_x(w,b)=0$ at every $x$ on the patch. Differentiate this identity and use the symmetry of $S$ to obtain $\|w\|^2=0$. Consequently $K$ is constant and one orthonormal basis works throughout. [Parallelism](FisherMidpoint/Parallel.lean) · [Midpoint rigidity](FisherMidpoint/Rigidity.lean)

## From the potential to an equality of laws

On axis $i$ with Fisher displacement $x$, the natural displacement is proportional to $s_\lambda(x)=(e^{\lambda x}-1)/\lambda$, with $s_0(x)=x$. The expectation chart has the opposite coefficient. Both formulas follow by an integrating factor on the connected patch. In these centered natural coordinates the joint log-Laplace transform of the score has one term per axis,

$$
f_0(u)=u^2/2,\qquad
f_\lambda(u)=u/\lambda-\log(1+\lambda u)/\lambda^2 .
$$

For a reference orthonormal basis $e_i$ the centered score is $Y_i=\langle DF_p e_i,T-G(p)\rangle$. On a nonzero axis the final affine statistic is $Z_i=(1/\lambda_i-Y_i)/\lambda_i$. On a zero axis $Z_i=Y_i$. The natural increment paired with score parameter $u$ is $DF_p(\sum_i u_i e_i)$. Both coordinate changes are bijective. [Chart integration](FisherMidpoint/Integration.lean) · [Potential](FisherMidpoint/Potential.lean) · [Affine changes](FisherMidpoint/Canonical.lean)

The local transform identifies the actual reference measure. For each linear projection, continue its marginal transform from a real interval about zero to the common vertical strip of analyticity. Evaluate on the imaginary axis and use uniqueness of the joint characteristic function. The product measure has exactly the required local transform. The gamma density calculation gives divergence at and beyond the rate, so equality of the reference laws identifies the full natural domain. Exponential tilting and pushforward then give the displayed Gaussian and gamma product for every admissible original parameter. [Local transform uniqueness](FisherMidpoint/Laplace.lean) · [Gamma boundary](FisherMidpoint/Gamma.lean) · [Classification](FisherMidpoint/Family.lean)

Conversely, each canonical axis has global Fisher arclength $x$, natural coordinate $s_\lambda(x)$ and expectation coordinate $s_{-\lambda}(x)$ in centered units. Their derivatives multiply to one. Gaussian means average arithmetically. For positive gamma rates $r,s$, the natural and expectation midpoint rates are $(r+s)/2$ and $2rs/(r+s)$. Their product is $rs$, so the updated Fisher midpoint has rate $\sqrt{rs}$. The formal converse constructs both global averages and proves uniqueness. [Product transforms](FisherMidpoint/Factors.lean) · [All tilts](FisherMidpoint/Tilts.lean) · [Global midpoint formulas](FisherMidpoint/Converse.lean)

## Sources and scope

Nielsen and Okamura derive the vector fourth-order obstruction, classify the scalar case and explain simultaneous splitting once the cubic is constant. The existing Euclidean midpoint formalization supplies the short-geodesic boundary-value theorem and the fourth-order remainder estimates used here. The scalar sufficiency implication uses the curvature identities specific to Hessian structures. [Nielsen and Okamura, Remark 8.7 and Theorem 9.2](https://arxiv.org/html/2609.07551v2#S8) · [Pinned formal dependency](https://github.com/JD-Jones-ASES/EuclideanMidpointRigidity/tree/4929a3c843e8b8c2905581575d9d5644694e0c79)

Xu and Lei give the local quadratic and negative-logarithmic normal form assuming a flat metric and parallel Fubini–Pick form. Hildebrand relates the parallel cubic equation to metrised Jordan algebras. The present result derives parallelism from the scalar observation and identifies the maximal tilted law. Priority of this characterization remains open. [Xu and Lei, Theorem 1.3](https://arxiv.org/abs/2007.02614) · [Hildebrand, §3](https://arxiv.org/abs/1303.7366)

The separate symbolic replay includes a bivariate example in which two observed sums share an exponential source. Its directional fourth-order coefficient is $1/1024$, obtained independently from the parameter averages and the cumulant geometry. The examples serve as exact computational checks. The general implication and its product-law conclusion are proved in Lean. [Exact replay](scripts/exact_replay.py)
