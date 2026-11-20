"""Replay finite algebra and exact controls for the Fisher midpoint theorem."""

from itertools import combinations_with_replacement

import sympy as sp


def require(condition: bool, description: str) -> None:
    if not condition:
        raise AssertionError(description)


def check_midpoint_coefficient() -> None:
    # Fisher arclength x, with natural and expectation coordinate derivatives
    # a(x) and 1/a(x). Invert the two actual coordinate averages to order four.
    x, t, b, c, d = sp.symbols("x t b c d")
    a = 1 + b*x + c*x**2 + d*x**3
    inverse_a = sp.series(1/a, x, 0, 4).removeO()
    midpoints = []
    for derivative in (a, inverse_a):
        chart = sp.integrate(derivative, x)
        target = (chart.subs(x, t/2) + chart.subs(x, -t/2)) / 2
        # chart(0) = 0 and chart'(0) = 1. Its inverse starts y - chart''(0)y²/2.
        midpoint = target - derivative.diff(x).subs(x, 0)*target**2/2
        midpoints.append(sp.series(midpoint, t, 0, 5).removeO())
    defect = sp.expand(sum(midpoints)/2)
    require(sp.expand(defect - b*(2*c-b**2)*t**4/128) == 0, "scalar fourth jet")

    s = sp.symbols("s", positive=True)
    poisson = (sp.sqrt(s**2-t**2/4) + sp.sqrt(s**2+t**2/4))/2 - s
    require(sp.series(poisson, t, 0, 6).removeO() == -t**4/(128*s**3),
            "Poisson fails at exactly order four")


def check_tensor_contraction() -> None:
    x, y, z = h = sp.symbols("x y z")
    cubic = 2*x**3 + 3*x*y*z - y**2*z + z**3
    quartic = (x-2*y+3*z)**4 + x**2*y*z - 4*y**3*z
    k = sp.Matrix([cubic.diff(v)/3 for v in h])      # K(h,h)
    u = sp.Matrix([quartic.diff(v)/4 for v in h])    # (D_h K)(h,h)
    first = sp.hessian(cubic, h)*u/6                  # K(h,u)
    other = sp.hessian(quartic, h)*k/12               # (D_k K)(h,h) = (D_h K)(h,k)
    projected = sp.Matrix(h).dot(2*first + 5*other - 4*other)
    require(sp.expand(projected - 3*k.dot(u)) == 0, "longitudinal contraction")
    require(sp.expand(projected) != 0, "nonzero contraction control")


def check_quartic_kernels() -> None:
    # The matrix sends every degree-four monomial to its quintic derivative
    # along the diagonal quadratic vector field. Compute its exact rank.
    for dimension in range(1, 6):
        axes = range(dimension)
        quartics = list(combinations_with_replacement(axes, 4))
        rows = {m: i for i, m in enumerate(combinations_with_replacement(axes, 5))}
        for active in range(dimension+1):
            eigenvalues = (2, -2, 2, 1, -3)[:active]
            matrix = sp.zeros(len(rows), len(quartics))
            for col, monomial in enumerate(quartics):
                for axis, value in enumerate(eigenvalues):
                    row = rows[tuple(sorted((*monomial, axis)))]
                    matrix[row, col] = value*monomial.count(axis)
            null_columns = [i for i, m in enumerate(quartics) if min(m) >= active]
            require(all(matrix[:, i].is_zero_matrix for i in null_columns),
                    "inactive quartics lie in the kernel")
            require(matrix.to_DM().rank() == len(quartics)-len(null_columns),
                    f"quartic kernel in dimension {dimension} with {active} active axes")


def check_cumulants_and_shapes() -> None:
    # Work in oblique natural coordinates. The bias moves the gamma boundaries.
    theta = sp.Matrix(sp.symbols("p q r"))
    affine = sp.Matrix([[1, 1, 0], [0, 1, -1], [1, 1, 1]])
    base = dict(zip(theta, [1, 0, -1], strict=True))
    u, v, w = affine*theta + sp.Matrix([2, -4, -3])
    h = sp.Matrix(sp.symbols("h:3"))
    t, eig = sp.symbols("t eig")
    for shape1, shape2 in [(sp.Rational(3, 2), 4), (2, 2)]:
        potential = u**2/2 - shape1*sp.log(-v) - shape2*sp.log(-w)
        g = sp.hessian(potential, theta).subs(base)
        require(g.is_positive_definite is True and not g.is_diagonal(),
                "positive nondiagonal covariance")
        inverse_g = g.inv()
        thirds = [sp.hessian(potential.diff(i), theta).subs(base) for i in theta]
        third_hh = sp.Matrix([h.dot(matrix*h) for matrix in thirds])
        tilted = {v: base[v]+t*direction for v, direction in zip(theta, h, strict=True)}
        fourth = potential.subs(tilted, simultaneous=True).diff(t, 4).subs(t, 0)
        require(sp.expand(fourth - sp.Rational(3, 2)*third_hh.dot(inverse_g*third_hh)) == 0,
                "cumulant equation in oblique coordinates")
        operators = [-inverse_g*matrix/2 for matrix in thirds]
        gram = sp.Matrix([[sp.trace(a*b) for b in operators] for a in operators])
        spectrum = (inverse_g*gram).charpoly(eig).as_expr()
        expected = eig*(eig-sp.S.One/shape1)*(eig-sp.S.One/shape2)
        require(sp.expand(spectrum - expected) == 0, "shape spectrum and Gaussian nullity")

    # A three-point law matches four Gaussian cumulants at a single tilt.
    moment_gen = (2 + sp.cosh(sp.sqrt(3)*t))/3
    series = sp.series(sp.log(moment_gen), t, 0, 7).removeO()
    require(series == t**2/2 - t**6/120, "single-tilt moment control")


def check_rate_and_matrix_midpoints() -> None:
    p, q = sp.symbols("p q", positive=True)
    arithmetic = (p+q)/2
    harmonic = 2/(1/p+1/q)
    require(sp.cancel(arithmetic*harmonic - p*q) == 0, "gamma rate midpoint")

    # A centered bivariate Gaussian with unknown precision. Congruence of
    # I and diag(4,9) yields a noncommuting pair with an exact geometric mean.
    mixing = sp.Matrix([[1, 1], [0, 1]])
    first = mixing*mixing.T
    second = mixing*sp.diag(4, 9)*mixing.T
    middle = mixing*sp.diag(2, 3)*mixing.T
    require(first*second != second*first, "noncommuting precisions")
    arithmetic = (first+second)/2
    harmonic = 2*(first.inv()+second.inv()).inv()
    require(middle*first.inv()*middle == second, "original Fisher midpoint")
    require(middle*arithmetic.inv()*middle == harmonic, "updated Fisher midpoint")


def check_three_exponentials() -> None:
    # A coupled two-dimensional statistic obtained from three exponentials.
    x, y = theta = sp.symbols("x y", negative=True)
    psi = -sp.log(-x) - sp.log(-y) - sp.log(-x-y)
    metric = sp.hessian(psi, theta)
    require((x*metric.diff(x)+y*metric.diff(y)+2*metric).applyfunc(sp.cancel)
            == sp.zeros(2), "parallel radial field on the surface")

    at = {x: -1, y: -1}
    inverse_g = metric.subs(at).inv()
    # For h = (1,0), these are kappa_3(h,h,.) and kappa_3(h,.,.).
    third_hh = sp.Matrix([psi.diff(x, 2).diff(v) for v in theta]).subs(at)
    third_h = sp.hessian(psi.diff(x), theta).subs(at)
    k = -inverse_g*third_hh/2
    fourth_hhh = sp.Matrix([psi.diff(x, 3).diff(v) for v in theta]).subs(at)
    scalar = -(fourth_hhh.dot(k)-sp.Rational(3, 2)*third_hh.dot(inverse_g*third_h*k))/2
    require(k == sp.Matrix([-11, 1])/12, "mixed statistic midpoint acceleration")
    require(scalar/128 == sp.Rational(1, 1024), "three-source fourth-order defect")


def check_three_exponential_midpoints() -> None:
    # Recompute the same defect directly by averaging in each affine chart.
    # Flat coordinates are (u,b) with metric 3 du²+2 db². The half-log rate
    # ratio v satisfies v=b-b³/18+O(b⁵), so (u,v) has the same 2-jet at zero.
    u, v, w = sp.symbols("u v w", real=True)
    origin = {u: 0, v: 0}
    cosh = sp.cosh(v)
    rate_scale = sp.exp(u)/cosh**sp.Rational(1, 3)
    rates = rate_scale*sp.Matrix([sp.exp(v), sp.exp(-v)])
    means = sp.Matrix([sp.exp(-v)+1/(2*cosh), sp.exp(v)+1/(2*cosh)])/rate_scale
    second_sum = sp.zeros(2, 1)
    fourth_sum = sp.zeros(2, 1)
    for chart in (rates, means):
        inverse_jacobian = chart.jacobian((u, v)).subs(origin).inv()
        # The symmetric endpoints have (u,b)=(w,w) and (-w,-w), w=t/4.
        along = chart.subs({u: w, v: w-w**3/18})
        series = along.applyfunc(lambda f: sp.series(f, w, 0, 5).removeO().expand())
        second = inverse_jacobian*series.applyfunc(lambda f: f.coeff(w, 2))
        # Invert the averaged chart at order four, retaining its quadratic term.
        quadratic = sp.Matrix([second.dot(sp.hessian(f, (u, v)).subs(origin)*second)/2
                               for f in chart])
        fourth = inverse_jacobian*(series.applyfunc(lambda f: f.coeff(w, 4))-quadratic)
        second_sum += second
        fourth_sum += fourth
    require(second_sum == sp.zeros(2, 1), "opposite quadratic midpoint shifts")
    chord_covector = sp.Matrix([-sp.Rational(3, 2), -1])
    require(chord_covector.dot(fourth_sum)/(2*4**4) == sp.Rational(1, 1024),
            "independent coefficient from the actual parameter averages")


def main() -> int:
    check_midpoint_coefficient()
    check_tensor_contraction()
    check_quartic_kernels()
    check_cumulants_and_shapes()
    check_rate_and_matrix_midpoints()
    check_three_exponentials()
    check_three_exponential_midpoints()
    print("Passed scalar jets, tensor contraction, 20 quartic ranks, "
          "mixed cumulants and shape spectra, single-tilt and matrix controls, "
          "and the three-exponential defect.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
