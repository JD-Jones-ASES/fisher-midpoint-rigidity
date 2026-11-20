# Fisher midpoint rigidity

This Lean project studies which flat exponential families preserve the Fisher midpoint when two endpoints are replaced by their natural and expectation averages.

The first development checkpoint proves the tensor implication behind the longitudinal fourth-order test. Let (K) be a differentiable symmetric metric product on a connected Euclidean open set. Suppose its multiplication operators commute and its lowered derivative is fully symmetric. If `⟪(D_h K)(h,h), K(h,h)⟫ = 0` in every direction at every point, then (K) is constant. This includes points where some or all multiplication operators vanish.

Run `lake build` using the pinned Lean toolchain.
