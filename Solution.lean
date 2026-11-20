module
public import FisherMidpoint

@[expose] public section
noncomputable section
open Set Metric MeasureTheory ProbabilityTheory Real
open scoped Topology InnerProductSpace BigOperators
namespace FisherMidpoint

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "I" => Fin (Module.finrank ℝ E)

/-- Exact preservation of Fisher midpoints forces the Gaussian and gamma factors for every natural tilt. -/
theorem from_exact_averages {Ω : Set E} {F G : E → E} {p : E} (μ : Measure E) [IsProbabilityMeasure μ]
    (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω) (A : FisherChart Ω F G)
    (M : MeanCoordinates μ Ω F G p) (H : ∀ q ∈ Ω, PreservesAt F G q) :
    HasGaussianGammaLaw μ F G p := by
  exact canonical_factorization μ ho hc hp A M fun q hq ↦
    longitudinal_of_equidistant (equidistant_of_preserves (H q hq))

/-- Equidistance of the updated midpoint from the two original endpoints suffices. -/
theorem from_equidistance {Ω : Set E} {F G : E → E} {p : E} (μ : Measure E) [IsProbabilityMeasure μ]
    (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω) (A : FisherChart Ω F G)
    (M : MeanCoordinates μ Ω F G p) (H : ∀ q ∈ Ω, EquidistantAt F G q) :
    HasGaussianGammaLaw μ F G p := by
  exact canonical_factorization μ ho hc hp A M fun q hq ↦ longitudinal_of_equidistant (H q hq)

/-- Vanishing of only the longitudinal fourth-order midpoint displacement suffices on one patch. -/
theorem from_fourth_order {Ω : Set E} {F G : E → E} {p : E} (μ : Measure E) [IsProbabilityMeasure μ]
    (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω) (A : FisherChart Ω F G)
    (M : MeanCoordinates μ Ω F G p) (H : ∀ q ∈ Ω, LongitudinalAt F G q) :
    HasGaussianGammaLaw μ F G p := by
  exact canonical_factorization μ ho hc hp A M H

/-- A single orthonormal basis integrates both parameter charts on the whole patch. -/
theorem affine_chart_formulas {Ω : Set E} {F G : E → E} {p : E}
    (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω) (A : FisherChart Ω F G)
    (H : ∀ q ∈ Ω, LongitudinalAt F G q) :
    ∃ (B : OrthonormalBasis I ℝ E) (l : I → ℝ), ∀ x ∈ Ω,
      F x = F p + jac F p (axisMap B.toBasis l (x-p)) ∧
      G x = G p + jac G p (axisMap B.toBasis (-l) (x-p)) := by
  obtain ⟨B,l,axes⟩ := midpoint_axes ho hc A H hp
  refine ⟨B,l,fun x hx ↦ ⟨?_,?_⟩⟩
  · exact integrate_axes ho hc hp (fun y hy ↦ (A.natural y hy).of_le (by decide)) B.toBasis l
      (fun y hy h i ↦ by simpa using (axes y hy h i).1) x hx
  · exact integrate_axes ho hc hp (fun y hy ↦ (A.expected y hy).of_le (by decide)) B.toBasis (-l)
      (fun y hy h i ↦ by simpa using (axes y hy h i).2) x hx

/-- The actual transform of the centered score product, on its exact integrability domain. -/
theorem product_log_partition {ι : Type*} [Fintype ι] (l v : ι → ℝ) :
    (Integrable (fun x ↦ exp (pairing v x)) (productLaw l 0) ↔ admissible l v) ∧
    (admissible l v → (∫ x, exp (pairing v x) ∂productLaw l 0) = exp (∑ i, axisCGF (l i) (v i))) := by
  exact ⟨by simpa using product_domain (admissible_zero l) v,fun hv ↦ base_laplace hv⟩

/-- The gamma Laplace integral diverges at its boundary and beyond. -/
theorem gamma_transform_and_domain {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (Integrable (fun x : ℝ ↦ exp (t*x)) (gammaMeasure a r) ↔ t < r) ∧
    (t < r → mgf id (gammaMeasure a r) t = (r/(r-t))^a) := by
  exact ⟨gamma_domain ha hr, gamma_mgf ha hr⟩

/-- The canonical products have unique natural and expectation averages for every pair, and preserve its Fisher midpoint. -/
theorem global_product_averages {ι : Type*} (l : ι → ℝ) (x y : ι → ℝ) :
    ∃ a b : ι → ℝ,
      (∀ i, sExp (l i) (a i) + sExp (l i) (a i) = sExp (l i) (x i)+sExp (l i) (y i)) ∧
      (∀ i, sExp (-(l i)) (b i) + sExp (-(l i)) (b i) = sExp (-(l i)) (x i)+sExp (-(l i)) (y i)) ∧
      a+b=x+y ∧ ∀ A B : ι → ℝ,
        (∀ i, sExp (l i) (A i)+sExp (l i) (A i)=sExp (l i) (x i)+sExp (l i) (y i)) →
        (∀ i, sExp (-(l i)) (B i)+sExp (-(l i)) (B i)=sExp (-(l i)) (x i)+sExp (-(l i)) (y i)) →
        A=a ∧ B=b := by
  exact product_midpoints l x y

/-- Each canonical axis has its true mean coordinate and unit Fisher speed. -/
theorem fisher_axis_coordinates (l x : ℝ) :
    (∀ u : ℝ, 0 < 1+l*u → HasDerivAt (axisCGF l) (axisMean l u) u) ∧
    0 < 1+l*sExp l x ∧ axisMean l (sExp l x) = sExp (-l) x ∧
    exp (l*x) * exp ((-l)*x) = 1 := by
  exact ⟨fun _ hu ↦ axis_cumulant_deriv hu,axis_chart_metric l x⟩

end FisherMidpoint
