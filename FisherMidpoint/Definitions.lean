module
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! # Fisher charts, midpoint observations and the canonical product law

These are the definitions used by the proofs. Their declaration order matches
the self-contained Challenge so that the independently elaborated constants
and the auxiliary proofs generated for their numerals agree in Comparator.
-/

@[expose] public section
noncomputable section
open Set Metric MeasureTheory ProbabilityTheory Real
open scoped Topology InnerProductSpace BigOperators
namespace FisherMidpoint

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Jacobian of a parameter chart. -/
abbrev jac (F : H → H) := fderiv ℝ F

/-- In coordinates where the Fisher metric is the ordinary inner product,
the differentials of the natural and expectation charts are mutually dual. -/
structure FisherChart (Ω : Set H) (θ η : H → H) : Prop where
  natural : ∀ x ∈ Ω, ContDiffAt ℝ 4 θ x
  expected : ∀ x ∈ Ω, ContDiffAt ℝ 4 η x
  naturalInv : ∀ x ∈ Ω, (jac θ x).IsInvertible
  expectedInv : ∀ x ∈ Ω, (jac η x).IsInvertible
  metric : ∀ x ∈ Ω, ∀ a b, ⟪jac η x a,jac θ x b⟫_ℝ = ⟪a,b⟫_ℝ

end

/-- Scalar little-o condition on the actual affine averages, in a Fisher isometry chart.
The sum of the two displacements is twice the displacement of their Fisher midpoint. -/
def LongitudinalAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (F G : H → H) (p : H) : Prop :=
  ∀ h : H, ∀ κ > (0:ℝ), ∃ r > (0:ℝ), ∃ δ > (0:ℝ), ∀ t : ℝ, 0 < t → t < δ →
    ∀ a ∈ ball p r, ∀ b ∈ ball p r,
      F a + F a = F (p-(t/2)•h) + F (p+(t/2)•h) →
      G b + G b = G (p-(t/2)•h) + G (p+(t/2)•h) →
      |⟪h,(a-p)+(b-p)⟫_ℝ| ≤ κ*t^4

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Natural and expectation midpoints of a nearby pair have the same Fisher midpoint
as the original endpoints. Sums express twice the Fisher midpoint in this chart. -/
def PreservesAt (F G : H → H) (p : H) : Prop :=
  ∃ r > (0:ℝ), ∀ P ∈ ball p r, ∀ Q ∈ ball p r, ∀ a ∈ ball p r, ∀ b ∈ ball p r,
    F a+F a=F P+F Q → G b+G b=G P+G Q → a+b=P+Q

/-- The updated Fisher midpoint is equidistant from the two original endpoints. -/
def EquidistantAt (F G : H → H) (p : H) : Prop :=
  ∃ r > (0:ℝ), ∀ P ∈ ball p r, ∀ Q ∈ ball p r, ∀ a ∈ ball p r, ∀ b ∈ ball p r,
    F a+F a=F P+F Q → G b+G b=G P+G Q → ‖a+b-(2:ℝ)•P‖=‖a+b-(2:ℝ)•Q‖

/-- The log-Laplace transform of the sufficient statistic at the reference member. -/
def cumulant [MeasurableSpace H] (μ : Measure H) (u : H) : ℝ :=
  log (∫ y, exp ⟪u,y⟫_ℝ ∂μ)

/-- Natural parameters are measured relative to the reference member at `p`.
The expectation coordinate is the gradient of the actual log-Laplace transform. -/
structure MeanCoordinates [MeasurableSpace H] (μ : Measure H) (Ω : Set H) (F G : H → H) (p : H) : Prop where
  finite : ∀ x ∈ Ω, Integrable (fun y ↦ exp ⟪F x-F p,y⟫_ℝ) μ
  mean : ∀ x ∈ Ω, HasFDerivAt (cumulant μ) (innerSL ℝ (G x)) (F x-F p)

variable {ι : Type*} [Fintype ι]

/-- Fisher-unit score coordinates, centered at the expected statistic of the reference member. -/
def statistic (B : OrthonormalBasis ι ℝ H) (F G : H → H) (p y : H) (i : ι) : ℝ :=
  ⟪jac F p (B i),y-G p⟫_ℝ

/-- The scalar affine rescaling which turns each nonzero score axis into a positive gamma coordinate. -/
def toCanonical (l x : ℝ) : ℝ := if l = 0 then x else (1/l-x)/l

/-- Gaussian coordinates have variance one. Each gamma coordinate has a fixed positive shape and affine rate. -/
def canonicalLaw (l u : ι → ℝ) : Measure (ι → ℝ) :=
  Measure.pi (fun i ↦ if l i = 0 then gaussianReal (u i) 1 else gammaMeasure (1/(l i)^2) (1+l i*u i))

/-- The dual linear change from score parameters to original natural-parameter increments. -/
def naturalDirection (B : OrthonormalBasis ι ℝ H) (F : H → H) (p : H) (u : ι → ℝ) : H :=
  jac F p (B.toBasis.equivFun.symm u)

end

section
variable {ι : Type*} [Fintype ι]

/-- Exact finiteness region in the centered natural coordinates. -/
def admissible (l u : ι → ℝ) : Prop := ∀ i, 0 < 1 + l i * u i

/-- Log-partition of the unit-variance centered coordinate in affine natural parameter. -/
def axisCGF (l u : ℝ) : ℝ := if l = 0 then u^2/2 else u/l - log (1+l*u)/l^2

/-- The Gaussian axis has mean `u`. A nonzero axis is a fixed invertible affine
image of a gamma variable of shape `1/l²` and rate `1+l*u`. -/
def factor (l u : ℝ) : Measure ℝ :=
  if l = 0 then gaussianReal u 1 else
    (gammaMeasure (1/l^2) (1+l*u)).map (fun y : ℝ ↦ 1/l + (-l)*y)

/-- Law of the centered score vector at tilt `u`. -/
def productLaw (l u : ι → ℝ) : Measure (ι → ℝ) := Measure.pi (fun i ↦ factor (l i) (u i))

/-- Natural-parameter pairing in score coordinates. -/
def pairing (v x : ι → ℝ) : ℝ := ∑ i, v i * x i

end

/-- Normalized affine coordinate on a Fisher axis with multiplication coefficient `l`. -/
def sExp (l t : ℝ) : ℝ := if l = 0 then t else (Real.exp (l*t) - 1) / l

/-- Reconstruct the natural or expectation displacement along the axes. -/
def axisMap {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [Fintype ι]
    (B : Module.Basis ι ℝ H) (l : ι → ℝ) (z : H) : H :=
  ∑ i, sExp (l i) (B.repr z i) • B i

/-- The first derivative of the standardized log-partition is the expectation coordinate. -/
def axisMean (l u : ℝ) : ℝ := u / (1+l*u)

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "I" => Fin (Module.finrank ℝ E)

/-- The affine change of statistics, the dual linear change of natural parameters,
the exact finiteness set and the Gaussian/gamma product under every tilt. -/
def HasGaussianGammaLaw (μ : Measure E) (F G : E → E) (p : E) : Prop :=
  ∃ (B : OrthonormalBasis I ℝ E) (l : I → ℝ),
    let N := naturalDirection B F p
    let Z := fun y i ↦ toCanonical (l i) (statistic B F G p y i)
    Function.Bijective N ∧ Function.Bijective Z ∧
    ∀ u : I → ℝ, (Integrable (fun y ↦ exp ⟪N u,y⟫_ℝ) μ ↔ admissible l u) ∧
      (admissible l u → (μ.tilted (fun y ↦ ⟪N u,y⟫_ℝ)).map Z = canonicalLaw l u)

end FisherMidpoint
