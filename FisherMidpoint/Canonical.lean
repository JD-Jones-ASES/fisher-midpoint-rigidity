module
public import FisherMidpoint.Family
public import FisherMidpoint.Equidistance

/-! # The law of one fixed affine statistic under every original natural tilt -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped InnerProductSpace BigOperators Topology
namespace FisherMidpoint
variable {ι : Type*} [Fintype ι]

def toCanonical (l x : ℝ) : ℝ := if l = 0 then x else (1/l-x)/l

def canonicalLaw (l u : ι → ℝ) : Measure (ι → ℝ) :=
  Measure.pi (fun i ↦ if l i = 0 then gaussianReal (u i) 1 else gammaMeasure (1/(l i)^2) (1+l i*u i))

theorem canonical_continuous (l : ℝ) : Continuous (toCanonical l) := by
  by_cases h : l = 0 <;> unfold toCanonical <;> simp only [h,ite_true,ite_false] <;> fun_prop

@[simp] theorem toCanonical_zero : toCanonical 0 = id := by funext x; simp [toCanonical]

theorem canonical_bijective (l : ℝ) : Function.Bijective (toCanonical l) := by
  by_cases h : l = 0
  · rw [h,toCanonical_zero]; exact Function.bijective_id
  · refine ⟨fun a b e ↦ ?_,fun y ↦ ⟨1/l-l*y,?_⟩⟩
    · simp only [toCanonical,ite_eq_right h,div_left_inj₀ h] at e; linarith
    · simp [toCanonical,h]

theorem map_toCanonical {l u : ι → ℝ} (hu : admissible l u) :
    (productLaw l u).map (fun x i ↦ toCanonical (l i) (x i)) = canonicalLaw l u := by
  let _ (i : ι) := factor_probability (l i) (u i) (hu i)
  rw [productLaw,Measure.pi_map_pi (fun i ↦ (canonical_continuous (l i)).measurable.aemeasurable)]
  unfold canonicalLaw
  congr 1; funext i
  by_cases h : l i = 0
  · simp [factor,h]
  · simp only [factor,ite_eq_right h]
    rw [Measure.map_map (canonical_continuous _).measurable (by fun_prop)]
    have comp : toCanonical (l i) ∘ (fun y : ℝ ↦ 1/l i + -l i*y) = id := by
      funext; simp [toCanonical,h]
    rw [comp,Measure.map_id]

private theorem tilt_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {f : X → Y} (hf : Measurable f) {g : Y → ℝ} (hg : Measurable g) :
    (μ.tilted (g ∘ f)).map f = (μ.map f).tilted g := by
  ext1 s hs
  rw [Measure.map_apply hf hs,tilted_apply_eq_ofReal_integral' _ (hf hs),
    tilted_apply_eq_ofReal_integral' _ hs,integral_map hf.aemeasurable hg.exp.aestronglyMeasurable,
    setIntegral_map hs ((hg.exp.div_const _).aestronglyMeasurable) hf.aemeasurable]
  rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def naturalDirection (B : OrthonormalBasis ι ℝ H) (F : H → H) (p : H) (u : ι → ℝ) : H :=
  jac F p (B.toBasis.equivFun.symm u)

private theorem pairing_statistic (B : OrthonormalBasis ι ℝ H) (F G : H → H) (p : H) (u : ι → ℝ) (y : H) :
    pairing u (statistic B F G p y) = ⟪naturalDirection B F p u,y-G p⟫_ℝ := by
  rw [naturalDirection,Module.Basis.equivFun_symm_apply,map_sum,sum_inner]
  simp only [map_smul,B.coe_toBasis,real_inner_smul_left,pairing,statistic]

open EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
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

theorem canonical_factorization {Ω : Set E} {F G : E → E} {p : E} (μ : Measure E) [IsProbabilityMeasure μ]
    (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω) (A : FisherChart Ω F G)
    (M : MeanCoordinates μ Ω F G p) (test : ∀ q ∈ Ω, LongitudinalAt F G q) :
    HasGaussianGammaLaw μ F G p := by
  classical
  obtain ⟨B,l,bY,_hLaw,global⟩ := fisher_factorization μ ho hc hp A M test
  let Y := statistic B F G p
  let Z (x : I → ℝ) (i : I) := toCanonical (l i) (x i)
  have mY := (continuous_statistic B F G p).measurable
  have mZ : Measurable Z := (continuous_pi fun i ↦ (canonical_continuous (l i)).comp (continuous_apply i)).measurable
  have bij : Function.Bijective Z := by
    constructor
    · intro x y e; exact funext fun i ↦ (canonical_bijective (l i)).1 (congrFun e i)
    · intro y; choose x hx using fun i ↦ (canonical_bijective (l i)).2 (y i)
      exact ⟨x,funext hx⟩
  refine ⟨B,l,(A.naturalInv p hp).bijective.comp B.toBasis.equivFun.symm.bijective,bij.comp bY,?_⟩
  intro u
  let n := naturalDirection B F p u
  let g := pairing u
  have gcont : Continuous g := by unfold g pairing; fun_prop
  let c := -⟪n,G p⟫_ℝ
  have expnt : g ∘ Y = (fun _ ↦ c) + (fun y : E ↦ ⟪n,y⟫_ℝ) := by
    funext y; simp only [Function.comp_apply,Pi.add_apply,g,Y,pairing_statistic,inner_sub_right]
    change _ = -_+_; ring
  have fin := (global u).1
  rw [integrable_map_measure gcont.measurable.exp.aestronglyMeasurable mY.aemeasurable] at fin
  have eqfn : (fun y ↦ exp (g (Y y))) = (fun y ↦ exp c * exp ⟪n,y⟫_ℝ) := by
    funext y; rw [←exp_add]; exact congrArg exp (congrFun expnt y)
  change Integrable (fun y ↦ exp (g (Y y))) μ ↔ _ at fin
  rw [eqfn,integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (exp_ne_zero _))] at fin
  refine ⟨fin,fun hu ↦ ?_⟩
  have shift := tilted_tilted (μ := μ) (f := fun _ ↦ c) (integrable_const (exp c)) (fun y ↦ ⟪n,y⟫_ℝ)
  rw [tilted_const,←expnt] at shift
  change (μ.tilted (fun y ↦ ⟪n,y⟫_ℝ)).map (Z ∘ Y) = _
  rw [shift,← Measure.map_map mZ mY,tilt_map μ mY gcont.measurable,(global u).2 hu,map_toCanonical hu]

end FisherMidpoint
