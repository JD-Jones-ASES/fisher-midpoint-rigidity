module
public import FisherMidpoint.Flat
public import EuclideanMidpointRigidity.CanonicalMidpoints
public import EuclideanMidpointRigidity.AnalyticObstruction

/-! # The fourth-order test on actual natural and expectation averages -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped Topology InnerProductSpace ContDiff
namespace FisherMidpoint
open EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
abbrev raw (C : E → Cubic d) (x : E) : ProductTensor E := (C x).val

/-- Scalar little-o condition on the actual affine averages, in a Fisher isometry chart.
The sum of the two displacements is twice the displacement of their Fisher midpoint. -/
def LongitudinalAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (F G : H → H) (p : H) : Prop :=
  ∀ h : H, ∀ κ > (0:ℝ), ∃ r > (0:ℝ), ∃ δ > (0:ℝ), ∀ t : ℝ, 0 < t → t < δ →
    ∀ a ∈ ball p r, ∀ b ∈ ball p r,
      F a + F a = F (p-(t/2)•h) + F (p+(t/2)•h) →
      G b + G b = G (p-(t/2)•h) + G (p+(t/2)•h) →
      |⟪h,(a-p)+(b-p)⟫_ℝ| ≤ κ*t^4

private theorem interval_constant {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ℝ → H} (h : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f 0 t)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : f t = f 0 := by
  have eqn := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := 0) (fun t ht ↦ (h t ht).hasDerivWithinAt) (by simp) (show (0:ℝ) ∈ Icc 0 1 by norm_num) ht
  exact sub_eq_zero.mp (by simpa using eqn)

theorem affine_midpoint {Ω : Set E} {C : E → Cubic d} {F : E → E}
    (reg : ∀ x ∈ Ω, ContDiffAt ℝ 2 F x) (σ : ℝ)
    (aff : ∀ x ∈ Ω, ∀ a b, fderiv ℝ (jac F) x a b = jac F x (σ • raw C x a b))
    {p P Q : E} {r : ℝ} {γ v : ℝ → E} (sub : ball p r ⊆ Ω)
    (g : IsShortGeodesic C σ p r P Q γ v) : F (γ (1/2))+F (γ (1/2)) = F P+F Q := by
  have mem t (ht : t ∈ Icc (0:ℝ) 1) : γ t ∈ Ω := sub (by
    rw [mem_ball,dist_eq_norm]; exact (g.2.2.2 t ht).1)
  let V (t : ℝ) := jac F (γ t) (v t)
  have dV t (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt V 0 t := by
    have j := (((reg _ (mem t ht)).fderiv_right (m := 1) (by decide)).differentiableAt
      (by decide)).hasFDerivAt.comp_hasDerivAt t (g.1.1 t ht)
    convert j.clm_apply (g.1.2 t ht) using 1
    · rfl
    change 0 = fderiv ℝ (jac F) (γ t) (v t) (v t) + jac F (γ t) ((-σ) • raw C (γ t) (v t) (v t))
    rw [aff _ (mem t ht),map_smul,map_smul,neg_smul,add_neg_cancel]
  have dF t (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt (fun s ↦ F (γ s) - s • V 0) 0 t := by
    have h1 := ((reg _ (mem t ht)).differentiableAt (by decide)).hasFDerivAt.comp_hasDerivAt t (g.1.1 t ht)
    have h2 := h1.sub ((hasDerivAt_id' t).smul_const (V 0))
    have eqn := interval_constant dV ht
    change jac F (γ t) (v t) = V 0 at eqn
    simpa only [Function.comp_def,Pi.sub_def,eqn,one_smul,sub_self] using h2
  have hm := interval_constant dF (t := 1/2) (by norm_num)
  have he := interval_constant dF (t := 1) (by norm_num)
  simp only [g.2.1,g.2.2.1,zero_smul,sub_zero,one_smul] at hm he
  linear_combination (norm := module) (2:ℝ) • hm - he

end FisherMidpoint
