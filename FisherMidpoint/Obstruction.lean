module
public import FisherMidpoint.Midpoints

/-! # Contraction of the geodesic remainder against the original chord -/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped Topology InnerProductSpace ContDiff
namespace FisherMidpoint
open EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d
local notation "Hessian" => SpatialHessian d

theorem longitudinal_obstruction {Ω : Set E} {C : E → Coeff} {p : E} {F G : E → E}
    (hΩ : IsOpen Ω) (hp : p ∈ Ω) (hC : ContDiffOn ℝ 2 C Ω)
    (rF : ∀ x ∈ Ω, ContDiffAt ℝ 2 F x) (rG : ∀ x ∈ Ω, ContDiffAt ℝ 2 G x)
    (aF : AffineFor Ω F (raw C)) (aG : AffineFor Ω G (-(raw C)))
    (test : LongitudinalAt F G p) (h : E) :
    ⟪h,obstruction (C p) (fderiv ℝ C p) h⟫_ℝ = 0 := by
  let c := C p
  let J := fderiv ℝ C p
  let H : Hessian := fderiv ℝ (fderiv ℝ C) p
  let e := obstruction c J h
  change ⟪h,e⟫_ℝ = 0
  by_contra he
  let κ := |⟪h,e⟫_ℝ| / (1000*(2*‖h‖+1))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨r,hr,M,hM,L,hL,_hsub,hbound,hLip,hsmall⟩ := local_coefficient_bounds hΩ hp hC
  have hTaylor : ∀ η > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ d : E, ‖d‖ < ρ →
      ‖C (p+d)-c-J d-(1/2 : ℝ)•H d d‖ ≤ η*‖d‖^2 := by
    intro η hη
    obtain ⟨ρ,hρ,_hsub,herr⟩ := exists_second_order_spatial_remainder hΩ hp hC hη
    exact ⟨ρ,hρ,herr⟩
  have hTaylorMinus : ∀ η > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ d : E, ‖d‖ < ρ →
      ‖(-C) (p+d)-(-c)-(-J) d-(1/2 : ℝ)•(-H) d d‖ ≤ η*‖d‖^2 := by
    intro η hη
    obtain ⟨ρ,hρ,herr⟩ := hTaylor η hη
    refine ⟨ρ,hρ,?_⟩
    intro d hd
    rw [neg_coeff_taylor_remainder]
    exact herr d hd
  obtain ⟨δPlus,hδPlus,hPlus⟩ := exists_short_geodesic_approximation
    C p c J H h r M L hr hM hL hbound hLip hsmall hTaylor κ hκ
  obtain ⟨δMinus,hδMinus,hMinus⟩ := exists_short_geodesic_approximation
    (-C) p (-c) (-J) (-H) h r M L hr hM hL
    (fun x hx ↦ by simpa only [Pi.neg_apply, norm_neg] using hbound x hx)
    (fun x hx y hy ↦ by simpa only [norm_neg_coeff_sub] using hLip x hx y hy)
    hsmall hTaylorMinus κ hκ
  obtain ⟨rTest,hrTest,δTest,hδTest,hTest⟩ := test h κ hκ
  let s := min r rTest
  have hs : 0 < s := lt_min hr hrTest
  have hc : ContDiffAt ℝ 1 C p := ((hC p hp).contDiffAt (hΩ.mem_nhds hp)).of_le (by decide)
  obtain ⟨d₁,hd₁,H₁⟩ := exists_arbitrarily_short_geodesic hc 1 s hs
  obtain ⟨d₂,hd₂,H₂⟩ := exists_arbitrarily_short_geodesic hc (-1) s hs
  let δPair := min d₁ d₂
  have hδPair : 0 < δPair := lt_min hd₁ hd₂
  obtain ⟨ε,hε,hδ⟩ := exists_between (show 0 < min δPlus (min δMinus (min δTest (δPair/(‖h‖+1)))) by positivity)
  simp only [lt_min_iff] at hδ
  obtain ⟨hεPlus,hεMinus,hεTest,hεEnd⟩ := hδ
  have hscalar : (ε/2)*‖h‖ < δPair := by
    have hh := (lt_div_iff₀ (show 0 < ‖h‖+1 by positivity)).mp hεEnd
    nlinarith [norm_nonneg h]
  have hP : p-(ε/2)•h ∈ ball p δPair := by
    rw [mem_ball, dist_eq_norm]
    have hh : p-(ε/2)•h-p = -((ε/2)•h) := by module
    rw [hh, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hscalar
  have hQ : p+(ε/2)•h ∈ ball p δPair := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hscalar
  obtain ⟨γ₁,v₁,g₁⟩ := H₁ _ _ (ball_subset_ball (min_le_left _ _) hP) (ball_subset_ball (min_le_left _ _) hQ)
  obtain ⟨γ₂,v₂,g₂⟩ := H₂ _ _ (ball_subset_ball (min_le_right _ _) hP) (ball_subset_ball (min_le_right _ _) hQ)
  have sub : ball p s ⊆ Ω := (ball_subset_ball (min_le_left _ _)).trans _hsub
  have fmean := affine_midpoint rF 1 (fun x hx a b ↦ by simpa using aF x hx a b) sub g₁
  have gmean := affine_midpoint rG (-1) (fun x hx a b ↦ by simpa using aG x hx a b) sub g₂
  have mb (γ v : ℝ → E) (σ : ℝ) (g : IsShortGeodesic C σ p s (p-(ε/2)•h) (p+(ε/2)•h) γ v) :
      γ (1/2) ∈ ball p rTest := by
    rw [mem_ball,dist_eq_norm]
    exact lt_of_lt_of_le (g.2.2.2 (1/2) (by norm_num)).1 (min_le_right _ _)
  have scalar := hTest ε hε hεTest _ (mb _ _ _ g₁) _ (mb _ _ _ g₂) fmean gmean
  let dP := approxDisplacement c J H h ε (1/2)
  let dM := approxDisplacement (-c) (-J) (-H) h ε (1/2)
  have herrP := hPlus ε hε.le hεPlus γ₁ v₁ (g₁.mono_radius (min_le_left _ _))
  have herrM := hMinus ε hε.le hεMinus γ₂ v₂
    ((isShortGeodesic_neg C p r _ _ γ₂ v₂).mp (g₂.mono_radius (min_le_left _ _)))
  let errP := γ₁ (1/2) - (p+dP)
  let errM := γ₂ (1/2) - (p+dM)
  have ep : |⟪h,errP⟫_ℝ| ≤ ‖h‖*(κ*ε^4) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left herrP (norm_nonneg _))
  have em : |⟪h,errM⟫_ℝ| ≤ ‖h‖*(κ*ε^4) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left herrM (norm_nonneg _))
  have geom : dP+dM = ((γ₁ (1/2)-p)+(γ₂ (1/2)-p)) - errP - errM := by dsimp [errP,errM]; module
  have poly : dP+dM = (ε^4/192)•e := approxDisplacement_add_opposite_midpoint c J H h ε
  have bound : |⟪h,dP+dM⟫_ℝ| ≤ (2*‖h‖+1)*κ*ε^4 := by
    rw [geom,inner_sub_right,inner_sub_right]
    grw [abs_sub,abs_sub,scalar,ep,em]
    apply le_of_eq; ring
  rw [poly,real_inner_smul_right,abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ ε^4/192)] at bound
  have cancel : |⟪h,e⟫_ℝ|/192 ≤ (2*‖h‖+1)*κ := by
    apply le_of_mul_le_mul_right (a := ε^4) _ (pow_pos hε 4)
    linarith only [bound]
  have kappa : (2*‖h‖+1)*κ = |⟪h,e⟫_ℝ|/1000 := by
    dsimp [κ]; field_simp [show (2*‖h‖+1) ≠ 0 by positivity]
  rw [kappa] at cancel
  linarith [abs_pos.mpr he]

end FisherMidpoint
