module
public import FisherMidpoint.Definitions
public import FisherMidpoint.Parallel
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Curvature of the two affine coordinate systems -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology InnerProductSpace ContDiff
namespace FisherMidpoint
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
/-- Christoffel transformation equation in a chart whose ordinary derivative is Levi-Civita. -/
def AffineFor (Ω : Set H) (F : H → H) (K : H → ProductTensor H) : Prop :=
  ∀ p ∈ Ω, ∀ u v, fderiv ℝ (jac F) p u v = jac F p (K p u v)

private theorem column_diff {G : H → H →L[ℝ] H} {p : H} (d : DifferentiableAt ℝ G p) (v : H) :
    HasFDerivAt (fun x ↦ G x v) ((fderiv ℝ G p).flip v) p := by
  convert d.hasFDerivAt.clm_apply (hasFDerivAt_const v p) using 1
  ext h; simp

theorem affine_curvature {Ω : Set H} {F : H → H} {K : H → ProductTensor H}
    (ho : IsOpen Ω) (reg : ∀ x ∈ Ω, ContDiffAt ℝ 3 F x)
    (inj : ∀ x ∈ Ω, Function.Injective (jac F x)) (aff : AffineFor Ω F K)
    {p : H} (hp : p ∈ Ω) (hD : DifferentiableAt ℝ K p) (a b w : H) :
    K p a (K p b w) + fderiv ℝ K p a b w =
      K p b (K p a w) + fderiv ℝ K p b a w := by
  let g (x : H) := jac F x w
  have Dr (x : H) (hx : x ∈ Ω) : ContDiffAt ℝ 2 (jac F) x :=
    (reg x hx).fderiv_right (by decide)
  have h2 : ContDiffAt ℝ 2 g p := (Dr p hp).clm_apply contDiffAt_const
  have eqn (v u : H) : fderiv ℝ (fderiv ℝ g) p u v =
      jac F p (K p u (K p v w) + fderiv ℝ K p u v w) := by
    have near : (fun x ↦ fderiv ℝ g x v) =ᶠ[𝓝 p] fun x ↦ jac F x (K x v w) := by
      filter_upwards [ho.mem_nhds hp] with x hx
      exact (congrArg (fun L : H →L[ℝ] H ↦ L v)
        (column_diff ((Dr x hx).differentiableAt (by decide)) w).fderiv).trans (aff x hx v w)
    have dl := column_diff ((h2.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)) v
    have dr := ((Dr p hp).differentiableAt (by decide)).hasFDerivAt.clm_apply (eval_derivative hD v w)
    have hh := congrArg (fun L : H →L[ℝ] H ↦ L u) (dl.unique (dr.congr_of_eventuallyEq near))
    simpa [aff p hp, add_comm] using hh
  exact inj p hp ((eqn b a).symm.trans ((h2.isSymmSndFDerivAt (by simp) a b).trans (eqn a b)))

set_option backward.isDefEq.respectTransparency false in
/-- Adding and subtracting the two curvature equations gives commutation and Codazzi. -/
theorem dual_curvature {Ω : Set H} {F G : H → H} {K : H → ProductTensor H}
    (ho : IsOpen Ω) (rF : ∀ x ∈ Ω, ContDiffAt ℝ 3 F x) (rG : ∀ x ∈ Ω, ContDiffAt ℝ 3 G x)
    (iF : ∀ x ∈ Ω, Function.Injective (jac F x)) (iG : ∀ x ∈ Ω, Function.Injective (jac G x))
    (aF : AffineFor Ω F K) (aG : AffineFor Ω G (-K)) {p : H} (hp : p ∈ Ω)
    (hD : DifferentiableAt ℝ K p) :
    Commutes (K p) ∧ ∀ a b w, fderiv ℝ K p a b w = fderiv ℝ K p b a w := by
  have negD := HasFDerivAt.neg (𝕜 := ℝ) (f := K) (f' := fderiv ℝ K p) (x := p) hD.hasFDerivAt
  have signed (a b w : H) := affine_curvature ho rG iG aG hp negD.differentiableAt a b w
  have dn := negD.fderiv
  constructor <;> intro a b w <;>
    have h₁ := affine_curvature ho rF iF aF hp hD a b w <;>
    have h₂ := signed a b w <;>
    simp only [dn,Pi.neg_apply,neg_apply,map_neg,neg_neg] at h₂ <;>
    first | linear_combination (norm := module) (1/2:ℝ) • h₁ + (1/2:ℝ) • h₂
          | linear_combination (norm := module) (1/2:ℝ) • h₁ - (1/2:ℝ) • h₂

end FisherMidpoint
