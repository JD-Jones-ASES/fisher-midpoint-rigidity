module
public import FisherMidpoint.Charts
public import FisherMidpoint.Integration

/-! # The longitudinal midpoint condition gives one fixed set of Fisher axes -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology InnerProductSpace ContDiff
namespace FisherMidpoint
open EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d

private theorem chart_parallel {Ω : Set E} {F G : E → E}
    (ho : IsOpen Ω) (hc : IsPreconnected Ω) (A : FisherChart Ω F G)
    {C : E → Cubic d} (hC : ContDiffOn ℝ 2 C Ω)
    (aF : AffineFor Ω F (raw C)) (aG : AffineFor Ω G (-(raw C)))
    (test : ∀ p ∈ Ω, LongitudinalAt F G p) :
    ∀ p ∈ Ω, ∀ q ∈ Ω, raw C p = raw C q := by
  let inc : Cubic d →L[ℝ] ProductTensor E := (cubicSubspace d).subtypeL
  have Dr (x : E) (hx : x ∈ Ω) : HasFDerivAt (raw C) (inc.comp (fderiv ℝ C x)) x :=
    inc.hasFDerivAt.comp x (((hC x hx).contDiffAt (ho.mem_nhds hx)).differentiableAt (by decide)).hasFDerivAt
  have cur (x : E) (hx : x ∈ Ω) := dual_curvature ho
    (fun p hp ↦ (A.natural p hp).of_le (by decide)) (fun p hp ↦ (A.expected p hp).of_le (by decide))
    (fun p hp ↦ (A.naturalInv p hp).bijective.1) (fun p hp ↦ (A.expectedInv p hp).bijective.1)
    aF aG hx (Dr x hx).differentiableAt
  have sym (x : E) (hx : x ∈ Ω) : SymmetricJet (fderiv ℝ (raw C) x) := by
    constructor
    · intro a b c e; unfold form; rw [(cur x hx).2 a b c]
    · intro a b c e; rw [(Dr x hx).fderiv]
      exact congrArg (fun v : E ↦ ⟪v,e⟫_ℝ) ((fderiv ℝ C x a).property.1 b c)
    · intro a b c e; rw [(Dr x hx).fderiv]
      exact ((fderiv ℝ C x a).property.2 b c e).trans (real_inner_comm _ _)
  have scalar (x : E) (hx : x ∈ Ω) (h : E) :
      form (fderiv ℝ (raw C) x) h h h (raw C x h h) = 0 := by
    let k := raw C x h h
    let J := fderiv ℝ C x
    let T := fderiv ℝ (raw C) x
    have S := sym x hx
    have perm : form T k h h h = form T h h h k := by
      dsimp only [T]; rw [S.first k h h h,S.middle h k h h,S.last h h k h]
    have t1 : ⟪K (C x) h (K (J h) h h),h⟫_ℝ = form T h h h k := by
      dsimp only [T]; rw [(Dr x hx).fderiv]; exact (C x).property.2 h _ h
    have t2 : ⟪K (J k) h h,h⟫_ℝ = form T h h h k := by
      rw [←perm]; dsimp only [T]; rw [(Dr x hx).fderiv]; rfl
    have t3 : ⟪K (J h) h k,h⟫_ℝ = form T h h h k := by
      rw [←S.last h h k h]; rw [(Dr x hx).fderiv]; rfl
    have z := longitudinal_obstruction ho hx hC (fun p hp ↦ (A.natural p hp).of_le (by decide))
      (fun p hp ↦ (A.expected p hp).of_le (by decide)) aF aG (test x hx) h
    rw [real_inner_comm] at z
    change ⟪2 • K (C x) h (K (J h) h h) + 5 • K (J k) h h - 4 • K (J h) h k,h⟫_ℝ = 0 at z
    simp only [inner_sub_left,inner_add_left,←Nat.cast_smul_eq_nsmul ℝ,real_inner_smul_left,t1,t2,t3] at z
    change form T h h h k = 0
    push_cast at z; linarith
  intro p hp q hq
  exact constant_of_longitudinal ho hc (fun x hx ↦ (Dr x hx).differentiableAt)
    (fun x _ ↦ (C x).property) (fun x hx ↦ (cur x hx).1) sym scalar hq hp

/-- The two charts have opposite diagonal second derivatives in one fixed orthonormal basis. -/
theorem midpoint_axes {Ω : Set E} {F G : E → E}
    (ho : IsOpen Ω) (hc : IsPreconnected Ω) (A : FisherChart Ω F G)
    (test : ∀ p ∈ Ω, LongitudinalAt F G p) {p : E} (hp : p ∈ Ω) :
    ∃ (B : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) (l : Fin (Module.finrank ℝ E) → ℝ),
      ∀ x ∈ Ω, ∀ h i,
        fderiv ℝ (jac F) x h (B i) = (l i * B.repr h i) • jac F x (B i) ∧
        fderiv ℝ (jac G) x h (B i) = (-(l i) * B.repr h i) • jac G x (B i) := by
  obtain ⟨C,hC,aF,aG⟩ := chart_cubic ho A
  let inc : Cubic d →L[ℝ] ProductTensor E := (cubicSubspace d).subtypeL
  have hd : DifferentiableAt ℝ (raw C) p := inc.differentiableAt.comp p
    (((hC p hp).contDiffAt (ho.mem_nhds hp)).differentiableAt (by decide))
  have com := (dual_curvature ho (fun x hx ↦ (A.natural x hx).of_le (by decide))
    (fun x hx ↦ (A.expected x hx).of_le (by decide)) (fun x hx ↦ (A.naturalInv x hx).bijective.1)
    (fun x hx ↦ (A.expectedInv x hx).bijective.1) aF aG hp hd).1
  obtain ⟨B,l,axes⟩ := orthogonal_axes (raw C p) (C p).property com
  refine ⟨B,l,fun x hx h i ↦ ?_⟩
  have eqn := chart_parallel ho hc A hC aF aG test x hx p hp
  rw [aF x hx,aG x hx,Pi.neg_apply,eqn]
  simp [axes h i, neg_mul]

end FisherMidpoint
