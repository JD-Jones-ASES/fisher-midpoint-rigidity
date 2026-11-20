module
public import FisherMidpoint.Quartic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Vanishing of the derivative, including on the null subspace -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology InnerProductSpace BigOperators
namespace FisherMidpoint
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem orthogonal_to_range (K : ProductTensor H) (J : Jet H)
    (hs : SymmetricProduct K) (hc : Commutes K) (S : SymmetricJet J)
    (hp : ∀ h, form J h h h (K h h) = 0) (z u v a b : H) :
    ⟪J z u v,K a b⟫_ℝ = 0 := by
  classical
  obtain ⟨B,l,hB⟩ := orthogonal_axes K hs hc
  have hb : K a b = ∑ i, K a (B.repr b i • B i) := by rw [← map_sum, B.sum_repr]
  rw [hb]
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul,hB, real_inner_smul_right,real_inner_smul_right]
  by_cases hl : l i = 0
  · simp [hl]
  · have hχ : l i * B.repr (B i) i ≠ 0 := by simpa using hl
    have h := active_axis K J hs S hp (B i) (fun x ↦ l i * B.repr x i) (fun x ↦ hB x i) hχ z u v
    simp [form] at h
    rw [h]; ring

variable {Ω : Set H} {K : H → ProductTensor H}

omit [FiniteDimensional ℝ H] in
theorem eval_derivative {p : H} (D : DifferentiableAt ℝ K p) (a b : H) :
    HasFDerivAt (fun x ↦ K x a b)
      ((((fderiv ℝ K p).flip a)).flip b) p := by
  convert (D.hasFDerivAt.clm_apply (hasFDerivAt_const a p)).clm_apply
    (hasFDerivAt_const b p) using 1
  ext h
  simp

/-- Longitudinal vanishing freezes the cubic on a connected open flat Hessian chart. -/
theorem parallel_of_longitudinal (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (hD : ∀ p ∈ Ω, DifferentiableAt ℝ K p)
    (hs : ∀ p ∈ Ω, SymmetricProduct (K p)) (hm : ∀ p ∈ Ω, Commutes (K p))
    (hS : ∀ p ∈ Ω, SymmetricJet (fderiv ℝ K p))
    (hp : ∀ p ∈ Ω, ∀ h, form (fderiv ℝ K p) h h h (K p h h) = 0) :
    ∀ p ∈ Ω, fderiv ℝ K p = 0 := by
  have ort p (h : p ∈ Ω) := orthogonal_to_range (K p) (fderiv ℝ K p)
    (hs p h) (hm p h) (hS p h) (hp p h)
  have flat (a b : H) {p q : H} (hP : p ∈ Ω) (hQ : q ∈ Ω) :
      ⟪K q a b,K q a b⟫_ℝ = ⟪K p a b,K p a b⟫_ℝ := by
    let f (x : H) := ⟪K x a b,K x a b⟫_ℝ
    have hf (x : H) (hx : x ∈ Ω) : HasFDerivAt (𝕜 := ℝ) f 0 x := by
      have d := eval_derivative (hD x hx) a b
      convert d.inner ℝ d using 1
      ext h
      have o := ort x hx h a b a b
      have rev := (real_inner_comm (K x a b) (fderiv ℝ K x h a b)).symm.trans o
      simp [o,rev]
    exact ho.is_const_of_fderiv_eq_zero hc
      (fun x hx ↦ (hf x hx).differentiableAt.differentiableWithinAt)
      (fun x hx ↦ (hf x hx).fderiv) hQ hP
  intro p hP
  ext z u v
  let w := fderiv ℝ K p z u v
  have kernel (b : H) : K p w b = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [(hs p hP).1 w b, (hs p hP).2]
    exact ort p hP z u v b _
  have allQ (b : H) (q : H) (hQ : q ∈ Ω) : K q w b = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [flat w b hP hQ, kernel, inner_zero_left]
  have derivZero (b : H) : fderiv ℝ K p z w b = 0 := by
    have eqn : (fun q ↦ K q w b) =ᶠ[𝓝 p] fun _ ↦ (0 : H) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ω,ho.mem_nhds hP,fun x hx ↦ allQ b x hx⟩
    have d := (eval_derivative (hD p hP) w b).fderiv
    rw [eqn.fderiv_eq, (hasFDerivAt_const (𝕜 := ℝ) (0 : H) p).fderiv] at d
    exact (congrArg (fun L : H →L[ℝ] H ↦ L z) d).symm
  change w = 0
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  change form (fderiv ℝ K p) z u v w = 0
  rw [(hS p hP).last z u v w, (hS p hP).middle z u w v]
  simp [form,derivZero]

theorem constant_of_longitudinal (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (hD : ∀ p ∈ Ω, DifferentiableAt ℝ K p)
    (hs : ∀ p ∈ Ω, SymmetricProduct (K p)) (hm : ∀ p ∈ Ω, Commutes (K p))
    (hS : ∀ p ∈ Ω, SymmetricJet (fderiv ℝ K p))
    (hp : ∀ p ∈ Ω, ∀ h, form (fderiv ℝ K p) h h h (K p h h) = 0)
    {p q : H} (hP : p ∈ Ω) (hQ : q ∈ Ω) : K q = K p :=
  ho.is_const_of_fderiv_eq_zero (𝕜 := ℝ) hc (fun x hx ↦ (hD x hx).differentiableWithinAt)
    (fun x hx ↦ parallel_of_longitudinal ho hc hD hs hm hS hp x hx) hQ hP

end FisherMidpoint
