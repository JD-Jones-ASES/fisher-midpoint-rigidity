module
public import FisherMidpoint.Obstruction
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Constructing the dual cubic from the Fisher metric in coordinates -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology InnerProductSpace ContDiff
namespace FisherMidpoint
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def connection (F : H → H) (p : H) : ProductTensor H :=
  ((ContinuousLinearMap.compL ℝ H H H) (jac F p).inverse).comp (fderiv ℝ (jac F) p)

theorem connection_affine {F : H → H} {p : H} (inv : (jac F p).IsInvertible) (u v : H) :
    fderiv ℝ (jac F) p u v = jac F p (connection F p u v) :=
  (inv.self_apply_inverse _).symm

theorem connection_smooth [CompleteSpace H] {F : H → H} {p : H} (hf : ContDiffAt ℝ 4 F p)
    (inv : (jac F p).IsInvertible) : ContDiffAt ℝ 2 (connection F) p := by
  have h3 : ContDiffAt ℝ 3 (jac F) p := hf.fderiv_right (by decide)
  have hinv := (inv.contDiffAt_map_inverse (𝕜 := ℝ) (n := 2)).comp p (h3.of_le (by decide))
  exact ((ContinuousLinearMap.compL ℝ H H H).contDiff.contDiffAt.comp p hinv).clm_comp
    (h3.fderiv_right (by decide))

private theorem conn_sym {F : H → H} {p : H} (hf : ContDiffAt ℝ 4 F p) (u v : H) :
    connection F p u v = connection F p v u := by
  change (jac F p).inverse (fderiv ℝ (jac F) p u v) = _
  rw [hf.isSymmSndFDerivAt (by norm_num) u v]; rfl

theorem chart_products {Ω : Set H} {F G : H → H} (ho : IsOpen Ω) (A : FisherChart Ω F G)
    {p : H} (hp : p ∈ Ω) :
    SymmetricProduct (connection F p) ∧ connection G p = -connection F p := by
  let J := connection F p
  let M := connection G p
  have dual (a b c : H) : ⟪M a b,c⟫_ℝ + ⟪b,J a c⟫_ℝ = 0 := by
    have hDer (f : H → H) (hd : ContDiffAt ℝ 4 f p) (w : H) :
        HasFDerivAt (fun x ↦ jac f x w) ((fderiv ℝ (jac f) p).flip w) p := by
      have h := ((hd.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)).hasFDerivAt
      convert h.clm_apply (hasFDerivAt_const w p) using 1
      ext; simp
    have z := (hDer G (A.expected p hp) b).inner ℝ (hDer F (A.natural p hp) c)
    have near : (fun x ↦ ⟪jac G x b,jac F x c⟫_ℝ) =ᶠ[𝓝 p] fun _ ↦ ⟪b,c⟫_ℝ :=
      by filter_upwards [ho.mem_nhds hp] with x hx; exact A.metric x hx b c
    have e := congrArg (fun L : H →L[ℝ] ℝ ↦ L a)
      (z.unique ((hasFDerivAt_const (𝕜 := ℝ) ⟪b,c⟫_ℝ p).congr_of_eventuallyEq near))
    simp only [ContinuousLinearMap.comp_apply,fderivInnerCLM_apply,ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.flip_apply,zero_apply] at e
    rw [connection_affine (A.naturalInv p hp), connection_affine (A.expectedInv p hp),
      A.metric p hp, A.metric p hp] at e
    linarith only [e]
  have symF := conn_sym (A.natural p hp)
  have symG := conn_sym (A.expected p hp)
  have swap (a b c : H) : ⟪b,J a c⟫_ℝ = ⟪a,J b c⟫_ℝ := by
    have u := dual a b c
    have v := dual b a c
    have s : M b a = M a b := symG b a
    rw [s] at v; linarith
  have adj (a b c : H) : ⟪J a b,c⟫_ℝ = ⟪b,J a c⟫_ℝ := by
    rw [real_inner_comm,swap a c b,show J c b=J b c from symF c b,swap b a c]
  refine ⟨⟨symF,adj⟩,?_⟩
  ext a b
  apply ext_inner_right ℝ
  intro c
  change ⟪M a b,c⟫_ℝ = ⟪-(J a b),c⟫_ℝ
  rw [inner_neg_left,adj]
  linarith only [dual a b c]

open EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d

/-- Both flat affine connections and the smooth symmetric cubic are obtained from the charts. -/
theorem chart_cubic {Ω : Set E} {F G : E → E} (ho : IsOpen Ω) (A : FisherChart Ω F G) :
    ∃ C : E → Cubic d, ContDiffOn ℝ 2 C Ω ∧ AffineFor Ω F (raw C) ∧ AffineFor Ω G (-(raw C)) := by
  let V := cubicSubspace d
  obtain ⟨proj,he⟩ := LinearMap.exists_leftInverse_of_injective (K := ℝ) (V := V) (V' := ProductTensor E) V.subtype V.ker_subtype
  let P : ProductTensor E →L[ℝ] Cubic d := proj.toContinuousLinearMap
  let C : E → Cubic d := P ∘ connection F
  have agree (x : E) (hx : x ∈ Ω) : raw C x = connection F x := by
    let v : V := ⟨connection F x,(chart_products ho A hx).1⟩
    have eqn := LinearMap.congr_fun he v
    exact congrArg Subtype.val eqn
  refine ⟨C,?_,?_,?_⟩
  · intro x hx
    have hP := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 2) («E» := ProductTensor E)
      (F := Cubic d) P).contDiffAt (x := connection F x)
    exact (hP.comp x (connection_smooth (A.natural x hx) (A.naturalInv x hx))).contDiffWithinAt
  · intro x hx a b; rw [agree x hx]; exact connection_affine (A.naturalInv x hx) a b
  · intro x hx a b
    rw [Pi.neg_apply,agree x hx,← (chart_products ho A hx).2]
    exact connection_affine (A.expectedInv x hx) a b

end FisherMidpoint
