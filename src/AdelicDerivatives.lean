import AdelicTheta
import IdeleOneParameter
import OneParameterFlows
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Filter IsDedekindDomain NumberField Set Topology
open scoped NumberField SchwartzMap Pointwise Classical

namespace Masullo

noncomputable section

section SchwartzLinearField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def realSchwartzLinearField (A : E →L[ℝ] E) : 𝓢(E, ℂ) →L[ℝ] 𝓢(E, ℂ) :=
  (SchwartzMap.bilinLeftCLM ((ContinuousLinearMap.apply ℝ ℂ).flip) A.hasTemperateGrowth).comp
    (SchwartzMap.fderivCLM ℝ E ℂ)

private theorem realSchwartzLinearField_apply (A : E →L[ℝ] E) (f : 𝓢(E, ℂ)) (x : E) :
    realSchwartzLinearField A f x = fderiv ℝ f x (A x) := rfl

/-- Differentiation against a real-linear vector field preserves Schwartz
space, and is continuous and complex-linear in the Schwartz function. -/
def schwartzLinearField (A : E →L[ℝ] E) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) where
  toFun := realSchwartzLinearField A
  map_add' := (realSchwartzLinearField A).map_add
  map_smul' c f := by
    ext x
    rw [RingHom.id_apply, smul_apply, realSchwartzLinearField_apply,
      realSchwartzLinearField_apply]
    change (fderiv ℝ (c • (f : E → ℂ)) x) (A x) = c • fderiv ℝ f x (A x)
    rw [fderiv_const_smul f.differentiableAt]
    rfl
  cont := (realSchwartzLinearField A).continuous

@[simp] theorem schwartzLinearField_apply (A : E →L[ℝ] E) (f : 𝓢(E, ℂ)) (x : E) :
    schwartzLinearField A f x = fderiv ℝ f x (A x) := rfl

end SchwartzLinearField

variable (F : Type*) [Field F] [NumberField F]

private abbrev Arch := mixedEmbedding.mixedSpace F

/-- Infinite coordinates of an idelic one-parameter subgroup, with logarithmic parameter. -/
def mixedIdeleFlow (γ : Multiplicative ℝ →* Idele F) (t : ℝ) : Arch F :=
  InfiniteAdeleRing.ringEquiv_mixedSpace F (γ (Multiplicative.ofAdd t)).val.1

@[simp] theorem mixedIdeleFlow_zero (γ : Multiplicative ℝ →* Idele F) :
    mixedIdeleFlow F γ 0 = 1 := by
  change InfiniteAdeleRing.ringEquiv_mixedSpace F (γ 1).val.1 = 1
  rw [map_one]
  exact map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem mixedIdeleFlow_continuous (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ) :
    Continuous (mixedIdeleFlow F γ) :=
  (infiniteAdele_toMixed_continuous F).comp
    (continuous_fst.comp ((Units.continuous_val.comp hγ).comp continuous_ofAdd))

private def mixedIdeleHom (γ : Multiplicative ℝ →* Idele F) :
    Multiplicative ℝ →* (Arch F)ˣ :=
  (Units.map ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).toMonoidHom).comp γ

theorem mixedIdeleFlow_hasDerivAt (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ) :
    ∃ c : Arch F, HasDerivAt (mixedIdeleFlow F γ) c 0 := by
  classical
  have hC := mixedIdeleFlow_continuous F γ hγ
  let γR (v : {w : InfinitePlace F // w.IsReal}) :=
    (Units.map ((Pi.evalRingHom (fun _ : {w : InfinitePlace F // w.IsReal} => ℝ) v).comp
      (RingHom.fst _ _)).toMonoidHom).comp (mixedIdeleHom F γ)
  let γC (v : {w : InfinitePlace F // w.IsComplex}) :=
    (Units.map ((Pi.evalRingHom (fun _ : {w : InfinitePlace F // w.IsComplex} => ℂ) v).comp
      (RingHom.snd _ _)).toMonoidHom).comp (mixedIdeleHom F γ)
  have hr (v : {w : InfinitePlace F // w.IsReal}) :
      ∃ c : ℝ, HasDerivAt (fun t => (mixedIdeleFlow F γ t).1 v) c 0 := by
    have hcont : Continuous (fun t : ℝ => ((γR v (Multiplicative.ofAdd t) : ℝˣ) : ℝ)) :=
      ((continuous_apply v).comp continuous_fst).comp hC
    obtain ⟨-, c, hc⟩ := continuous_oneParameter_smooth (γR v) hcont
    exact ⟨_, hc 0⟩
  have hc (v : {w : InfinitePlace F // w.IsComplex}) :
      ∃ c : ℂ, HasDerivAt (fun t => (mixedIdeleFlow F γ t).2 v) c 0 := by
    have hcont : Continuous (fun t : ℝ => ((γC v (Multiplicative.ofAdd t) : ℂˣ) : ℂ)) :=
      ((continuous_apply v).comp continuous_snd).comp hC
    obtain ⟨-, c, hc⟩ := continuous_oneParameter_smooth (γC v) hcont
    exact ⟨_, hc 0⟩
  choose cr hr using hr
  choose cc hc using hc
  exact ⟨(cr, cc), (hasDerivAt_pi.mpr hr).prodMk (hasDerivAt_pi.mpr hc)⟩

/-- Velocities along the logarithmic flow are translates of the velocity at the identity. -/
theorem mixedIdeleFlow_log_hasDerivAt (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (r : ℝ) :
    HasDerivAt (mixedIdeleFlow F γ)
      (deriv (mixedIdeleFlow F γ) 0 * mixedIdeleFlow F γ r) r := by
  obtain ⟨c, hc⟩ := mixedIdeleFlow_hasDerivAt F γ hγ
  have h₀ : HasDerivAt (mixedIdeleFlow F γ) c (r - r) := by simpa only [sub_self] using hc
  have h := (h₀.comp_sub_const r r).mul_const (mixedIdeleFlow F γ r)
  have he (t : ℝ) :
      mixedIdeleFlow F γ (t - r) * mixedIdeleFlow F γ r = mixedIdeleFlow F γ t := by
    let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
    change m ((γ (Multiplicative.ofAdd (t - r))).val.1) *
      m ((γ (Multiplicative.ofAdd r)).val.1) = m ((γ (Multiplicative.ofAdd t)).val.1)
    rw [← m.map_mul]
    change m ((γ (Multiplicative.ofAdd (t - r)) * γ (Multiplicative.ofAdd r)).val.1) = _
    rw [← map_mul]
    change m ((γ (Multiplicative.ofAdd ((t - r) + r))).val.1) = _
    rw [sub_add_cancel]
  simpa only [he, hc.deriv] using h

/-- The archimedean vector field of an idelic flow is multiplication by
the velocity at the identity. -/
def mixedIdeleVectorField (γ : Multiplicative ℝ →* Idele F) : Arch F →L[ℝ] Arch F :=
  ContinuousLinearMap.mul ℝ (Arch F) (deriv (mixedIdeleFlow F γ) 0)

private theorem mixedIdele_orbit_hasDerivAt (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (x : Arch F) :
    HasDerivAt (fun t : ℝ => mixedIdeleFlow F γ (Real.log t) * x) (mixedIdeleVectorField F γ x) 1 := by
  obtain ⟨c, hc⟩ := mixedIdeleFlow_hasDerivAt F γ hγ
  have hlog : HasDerivAt Real.log 1 1 := by simpa using Real.hasDerivAt_log (one_ne_zero (α := ℝ))
  have h0 : HasDerivAt (fun t => mixedIdeleFlow F γ t * x) (c * x) (Real.log 1) := by
    simpa only [Real.log_one] using hc.mul_const x
  have h := h0.scomp 1 hlog
  simpa only [mixedIdeleVectorField, hc.deriv, ContinuousLinearMap.mul_apply', one_smul, Function.comp_def] using h


/-- Logarithmic coordinates identify the manuscript's positive-parameter
action with an action defined on an open neighborhood of 1 in ℝ. -/
def positiveParameterOrbit (γ : Multiplicative ℝ →* Idele F) (a : Adeles F) (t : ℝ) : Adeles F :=
  (γ (Multiplicative.ofAdd (Real.log t))).val * a

private theorem bruhatTensor_hasDerivAt (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (φ : 𝓢(Arch F, ℂ)) (ψ : FiniteBruhat F) (a : Adeles F) :
    HasDerivAt (fun t => bruhatTensor F φ ψ (positiveParameterOrbit F γ a t))
      (bruhatTensor F (schwartzLinearField (mixedIdeleVectorField F γ) φ) ψ a) 1 := by
  let x := InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
  let p := fun t : ℝ => mixedIdeleFlow F γ (Real.log t) * x
  have hp : HasDerivAt p (mixedIdeleVectorField F γ x) 1 :=
    mixedIdele_orbit_hasDerivAt F γ hγ x
  have hp₁ : p 1 = x := by simp [p]
  have hd := (φ.hasFDerivAt (p 1)).comp_hasDerivAt 1 hp
  have hh := hd.mul_const (ψ.toLocallyConstant a.2)
  have he (t : ℝ) :
      bruhatTensor F φ ψ (positiveParameterOrbit F γ a t) =
        φ (p t) * ψ.toLocallyConstant a.2 := by
    let g := γ (Multiplicative.ofAdd (Real.log t))
    have hfin := finite_component_eq_one_of_mem_infinitePlaceIdeles F
      ((idele_oneParameter_structure F γ hγ).1 (Multiplicative.ofAdd (Real.log t)))
    change φ (InfiniteAdeleRing.ringEquiv_mixedSpace F (g.val.1 * a.1)) *
      ψ.toLocallyConstant (g.val.2 * a.2) = _
    rw [map_mul, hfin, one_mul]
    rfl
  simp only [hp₁] at hh
  change HasDerivAt (fun t => bruhatTensor F φ ψ (positiveParameterOrbit F γ a t))
    (fderiv ℝ φ x (mixedIdeleVectorField F γ x) * ψ.toLocallyConstant a.2) 1
  exact (funext he).symm ▸ hh

private theorem bruhat_hasDerivAt (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    {f : Adeles F → ℂ} (hf : f ∈ bruhatSubmodule F) :
    ∃ g ∈ bruhatSubmodule F, ∀ a : Adeles F,
      HasDerivAt (fun t => f (positiveParameterOrbit F γ a t)) (g a) 1 := by
  apply Submodule.span_induction (p := fun f _ => ∃ g ∈ bruhatSubmodule F, ∀ a : Adeles F,
    HasDerivAt (fun t => f (positiveParameterOrbit F γ a t)) (g a) 1) _ _ _ _ hf
  · rintro _ ⟨φ, ψ, rfl⟩
    let G := schwartzLinearField (mixedIdeleVectorField F γ) φ
    exact ⟨bruhatTensor F G ψ, bruhatTensor_mem F G ψ, bruhatTensor_hasDerivAt F γ hγ φ ψ⟩
  · exact ⟨0, Submodule.zero_mem _, fun _ => hasDerivAt_const _ _⟩
  · rintro f g _ _ ⟨f', hf', hf⟩ ⟨g', hg', hg⟩
    exact ⟨f' + g', Submodule.add_mem _ hf' hg', fun a => (hf a).add (hg a)⟩
  · rintro c f _ ⟨f', hf', hf⟩
    exact ⟨c • f', Submodule.smul_mem _ c hf', fun a => (hf a).const_smul c⟩

/-- The pointwise directional derivative maps the algebraic adelic
Schwartz–Bruhat space back into itself. -/
def algebraicBruhatDeriv (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ) :
    bruhatSubmodule F →ₗ[ℂ] bruhatSubmodule F where
  toFun f :=
    ⟨fun a => deriv (fun t => f.val (positiveParameterOrbit F γ a t)) 1, by
      obtain ⟨g, hg, he⟩ := bruhat_hasDerivAt F γ hγ f.property
      exact (funext fun a => (he a).deriv).symm ▸ hg⟩
  map_add' f g := by
    obtain ⟨_, _, hf⟩ := bruhat_hasDerivAt F γ hγ f.property
    obtain ⟨_, _, hg⟩ := bruhat_hasDerivAt F γ hγ g.property
    apply Subtype.ext
    funext a
    change deriv (fun t => f.val (positiveParameterOrbit F γ a t) +
      g.val (positiveParameterOrbit F γ a t)) 1 =
        deriv (fun t => f.val (positiveParameterOrbit F γ a t)) 1 +
          deriv (fun t => g.val (positiveParameterOrbit F γ a t)) 1
    rw [(hf a).deriv, (hg a).deriv]
    exact ((hf a).add (hg a)).deriv
  map_smul' c f := by
    obtain ⟨_, _, hf⟩ := bruhat_hasDerivAt F γ hγ f.property
    apply Subtype.ext
    funext a
    change deriv (fun t => c • f.val (positiveParameterOrbit F γ a t)) 1 =
      c • deriv (fun t => f.val (positiveParameterOrbit F γ a t)) 1
    rw [(hf a).deriv]
    exact ((hf a).const_smul c).deriv

theorem algebraicBruhatDeriv_hasDerivAt (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (f : bruhatSubmodule F) (a : Adeles F) :
    HasDerivAt (fun t => f.val (positiveParameterOrbit F γ a t))
      ((algebraicBruhatDeriv F γ hγ f).val a) 1 := by
  obtain ⟨_, _, hg⟩ := bruhat_hasDerivAt F γ hγ f.property
  change HasDerivAt _ (deriv (fun t => f.val (positiveParameterOrbit F γ a t)) 1) 1
  rw [(hg a).deriv]
  exact hg a


/-- The algebraic adelic Schwartz–Bruhat space with its final locally convex
topology generated by the Archimedean Schwartz slices. -/
def GlobalBruhat := bruhatSubmodule F

namespace GlobalBruhat

instance : AddCommGroup (GlobalBruhat F) := inferInstanceAs (AddCommGroup (bruhatSubmodule F))

instance : Module ℂ (GlobalBruhat F) := inferInstanceAs (Module ℂ (bruhatSubmodule F))

instance : Module ℝ (GlobalBruhat F) := inferInstanceAs (Module ℝ (bruhatSubmodule F))

instance : IsScalarTower ℝ ℂ (GlobalBruhat F) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (bruhatSubmodule F))

def algebraicEquiv : GlobalBruhat F ≃ₗ[ℂ] bruhatSubmodule F := LinearEquiv.refl ℂ _

def pure (ψ : FiniteBruhat F) : 𝓢(Arch F, ℂ) →ₗ[ℂ] GlobalBruhat F where
  toFun φ := (algebraicEquiv F).symm ⟨bruhatTensor F φ ψ, bruhatTensor_mem F φ ψ⟩
  map_add' φ ξ := by
    apply (algebraicEquiv F).injective
    ext a
    simp [bruhatTensor, add_mul]
  map_smul' c φ := by
    apply (algebraicEquiv F).injective
    ext a
    simp [bruhatTensor, smul_eq_mul, mul_assoc]

def evaluation (a : Adeles F) : GlobalBruhat F →ₗ[ℂ] ℂ where
  toFun f := (algebraicEquiv F f).val a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def Admissible := {p : Seminorm ℂ (GlobalBruhat F) //
  ∀ ψ : FiniteBruhat F, Continuous (fun φ => p (pure F ψ φ))}

private def seminormFamily : SeminormFamily ℂ (GlobalBruhat F) (Admissible F) := Subtype.val

instance : TopologicalSpace (GlobalBruhat F) := (seminormFamily F).moduleFilterBasis.topology

private theorem withSeminorms : WithSeminorms (seminormFamily F) := ⟨rfl⟩

instance : IsTopologicalAddGroup (GlobalBruhat F) := (withSeminorms F).topologicalAddGroup

instance : ContinuousSMul ℂ (GlobalBruhat F) := (withSeminorms F).continuousSMul
instance : PolynormableSpace ℂ (GlobalBruhat F) := (withSeminorms F).toPolynormableSpace

instance : LocallyConvexSpace ℝ (GlobalBruhat F) := (withSeminorms F).toLocallyConvexSpace

theorem pure_continuous (ψ : FiniteBruhat F) : Continuous (pure F ψ) :=
  WithSeminorms.continuous_of_continuous_comp (withSeminorms F) (pure F ψ)
    (fun p => p.property ψ)

theorem continuous_seminorm_of_pure (p : Seminorm ℂ (GlobalBruhat F))
    (hp : ∀ ψ, Continuous (fun φ => p (pure F ψ φ))) : Continuous p :=
  (withSeminorms F).continuous_seminorm ⟨p, hp⟩

/-- The final topology can be tested on the Schwartz slices for each
fixed finite-place input. -/
theorem continuous_of_pure {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {ι : Type*} {q : SeminormFamily ℂ E ι} (hE : WithSeminorms q)
    (f : GlobalBruhat F →ₗ[ℂ] E) (hf : ∀ ψ, Continuous (fun φ => f (pure F ψ φ))) :
    Continuous f := by
  apply WithSeminorms.continuous_of_continuous_comp hE f
  intro i
  exact continuous_seminorm_of_pure F ((q i).comp f)
    (fun ψ => (hE.continuous_seminorm i).comp (hf ψ))

theorem evaluation_continuous (a : Adeles F) : Continuous (evaluation F a) := by
  apply continuous_of_pure F (norm_withSeminorms ℂ ℂ)
  intro ψ
  change Continuous (fun φ : 𝓢(Arch F, ℂ) => bruhatTensor F φ ψ a)
  let x := InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
  have h : Continuous (fun φ : 𝓢(Arch F, ℂ) => φ x) :=
    ((BoundedContinuousFunction.lipschitz_eval_const x).continuous).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Arch F) ℂ).continuous
  exact h.mul continuous_const

instance : T2Space (GlobalBruhat F) := T2Space.of_injective_continuous
  (f := fun f a => evaluation F a f)
  (fun _ _ h => (algebraicEquiv F).injective (Subtype.ext h))
  (continuous_pi (evaluation_continuous F))

/-- The directional derivative on the adelic test space as a complex-linear map. -/
def derivativeLinear (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ) :
    GlobalBruhat F →ₗ[ℂ] GlobalBruhat F :=
  (algebraicEquiv F).symm.toLinearMap.comp
    ((algebraicBruhatDeriv F γ hγ).comp (algebraicEquiv F).toLinearMap)

theorem derivativeLinear_pure (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (ψ : FiniteBruhat F) (φ : 𝓢(Arch F, ℂ)) :
    derivativeLinear F γ hγ (pure F ψ φ) =
      pure F ψ (schwartzLinearField (mixedIdeleVectorField F γ) φ) := by
  apply (algebraicEquiv F).injective
  apply Subtype.ext
  funext a
  exact (bruhatTensor_hasDerivAt F γ hγ φ ψ a).deriv

/-- Lemma 2.2.4.2 in the final locally convex Schwartz-slice topology. -/
def derivative (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ) :
    GlobalBruhat F →L[ℂ] GlobalBruhat F where
  toLinearMap := derivativeLinear F γ hγ
  cont := by
    apply continuous_of_pure F (withSeminorms F)
    intro ψ
    simp_rw [derivativeLinear_pure]
    exact (pure_continuous F ψ).comp (schwartzLinearField _).continuous

theorem derivative_is_pointwise (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (f : GlobalBruhat F) (a : Adeles F) :
    Tendsto (fun t : ℝ => (t - 1)⁻¹ •
      (evaluation F (positiveParameterOrbit F γ a t) f - evaluation F a f))
      (𝓝[≠] (1 : ℝ)) (𝓝 (evaluation F a (derivative F γ hγ f))) := by
  have h := (algebraicBruhatDeriv_hasDerivAt F γ hγ (algebraicEquiv F f) a).tendsto_slope
  have h₁ : positiveParameterOrbit F γ a 1 = a := by
    simp [positiveParameterOrbit]
  have hD : (algebraicEquiv F) (derivative F γ hγ f) = algebraicBruhatDeriv F γ hγ (algebraicEquiv F f) :=
    (algebraicEquiv F).apply_symm_apply _
  change Tendsto (fun t : ℝ => (t - 1)⁻¹ • ((algebraicEquiv F f).val
    (positiveParameterOrbit F γ a t) - (algebraicEquiv F f).val a))
    (𝓝[≠] 1) (𝓝 ((algebraicEquiv F (derivative F γ hγ f)).val a))
  rw [hD]
  convert h using 1
  funext t
  simp only [slope_def_module, h₁]

end GlobalBruhat

end

end Masullo
