import ArchimedeanProductZeta

open Filter MeasureTheory NumberField Set Topology
open scoped Classical ContDiff SchwartzMap NumberField

namespace Masullo

noncomputable section

/-- A radial Schwartz profile has an entire Taylor-subtracted Mellin
transform exactly when every derivative at zero vanishes. -/
theorem mellinTaylorContinued_entire_iff_flat (f : 𝓢(ℝ, ℂ)) :
    (∀ z : ℂ, AnalyticAt ℂ (mellinTaylorContinued f) z) ↔
      ∀ n : ℕ, iteratedDeriv n f 0 = 0 := by
  have hcoeff (n : ℕ) :
      mellinTaylorCoeff f.toFun n = 0 ↔ iteratedDeriv n f 0 = 0 := by
    change mellinTaylorCoeff f.toFun n = 0 ↔ iteratedDeriv n f.toFun 0 = 0
    have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    simp [mellinTaylorCoeff, hn]
  constructor
  · intro h n
    apply (hcoeff n).mp
    by_contra hne
    have hp := mellinTaylorContinued_order f.smooth' (schwartz_radial_rapid f) n
    rw [ite_eq_right hne] at hp
    have hpos : 0 ≤ meromorphicOrderAt (mellinTaylorContinued f.toFun) (-(n : ℂ)) :=
      (h (-(n : ℂ))).meromorphicOrderAt_nonneg
    rw [hp] at hpos
    change ((0 : ℤ) : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ) at hpos
    exact (show ¬ (0 : ℤ) ≤ -1 by norm_num) (WithTop.coe_le_coe.mp hpos)
  · intro hf z
    by_cases hz : ∀ k : ℕ, z + k ≠ 0
    · exact mellinTaylorContinued_analyticAt f.smooth' (schwartz_radial_rapid f) hz
    · push Not at hz
      obtain ⟨k, hk⟩ := hz
      have hp := mellinTaylorContinued_order f.smooth' (schwartz_radial_rapid f) k
      rw [ite_eq_left ((hcoeff k).mpr (hf k))] at hp
      rw [eq_neg_of_add_eq_zero_left hk]
      exact hp

/-- Sign folding projects onto the parity seen by the real-place Mellin
integral. The projected test represents the same continuation. -/
theorem realZetaProfile_normalized_rep (a : ℕ) (f : 𝓢(ℝ, ℂ)) :
    realArchimedeanZetaContinued a ((2 : ℂ)⁻¹ • realZetaProfile a f) =
      realArchimedeanZetaContinued a f := by
  have h : realZetaProfile a ((2 : ℂ)⁻¹ • realZetaProfile a f) = realZetaProfile a f := by
    ext t
    simp only [realZetaProfile_apply, smul_apply, smul_eq_mul, neg_neg]
    have hphase : ((-1 : ℂ) ^ a)^2 = 1 := by rw [← pow_mul, mul_comm a, pow_mul, neg_one_sq, one_pow]
    linear_combination ((2 : ℂ)⁻¹ * f t) * hphase
  funext z
  change mellinTaylorContinued (realZetaProfile a ((2 : ℂ)⁻¹ • realZetaProfile a f)) z =
    mellinTaylorContinued (realZetaProfile a f) z
  rw [h]

/-- A real local component with entire Mellin transform has a flat
Schwartz representative, given by the normalized sign projection. -/
theorem realArchimedeanZeta_entire_iff_exists_flat (a : ℕ) (f : 𝓢(ℝ, ℂ)) :
    (∀ z : ℂ, AnalyticAt ℂ (realArchimedeanZetaContinued a f) z) ↔
      ∃ g : 𝓢(ℝ, ℂ), (∀ n : ℕ, iteratedDeriv n g 0 = 0) ∧
        realArchimedeanZetaContinued a g = realArchimedeanZetaContinued a f := by
  constructor
  · intro hf
    have hzero := (mellinTaylorContinued_entire_iff_flat (realZetaProfile a f)).mp hf
    refine ⟨(2 : ℂ)⁻¹ • realZetaProfile a f, fun n ↦ ?_, realZetaProfile_normalized_rep a f⟩
    change iteratedDeriv n (fun t ↦ (2 : ℂ)⁻¹ • realZetaProfile a f t) 0 = 0
    rw [iteratedDeriv_fun_const_smul_field, hzero n, smul_zero]
  · rintro ⟨g, hg, he⟩
    rw [← he]
    apply (mellinTaylorContinued_entire_iff_flat (realZetaProfile a g)).mpr
    intro n
    have h : mellinTaylorCoeff (realZetaProfile a g) n = 0 := by
      rw [realZetaProfile_taylorCoeff, hg n, mul_zero, mul_zero]
    have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    simpa [mellinTaylorCoeff, hn] using h

attribute [local instance] complexZeta_circleMeasurable

/-- Flatness at the origin also removes every pole of the complex local
Mellin transform, for any angular mode. -/
theorem complexArchimedeanZeta_entire_of_flat (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℤ) (f : 𝓢(ℂ, ℂ)) (hf : ∀ n : ℕ, iteratedFDeriv ℝ n f 0 = 0) :
    ∀ z : ℂ, AnalyticAt ℂ (complexArchimedeanZetaContinued ν m f) z := by
  let r := complexZetaRadialSchwartz ν m f
  have h0 (n : ℕ) : iteratedDeriv n r 0 = 0 := by
    change iteratedDeriv n (complexZetaProfile ν m f) 0 = 0
    rw [complexZetaProfile_iteratedDeriv]
    change (∫ u : Circle, (u : ℂ)^m *
      iteratedFDeriv ℝ n f ((0 : ℝ) • (u : ℂ)) (fun _ ↦ (u : ℂ)) ∂ν) = 0
    simp only [zero_smul, hf, zero_apply, mul_zero, integral_zero]
  have he := (mellinTaylorContinued_entire_iff_flat r).mpr h0
  intro z
  exact (he (2*z)).comp (f := fun w : ℂ ↦ 2*w) (analyticAt_const.mul analyticAt_id)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def schwartzJetEvaluation (n : ℕ) (x : E) :
    𝓢(E, ℂ) →L[ℂ] ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (fun f ↦ iteratedFDeriv ℝ n f x)
    (fun f g ↦ iteratedFDeriv_add_apply (f.smooth n).contDiffAt (g.smooth n).contDiffAt)
    (fun c f ↦ iteratedFDeriv_const_smul_apply (a := c) (f.smooth n).contDiffAt)
    ⟨{(0, n)}, 1, zero_le_one, fun f ↦ by
      simpa only [one_mul, Finset.sup_singleton, schwartzSeminormFamily] using
        SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f n x⟩

/-- Schwartz functions whose Fréchet derivatives of all orders vanish
on a specified subset. The condition includes the value of the function. -/
def schwartzFlatSubspace (A : Set E) : Submodule ℂ 𝓢(E, ℂ) :=
  ⨅ j : A × ℕ, (schwartzJetEvaluation j.2 j.1.val).ker

@[simp] theorem mem_schwartzFlatSubspace (A : Set E) (f : 𝓢(E, ℂ)) :
    f ∈ schwartzFlatSubspace A ↔ ∀ x ∈ A, ∀ n : ℕ, iteratedFDeriv ℝ n f x = 0 := by
  rw [schwartzFlatSubspace, Submodule.mem_iInf]
  exact ⟨fun h x hx n ↦ h (⟨x, hx⟩, n), fun h j ↦ h j.1.val j.1.property j.2⟩

theorem schwartzFlatSubspace_isClosed (A : Set E) :
    IsClosed (schwartzFlatSubspace A : Set 𝓢(E, ℂ)) := by
  classical
  rw [schwartzFlatSubspace, Submodule.coe_iInf]
  exact isClosed_iInter fun j ↦ (schwartzJetEvaluation j.2 j.1.val).isClosed_ker

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Pullback preserves flatness whenever the continuous linear
equivalence sends the new vanishing locus into the old one. -/
theorem schwartzFlatSubspace_compCLM {A : Set E} {B : Set D}
    (e : D ≃L[ℝ] E) (he : MapsTo e B A) {f : 𝓢(E, ℂ)} (hf : f ∈ schwartzFlatSubspace A) :
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f ∈ schwartzFlatSubspace B := by
  apply (mem_schwartzFlatSubspace _ _).mpr
  intro x hx n
  have h0 := (mem_schwartzFlatSubspace _ _).mp hf (e x) (he hx) n
  change iteratedFDeriv ℝ n (f.toFun ∘ e.toContinuousLinearMap) x = 0
  rw [e.toContinuousLinearMap.iteratedFDeriv_comp_right f.smooth' x
    (by exact_mod_cast le_top : (n : ℕ∞ω) ≤ ∞)]
  change (iteratedFDeriv ℝ n f (e x)).compContinuousLinearMap _ = 0
  rw [h0]
  ext v
  simp

/-- A coordinate slice of a test flat at the point on the zero
hyperplane is flat at its own origin. -/
theorem archimedeanSlice_flat_of_flat
    (f : 𝓢(E × D, ℂ)) (y : D)
    (hf : ∀ n : ℕ, iteratedFDeriv ℝ n f (0, y) = 0) :
    ∀ n : ℕ, iteratedFDeriv ℝ n (archimedeanSlice y f) 0 = 0 := by
  intro n
  let L := ContinuousLinearMap.inl ℝ E D
  let g (x : E × D) := f (x + (0, y))
  have hg : ContDiff ℝ ∞ g := f.smooth'.comp (contDiff_id.add contDiff_const)
  have he : (archimedeanSlice y f : E → ℂ) = g ∘ L := by
    funext x
    simp [archimedeanSlice_apply, g, L]
  rw [he, L.iteratedFDeriv_comp_right hg 0 (by exact_mod_cast le_top : (n : ℕ∞ω) ≤ ∞),
    map_zero]
  have h0 : iteratedFDeriv ℝ n g 0 = 0 := by
    change iteratedFDeriv ℝ n (fun x : E × D ↦ f (x + (0, y))) 0 = 0
    simpa only [iteratedFDeriv_comp_add_right, zero_add] using hf n
  rw [h0]
  ext v
  simp

variable (F : Type*) [Field F] [NumberField F]

/-- The closed archimedean flat-test space of (5.3.3.10), on the actual
mixed space of a number field. -/
def archimedeanFlatTestSubspace : Submodule ℂ 𝓢(mixedEmbedding.mixedSpace F, ℂ) :=
  schwartzFlatSubspace {x | (∃ v : {v : InfinitePlace F // v.IsReal}, x.1 v = 0) ∨
    ∃ v : {v : InfinitePlace F // v.IsComplex}, x.2 v = 0}

theorem archimedeanFlatTestSubspace_isClosed :
    IsClosed (archimedeanFlatTestSubspace F : Set 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :=
  schwartzFlatSubspace_isClosed _

private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}

private theorem realRingEquiv_apply_eq (e : ℝ ≃+* ℝ) (he : Continuous e) (x : ℝ) :
    e x = x := by
  have h : Complex.ofRealHom.comp e.toRingHom = Complex.ofRealHom :=
    Complex.ringHom_eq_ofReal_of_continuous (Complex.continuous_ofReal.comp he)
  exact Complex.ofReal_injective (DFunLike.congr_fun h x)

private def realRingCoordinate (e : ℝ ≃+* ℝ) (he : Continuous e) : ℝ ≃L[ℝ] ℝ := by
  let l : ℝ ≃ₗ[ℝ] ℝ :=
    { e.toEquiv with
      map_add' := e.map_add
      map_smul' := fun r x ↦ by
        change e (r • x) = r • e x
        rw [realRingEquiv_apply_eq e he (r • x), realRingEquiv_apply_eq e he x] }
  exact l.toContinuousLinearEquiv

private def complexRingCoordinate (e : ℂ ≃+* ℂ) (he : Continuous e) : ℂ ≃L[ℝ] ℂ := by
  have h : e.toRingHom.comp Complex.ofRealHom = Complex.ofRealHom :=
    Complex.ringHom_eq_ofReal_of_continuous (he.comp Complex.continuous_ofReal)
  let l : ℂ ≃ₗ[ℝ] ℂ :=
    { e.toEquiv with
      map_add' := e.map_add
      map_smul' := fun r x ↦ by
        change e ((r : ℂ) * x) = (r : ℂ) * e x
        rw [map_mul, show e (r : ℂ) = (r : ℂ) from DFunLike.congr_fun h r] }
  exact l.toContinuousLinearEquiv

/-- The mixed coordinate change coming from arbitrary continuous field
automorphisms of the real and complex coordinate fields. -/
def archimedeanFlatCoordinateChange (r : R F → ℝ ≃+* ℝ) (j : C F → ℂ ≃+* ℂ)
    (hr : ∀ v, Continuous (r v)) (hj : ∀ v, Continuous (j v)) :
    mixedEmbedding.mixedSpace F ≃L[ℝ] mixedEmbedding.mixedSpace F :=
  (ContinuousLinearEquiv.piCongrRight (fun v ↦ realRingCoordinate (r v) (hr v))).prodCongr
    (ContinuousLinearEquiv.piCongrRight (fun v ↦ complexRingCoordinate (j v) (hj v)))

/-- The archimedean flat subspace is independent of continuous field
coordinate choices. -/
theorem archimedeanFlatTestSubspace_coordinateChange
    (r : R F → ℝ ≃+* ℝ) (j : C F → ℂ ≃+* ℂ)
    (hr : ∀ v, Continuous (r v)) (hj : ∀ v, Continuous (j v))
    (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archimedeanFlatCoordinateChange F r j hr hj) f ∈
      archimedeanFlatTestSubspace F ↔ f ∈ archimedeanFlatTestSubspace F := by
  let e := archimedeanFlatCoordinateChange F r j hr hj
  let H : Set (mixedEmbedding.mixedSpace F) := {x | (∃ v : R F, x.1 v = 0) ∨ ∃ v : C F, x.2 v = 0}
  have h (x : mixedEmbedding.mixedSpace F) : e x ∈ H ↔ x ∈ H := by
    change ((∃ v : R F, r v (x.1 v) = 0) ∨ ∃ v : C F, j v (x.2 v) = 0) ↔ _
    have hR (v : R F) : r v (x.1 v) = 0 ↔ x.1 v = 0 := map_eq_zero_iff _ (r v).injective
    have hC (v : C F) : j v (x.2 v) = 0 ↔ x.2 v = 0 := map_eq_zero_iff _ (j v).injective
    simp only [hR, hC]
    rfl
  change SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f ∈ schwartzFlatSubspace H ↔
    f ∈ schwartzFlatSubspace H
  refine ⟨fun hf ↦ ?_, schwartzFlatSubspace_compCLM e (fun _ hx ↦ (h _).mpr hx)⟩
  have hb : MapsTo e.symm H H := fun x hx ↦ (h (e.symm x)).mp (by simpa only [e.apply_symm_apply] using hx)
  have hg := schwartzFlatSubspace_compCLM e.symm hb hf
  have he : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) = f := by
    ext x
    simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, e.apply_symm_apply]
  rwa [he] at hg

end

end Masullo
