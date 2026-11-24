import ModulatedExponentialInductive
import ElementaryRadialSchwartz
import BruhatStageEvaluation
import BruhatWholeQuotientStages
import ModulatedSobolevQuasiCharacters

open Function Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 1700000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ) {I J : Set ℝ}

/-- The continuity of a linear map on the decay space is checked by
continuous maps between individual whole-group stages. -/
private theorem decay_continuous_of_stageMaps
    (L : ModulatedExponentialInductive m I →ₗ[ℂ] ModulatedExponentialInductive m J)
    (hL : ∀ p : WholeBruhatStage G, ∃ (q : WholeBruhatStage G)
      (U : WholeBruhatDecayStage m I p → WholeBruhatDecayStage m J q), Continuous U ∧
      ∀ f, (L (ModulatedExponentialInductive.stageMap p f)).val = (U f).val) :
    Continuous L := by
  apply (locallyConvexFinal_continuous_iff
    (fun p : WholeBruhatStage G ↦ ModulatedExponentialInductive.stageMap (m := m) (I := I) p)
    L).mpr
  intro p
  obtain ⟨q,U,hU,hval⟩ := hL p
  refine ((ModulatedExponentialInductive.stageMap_continuous q).comp hU).congr fun f ↦ ?_
  apply ModulatedExponentialInductive.algebraicEquiv.injective
  exact Subtype.ext (hval f).symm

private def decayShiftMap (c : ℝ) (h : ∀ b ∈ J, b + c ∈ I) :
    ModulatedExponentialInductive m I →L[ℂ] ModulatedExponentialInductive m J := by
  let W := modulatedExponentialWeight m c
  let L₀ := (W.comp ((modulatedExponentialDecaySubmodule m I).subtype.comp
    ModulatedExponentialInductive.algebraicEquiv.toLinearMap)).codRestrict
    (modulatedExponentialDecaySubmodule m J) (fun f ↦ (Submodule.mem_iInf _).mpr fun b ↦ by
      change modulatedExponentialWeight m b (modulatedExponentialWeight m c f.val) ∈
        bruhatSchwartzSubmodule
      rw [modulatedExponentialWeight_add]
      exact (modulatedExponentialDecay_twist m I ⟨b + c, h b b.property⟩
        (ModulatedExponentialInductive.algebraicEquiv f)).property)
  let L := ModulatedExponentialInductive.algebraicEquiv.symm.toLinearMap.comp L₀
  refine ⟨L, decay_continuous_of_stageMaps m L fun p ↦ ?_⟩
  let a (b : J) : I := ⟨b + c, h b b.property⟩
  let U (f : WholeBruhatDecayStage m I p) : WholeBruhatDecayStage m J p :=
    WholeBruhatDecayStage.algebraicEquiv.symm ⟨W f.val, (Submodule.mem_iInf _).mpr fun b ↦ by
      change modulatedExponentialWeight m b (modulatedExponentialWeight m c f.val) ∈ p.val.realize.range
      rw [modulatedExponentialWeight_add]
      exact f.property (a b)⟩
  refine ⟨p, U, (WholeBruhatDecayStage.continuous_iff U).mpr fun b ↦ ?_, fun _ ↦ rfl⟩
  have he : WholeBruhatDecayStage.twist p b ∘ U = WholeBruhatDecayStage.twist p (a b) := by
    funext f
    apply p.val.1.realizeSchwartz_injective p.val.2
    change p.val.realize (WholeBruhatDecayStage.twist p b (U f)) =
      p.val.realize (WholeBruhatDecayStage.twist p (a b) f)
    rw [WholeBruhatDecayStage.realize_twist, WholeBruhatDecayStage.realize_twist]
    exact modulatedExponentialWeight_add m b c f.val
  rw [he]
  exact ((WholeBruhatDecayStage.continuous_iff (id : WholeBruhatDecayStage m I p → _)).mp
    continuous_id) (a b)

/-- Remark D.3.3.6. Multiplication by the modulus to power `c` translates
the allowed abscissae by `-c` and is a homeomorphism for the inductive topology. -/
theorem modulatedDecay_shiftEquiv (c : ℝ) (hJ : J = (fun b : ℝ ↦ b - c) '' I) :
    ∃ e : ModulatedExponentialInductive m I ≃L[ℂ] ModulatedExponentialInductive m J,
      ∀ f, (e f).val = modulatedExponentialWeight m c f.val := by
  have h₁ (b : ℝ) (hb : b ∈ J) : b + c ∈ I := by
    rw [hJ] at hb
    obtain ⟨a,ha,rfl⟩ := hb
    simpa only [sub_add_cancel] using ha
  have h₂ (b : ℝ) (hb : b ∈ I) : b + -c ∈ J := by
    rw [hJ]
    exact ⟨b, hb, sub_eq_add_neg b c⟩
  let A := decayShiftMap m c h₁
  let B := decayShiftMap m (-c) h₂
  have hcancel (a b : ℝ) (hab : a + b = 0) (f : G → ℂ) :
      modulatedExponentialWeight m a (modulatedExponentialWeight m b f) = f := by
    rw [modulatedExponentialWeight_add, hab]
    funext x
    rw [modulatedExponentialWeight_apply, zero_mul, Real.exp_zero, one_smul]
  refine ⟨ContinuousLinearEquiv.equivOfInverse A B (fun f ↦ ?_) (fun f ↦ ?_), fun _ ↦ rfl⟩
  · exact ModulatedExponentialInductive.algebraicEquiv.injective
      (Subtype.ext (hcancel (-c) c (neg_add_cancel c) f.val))
  · exact ModulatedExponentialInductive.algebraicEquiv.injective
      (Subtype.ext (hcancel c (-c) (add_neg_cancel c) f.val))

set_option maxHeartbeats 6500000 in
private theorem exists_decayCharacter_stageMap (hm : IsProperMap m) (hms : Surjective m)
    (χ : PontryaginDual G) (p : BruhatSchwartzStage G) :
    ∃ (q : WholeBruhatStage G) (L : p.Space →L[ℂ] q.val.Space),
      ∀ f x, q.val.realize (L f) x = (χ x : ℂ) * p.realize f x := by
  obtain ⟨P,hP,hχ⟩ := exists_modulatedBruhat_character_stage m hm hms χ
  letI := (lcaStructuralPairs_filtered (G := G)).2
  obtain ⟨R,hp,hR⟩ := exists_ge_ge p.1 P
  obtain ⟨r⟩ := R.quotient_elementary
  let q : WholeBruhatStage G := ⟨⟨R,r⟩, top_unique (hP ▸ hR.1)⟩
  let C := ElementaryLCAModel r.realDim r.torusDim r.latticeRank r.finiteFactor
  let e : Multiplicative C →ₜ* R.StageQuotient := r.equiv.symm
  let χ₀ := R.descendHom (show CircleCharacter G from χ) (fun k => hχ ⟨k.val,hR.2 k.property⟩)
  let θ : PontryaginDual (Multiplicative C) := χ₀.comp e
  have hθ (x : G) : θ (q.coordinates x) = χ x := by
    let y : R.upper.val := ⟨x, q.property.symm ▸ Subgroup.mem_top x⟩
    change χ₀ (r.equiv.symm (r.equiv (QuotientGroup.mk y))) = χ x
    exact (congrArg χ₀ (r.equiv.symm_apply_apply (QuotientGroup.mk y))).trans rfl
  let eval (x : G) : p.Space →L[ℂ] ℂ :=
    ⟨(LinearMap.proj x).comp p.realize, p.continuous_realize_eval x⟩
  have hStage (f : p.Space) : ∃ g : q.val.Space,
      ∀ x : G, q.val.realize g x = (χ x : ℂ) * p.realize f x := by
    let u := p.transition q.val hp f
    let g : q.val.Space := ⟨_, elementarySchwartz_unitaryMul_mem θ u⟩
    refine ⟨g,fun x => ?_⟩
    have he : q.val.realize u x = p.realize f x :=
      congrArg (fun w : BruhatSchwartz G => w.val x) (p.inclusion_transition q.val hp f)
    rw [q.realize_eq_coordinates g, ← he, q.realize_eq_coordinates u]
    change (θ (q.coordinates x) : ℂ) * u (q.coordinates x).toAdd = _
    rw [hθ]
  obtain ⟨L,hL⟩ := bruhatStage_exists_clm_of_evaluation p q.val id surjective_id
    (fun x => (χ x : ℂ) • eval x) hStage
  exact ⟨q,L,hL⟩

private def unitaryWeight (χ : PontryaginDual G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
  LinearMap.mulLeft ℂ (fun g ↦ (χ g : ℂ))

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
private theorem unitaryWeight_commutes (χ : PontryaginDual G) (b : ℝ) (f : G → ℂ) :
    modulatedExponentialWeight m b (unitaryWeight χ f) =
      unitaryWeight χ (modulatedExponentialWeight m b f) :=
  funext fun g => mul_left_comm (Real.exp (b * (m g).toAdd) : ℂ) (χ g : ℂ) (f g)

set_option maxHeartbeats 3200000 in
private theorem exists_decayUnitaryMap (hm : IsProperMap m) (hms : Surjective m)
    (χ : PontryaginDual G) :
    ∃ M : ModulatedExponentialInductive m I →L[ℂ] ModulatedExponentialInductive m I,
      ∀ f, (M f).val = unitaryWeight χ f.val := by
  have hStage (p : BruhatSchwartzStage G) :
      ∃ (q : WholeBruhatStage G) (T : p.Space →L[ℂ] q.val.Space),
        ∀ v, q.val.realize (T v) = unitaryWeight χ (p.realize v) := by
    obtain ⟨q,T,hT⟩ := exists_decayCharacter_stageMap m hm hms χ p
    exact ⟨q,T,fun v => funext (hT v)⟩
  let M₀ := ((unitaryWeight χ).comp ((modulatedExponentialDecaySubmodule m I).subtype.comp
    ModulatedExponentialInductive.algebraicEquiv.toLinearMap)).codRestrict
    (modulatedExponentialDecaySubmodule m I) (fun f ↦ (Submodule.mem_iInf _).mpr fun b ↦ by
      change modulatedExponentialWeight m b (unitaryWeight χ f.val) ∈ bruhatSchwartzSubmodule
      rw [unitaryWeight_commutes]
      obtain ⟨p,v,hv⟩ := (modulatedExponentialDecay_twist m I b
        (ModulatedExponentialInductive.algebraicEquiv f)).property
      obtain ⟨q,T,hT⟩ := hStage p
      exact ⟨q.val,T v,(hT v).trans (congrArg (unitaryWeight χ) hv)⟩)
  let M := ModulatedExponentialInductive.algebraicEquiv.symm.toLinearMap.comp M₀
  refine ⟨⟨M,decay_continuous_of_stageMaps m M fun p ↦ ?_⟩,fun _ ↦ rfl⟩
  obtain ⟨q,T,hT⟩ := hStage p.val
  have hTwist (b : I) (f : WholeBruhatDecayStage m I p) :
      q.val.realize (T (WholeBruhatDecayStage.twist p b f)) =
        modulatedExponentialWeight m b (unitaryWeight χ f.val) := by
    rw [hT, WholeBruhatDecayStage.realize_twist, unitaryWeight_commutes]
  let U (f : WholeBruhatDecayStage m I p) : WholeBruhatDecayStage m I q :=
    WholeBruhatDecayStage.algebraicEquiv.symm ⟨unitaryWeight χ f.val,
      (Submodule.mem_iInf _).mpr fun b => ⟨T (WholeBruhatDecayStage.twist p b f),hTwist b f⟩⟩
  refine ⟨q,U,(WholeBruhatDecayStage.continuous_iff U).mpr fun b ↦ ?_,fun _ ↦ rfl⟩
  have he : WholeBruhatDecayStage.twist q b ∘ U = T ∘ WholeBruhatDecayStage.twist p b := by
    funext f
    apply q.val.1.realizeSchwartz_injective q.val.2
    exact (WholeBruhatDecayStage.realize_twist q b (U f)).trans (hTwist b f).symm
  rw [he]
  exact T.continuous.comp ((WholeBruhatDecayStage.continuous_iff
    (id : WholeBruhatDecayStage m I p → _)).mp continuous_id b)

/-- Unitary character multiplication is a continuous automorphism of the
inductive-limit decay space, with inverse multiplication by the inverse character. -/
theorem modulatedDecay_unitaryEquiv (hm : IsProperMap m) (hms : Surjective m)
    (χ : PontryaginDual G) :
    ∃ e : ModulatedExponentialInductive m I ≃L[ℂ] ModulatedExponentialInductive m I,
      ∀ f g, (e f).val g = (χ g : ℂ) * f.val g := by
  obtain ⟨A,hA⟩ := exists_decayUnitaryMap (I := I) m hm hms χ
  obtain ⟨B,hB⟩ := exists_decayUnitaryMap (I := I) m hm hms χ⁻¹
  have hc (ψ : PontryaginDual G) (f : G → ℂ) : unitaryWeight ψ⁻¹ (unitaryWeight ψ f) = f := by
    funext x
    change (ψ⁻¹ x : ℂ) * ((ψ x : ℂ) * f x) = f x
    rw [← mul_assoc]
    change (((ψ x)⁻¹ * ψ x : Circle) : ℂ) * f x = _
    simp
  refine ⟨ContinuousLinearEquiv.equivOfInverse A B (fun f ↦ ?_) (fun f ↦ ?_),fun f g ↦
    congrFun (hA f) g⟩
  · apply ModulatedExponentialInductive.algebraicEquiv.injective
    apply Subtype.ext
    change (B (A f)).val = f.val
    rw [hB,hA,hc]
  · apply ModulatedExponentialInductive.algebraicEquiv.injective
    apply Subtype.ext
    change (A (B f)).val = f.val
    rw [hA,hB]
    simpa only [inv_inv] using hc χ⁻¹ f.val

/-- Remark D.3.3.6. Multiplication by any continuous quasi-character
is a linear homeomorphism of the space of two-sided exponential decay. -/
theorem modulatedDecay_quasiCharacterEquiv (hm : IsProperMap m) (hms : Surjective m)
    (d : G →ₜ* ℂ) :
    ∃ e : ModulatedExponentialInductive m univ ≃L[ℂ] ModulatedExponentialInductive m univ,
      ∀ f g, (e f).val g = d g * f.val g := by
  obtain ⟨τ,hτ⟩ := exists_realModulation_section m hm hms
  letI : CompactSpace m.toMonoidHom.ker :=
    isCompact_iff_compactSpace.mp (hm.isCompact_preimage (K := {1}) isCompact_singleton)
  obtain ⟨p,⟨_,hp⟩,_⟩ := modulatedLogQuasiCharacter_coordinates m τ hτ d
  have hn (g : G) : ‖d g‖ ≠ 0 := norm_ne_zero_iff.mpr ((Group.isUnit g).map d).ne_zero
  let η : PontryaginDual G :=
    ⟨{ toFun := fun g => ⟨d g / (‖d g‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
         rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self (hn g)])⟩
       map_one' := Circle.ext (by simp)
       map_mul' := fun x y => Circle.ext (by
         change d (x * y) / (‖d (x * y)‖ : ℂ) = (d x / (‖d x‖ : ℂ)) * (d y / (‖d y‖ : ℂ))
         simp only [map_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]) },
      (d.continuous.div (Complex.continuous_ofReal.comp d.continuous.norm)
        (fun g => Complex.ofReal_ne_zero.mpr (hn g))).subtype_mk _⟩
  have hJ : (univ : Set ℝ) = (fun b : ℝ ↦ b - p.2.re) '' univ :=
    (image_univ_of_surjective (fun b => ⟨b + p.2.re, add_sub_cancel_right b p.2.re⟩)).symm
  obtain ⟨S,hS⟩ := modulatedDecay_shiftEquiv m p.2.re hJ
  obtain ⟨U,hU⟩ := modulatedDecay_unitaryEquiv (I := univ) m hm hms η
  refine ⟨S.trans U,fun f g ↦ ?_⟩
  change (U (S f)).val g = _
  rw [hU,hS]
  change d g / (‖d g‖ : ℂ) * ((Real.exp (p.2.re * (m g).toAdd) : ℂ) * f.val g) = _
  rw [← hp g, ← mul_assoc, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hn g))]


end

end Masullo
