import CompactElementaryDual
import CompactBruhatFourierSynthesis
import BruhatCyclicPeriodizationCorollary

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal

namespace Masullo

noncomputable section

set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 8

section Elementary

variable {n : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

local notation "B" => ElementaryLCAModel 0 0 n F

/-- Polynomial decay in integer coordinates gives a Schwartz test in the
corresponding discrete elementary model. -/
theorem elementarySchwartz_mem_discrete_of_rapid (f : B → ℂ)
    (hf : ∀ d : ℕ, ∃ C : ℝ, ∀ (a : Fin n → ℤ) (b : F),
      (1 + ∑ i, ‖(a i : ℝ)‖) ^ d * ‖f (0, 0, a, b)‖ ≤ C) :
    f ∈ elementarySchwartzSubmodule 0 0 n F := by
  change (∀ a b, ContDiff ℝ ∞ (fun x ↦ f (elementaryCover x a b))) ∧
    ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞)
  constructor
  · intro a b
    have h : (fun x : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 0) ↦
        f (elementaryCover x a b)) = fun _ ↦ f (0, 0, a, b) := by
      funext x
      rw [show x = 0 from Subsingleton.elim _ _]
      congr 1
    rw [h]
    exact contDiff_const
  · intro i
    obtain ⟨C, hC⟩ := hf (∑ j, i.2.2.2 j)
    refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := C))
    unfold elementarySchwartzBound
    refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
    rw [show i.2.1 = 0 from Subsingleton.elim _ _, show i.2.2.1 = 0 from Subsingleton.elim _ _,
      elementaryPartial_zero, Finset.prod_of_isEmpty, one_mul]
    have hx : elementaryCover x a b = ((0, 0, a, b) : B) :=
      Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) rfl)
    rw [hx]
    have hp : ‖∏ j, (a j : ℂ) ^ i.2.2.2 j‖ ≤ (1 + ∑ j, ‖(a j : ℝ)‖) ^ (∑ j, i.2.2.2 j) := by
      rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
      simp only [norm_pow, ← Complex.ofReal_intCast, Complex.norm_real]
      refine Finset.prod_le_prod (fun j _ ↦ by positivity) fun j _ ↦ ?_
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (Finset.single_le_sum (f := fun l : Fin n ↦ ‖(a l : ℝ)‖)
        (fun l _ ↦ norm_nonneg _) (Finset.mem_univ j)).trans (by linarith)
    apply (ENNReal.le_ofReal_iff_toReal_le ENNReal.coe_ne_top ?_).2
    · change ‖(∏ j, (a j : ℂ) ^ i.2.2.2 j) * f (0, 0, a, b)‖ ≤ C
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans (hC a b)
    · exact (by positivity : 0 ≤ (1 + ∑ j, ‖(a j : ℝ)‖) ^ (∑ j, i.2.2.2 j) * ‖f (0, 0, a, b)‖)
        |>.trans (hC a b)

end Elementary

section CompactElementary

variable {m n r : ℕ} {F : Type} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

local notation "A" => ElementaryLCAModel m n r F

/-- A compact elementary stage's Fourier pairing is a Schwartz test in an
elementary presentation of its discrete dual. -/
theorem exists_elementaryFourierPairing_dualSchwartz
    [CompactSpace A] [CompactSpace (Multiplicative A)] [MeasurableSpace (Multiplicative A)]
    [BorelSpace (Multiplicative A)] (μ : Measure (Multiplicative A)) [μ.IsHaarMeasure]
    (f : ElementarySchwartz m n r F) :
    ∃ (p : ElementaryLCAPresentation (PontryaginDual (Multiplicative A)))
      (u : ElementarySchwartz p.realDim p.torusDim p.latticeRank p.finiteFactor),
      ∀ χ, u.val (p.equiv χ).toAdd = elementaryFourierPairing μ χ f := by
  obtain ⟨rfl, rfl⟩ := elementaryLCAModel_compact_dimensions (m := m) (n := n) (r := r) (F := F)
  letI : Finite (Multiplicative F) := Finite.of_equiv F Multiplicative.ofAdd
  letI : CompactSpace (Multiplicative F) := Finite.compactSpace
  let D := Additive (PontryaginDual (Multiplicative F))
  let e := compactElementaryDualEquiv (F := F) (n := n)
  let p : ElementaryLCAPresentation (PontryaginDual (Multiplicative (ElementaryLCAModel 0 n 0 F))) :=
    { realDim := 0
      torusDim := 0
      latticeRank := n
      finiteFactor := D
      equiv := e.symm }
  let g (x : ElementaryLCAModel 0 0 n D) :=
    elementaryFourierPairing μ (compactElementaryDualEquiv (Multiplicative.ofAdd x)) f
  have hg : g ∈ elementarySchwartzSubmodule 0 0 n D := by
    apply elementarySchwartz_mem_discrete_of_rapid
    intro d
    let C := ((n : ℝ) + 1) ^ d * (elementarySchwartzSeminorm (0, 0, 0, 0) f +
      ∑ i : Fin n, elementarySchwartzSeminorm (0, 0, 0, 0)
        ((elementarySchwartz_derivative (elementaryOneParameter (elementaryTorusVelocity i)))^[d + 1] f)) *
      μ.real univ
    refine ⟨C, fun a b ↦ ?_⟩
    let χ := compactElementaryDualEquiv (F := F) (Multiplicative.ofAdd ((0, 0, a, b) :
      ElementaryLCAModel 0 0 n D))
    have hw : compactElementaryFrequencyWeight χ = 1 + ∑ i, ‖(a i : ℝ)‖ := by
      unfold compactElementaryFrequencyWeight
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦
        congrArg (fun j : ℤ ↦ ‖(j : ℝ)‖) (compactElementaryDualEquiv_frequency _ i)
    change (1 + ∑ i, ‖(a i : ℝ)‖) ^ d * ‖elementaryFourierPairing μ χ f‖ ≤ C
    rw [← hw]
    have hw₀ : 1 ≤ compactElementaryFrequencyWeight χ :=
      hw ▸ le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hw₀ (Nat.le_succ d))
      (norm_nonneg _)).trans (compactElementaryFourierPairing_rapid_decay μ χ f d)
  refine ⟨p, ⟨g, hg⟩, fun χ ↦ ?_⟩
  change elementaryFourierPairing μ (e (e.symm χ)) f = _
  rw [ContinuousMulEquiv.apply_symm_apply]

end CompactElementary

section Discrete

variable {T : Type*} [CommGroup T] [TopologicalSpace T] [DiscreteTopology T]

private theorem lcaAnnihilator_dual_bot_eq_top : lcaAnnihilator (⊥ : Subgroup T) = ⊤ := by
  apply top_unique
  intro χ _
  apply (mem_lcaAnnihilator_iff _ _).mpr
  intro x
  have hx : x.val = 1 := Subgroup.mem_bot.mp x.property
  rw [hx, map_one]

private def discreteFourierStagePair (H : OpenCompactlyGeneratedSubgroups T) : LCAStructuralPair T where
  upper := H
  kernel := ⊥
  kernel_closed := isClosed_discrete _
  annihilator_open := by
    rw [lcaAnnihilator_dual_bot_eq_top, Subgroup.coe_top]
    exact isOpen_univ
  annihilator_compactlyGenerated := by
    rw [lcaAnnihilator_dual_bot_eq_top]
    let V := (⊤ : Subgroup (PontryaginDual T))
    have hV : IsCompact (V : Set (PontryaginDual T)) := by
      rw [Subgroup.coe_top]
      exact isCompact_univ
    letI : CompactSpace V := isCompact_iff_compactSpace.mp hV
    exact ⟨univ, univ_mem, isCompact_univ, by simp⟩
  kernel_le := bot_le

private def discreteFourierStageQuotientEquiv (H : OpenCompactlyGeneratedSubgroups T) :
    (discreteFourierStagePair H).StageQuotient ≃ₜ* H.val := by
  let K : Subgroup H.val := (discreteFourierStagePair H).kernel.comap H.val.subtype
  have hk : K = (MonoidHom.id H.val).ker := by
    ext x
    change x.val = 1 ↔ x = 1
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  let e := QuotientGroup.liftEquiv K (show Surjective (MonoidHom.id H.val) from surjective_id) hk
  have he (x : H.val) : e (QuotientGroup.mk x) = x := rfl
  exact { e with
    continuous_toFun := (QuotientGroup.isQuotientMap_mk K).continuous_iff.2
      (continuous_id.congr fun x ↦ (he x).symm)
    continuous_invFun := QuotientGroup.continuous_mk.congr fun x ↦
      (e.symm_apply_eq.mpr (he x)).symm }

private theorem discreteFourierStageQuotientEquiv_mk (H : OpenCompactlyGeneratedSubgroups T)
    (x : H.val) :
    discreteFourierStageQuotientEquiv H (QuotientGroup.mk x) = x := rfl

private theorem discreteFourierStage_mem
    (H : OpenCompactlyGeneratedSubgroups T) (p : ElementaryLCAPresentation H.val)
    (u : ElementarySchwartz p.realDim p.torusDim p.latticeRank p.finiteFactor) (f : T → ℂ)
    (hinside : ∀ x : H.val, f x.val = u.val (p.equiv x).toAdd)
    (houtside : ∀ x ∉ H.val, f x = 0) :
    f ∈ bruhatSchwartzSubmodule := by
  let Q := discreteFourierStagePair H
  let q : ElementaryLCAPresentation Q.StageQuotient :=
    { p with equiv := (discreteFourierStageQuotientEquiv H).trans p.equiv }
  let s : BruhatSchwartzStage T := ⟨Q, q⟩
  refine ⟨s, u, funext fun x ↦ ?_⟩
  by_cases hx : x ∈ H.val
  · let y : H.val := ⟨x, hx⟩
    have hy : Q.stageCoordinates q y = p.equiv y :=
      congrArg p.equiv (discreteFourierStageQuotientEquiv_mk H y)
    exact (Q.realizeSchwartz_apply_of_mem q u y).trans
      ((congrArg (fun z ↦ u.val z.toAdd) hy).trans (hinside y).symm)
  · exact (Q.realizeSchwartz_apply_of_not_mem q u x hx).trans (houtside x hx).symm

end Discrete

section Compact

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [CompactSpace G] [LocallyCompactSpace G]

local notation "T" => PontryaginDual G

variable (P : WholeBruhatStage G)

local notation "A" => WholeBruhatStage.coordinateModel P

private def stageDualEquiv [CompactSpace (Multiplicative A)] :
    PontryaginDual (Multiplicative A) ≃ₜ* lcaAnnihilator P.val.1.kernel := by
  let pull := PontryaginDual.map P.coordinates
  let t : PontryaginDual (Multiplicative A) →* lcaAnnihilator P.val.1.kernel :=
    { toFun θ := ⟨pull θ, (mem_lcaAnnihilator_iff _ _).2 fun a ↦ by
        have ha : a.val ∈ P.coordinates.toMonoidHom.ker := by
          rw [P.coordinates_ker]
          exact a.property
        change θ (P.coordinates a.val) = 1
        rw [show P.coordinates a.val = 1 from ha, map_one]⟩
      map_one' := Subtype.ext (map_one pull)
      map_mul' θ η := Subtype.ext (map_mul pull θ η) }
  let e := MulEquiv.ofBijective t (by
    constructor
    · intro θ η h
      apply PontryaginDual.ext
      intro z
      obtain ⟨x, rfl⟩ := P.coordinates_surjective z
      exact congrArg (fun χ : lcaAnnihilator P.val.1.kernel ↦ χ.val x) h
    · intro χ
      have hk : P.val.1.kernel ≤ χ.val.toMonoidHom.ker := fun a ha ↦
        (mem_lcaAnnihilator_iff _ _).1 χ.property ⟨a, ha⟩
      obtain ⟨θ, hθ, _⟩ := wholeBruhatStage_character_descends P χ.val hk
      exact ⟨θ, Subtype.ext hθ⟩)
  exact { e with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

private theorem stageDualEquiv_val [CompactSpace (Multiplicative A)]
    (θ : PontryaginDual (Multiplicative A)) : (stageDualEquiv P θ).val = θ.comp P.coordinates := rfl

variable [MeasurableSpace G] [BorelSpace G]

variable {L : Type*} [CommGroup L] [TopologicalSpace L] [DiscreteTopology L]

private theorem compactBruhatFourierCoeff_mem_bruhat_stage (μ : Measure G) [μ.IsHaarMeasure]
    (u : P.val.Space) (E : T ≃ₜ* L) :
    (fun χ : L ↦ compactBruhatFourierCoeff μ (E.symm χ) (P.val.inclusion u)) ∈ bruhatSchwartzSubmodule := by
  letI : CompactSpace (Multiplicative A) := P.coordinates_surjective.compactSpace P.coordinates.continuous
  letI : CompactSpace A := Multiplicative.toAdd.surjective.compactSpace continuous_toAdd
  letI : MeasurableSpace (Multiplicative A) := borel _
  letI : BorelSpace (Multiplicative A) := ⟨rfl⟩
  let ν : Measure (Multiplicative A) := μ.map P.coordinates
  letI : ν.IsHaarMeasure := μ.isHaarMeasure_map_of_isFiniteMeasure P.coordinates.toMonoidHom
    P.coordinates.continuous P.coordinates_surjective
  obtain ⟨p, f, hf⟩ := exists_elementaryFourierPairing_dualSchwartz ν u
  let H := lcaAnnihilator P.val.1.kernel
  let I := H.map E.toMulEquiv.toMonoidHom
  let j₀ := E.toMulEquiv.subgroupMap H
  let j : H ≃ₜ* I :=
    { j₀ with continuous_toFun := continuous_of_discreteTopology
              continuous_invFun := continuous_of_discreteTopology }
  have hI : IsCompactlyGeneratedGroup I := by
    obtain ⟨K, hn, hc, hg⟩ := P.val.1.annihilator_compactlyGenerated
    refine ⟨j '' K, mem_nhds_discrete.mpr ⟨1, mem_of_mem_nhds hn, map_one j⟩, hc.image j.continuous, ?_⟩
    change Subgroup.closure (j.toMulEquiv.toMonoidHom '' K) = ⊤
    rw [← MonoidHom.map_closure, hg, Subgroup.map_top_of_surjective _ j.surjective]
  let U : OpenCompactlyGeneratedSubgroups L := ⟨I, isOpen_discrete _, hI⟩
  let e := j.symm.trans (stageDualEquiv P).symm
  let q : ElementaryLCAPresentation U.val := { p with equiv := e.trans p.equiv }
  let c : ℂ := (μ.real univ : ℂ)⁻¹
  refine discreteFourierStage_mem U q (c • f) _ ?_ ?_
  · intro y
    let x : H := j.symm y
    have hx : x.val = E.symm y.val := rfl
    let θ := (stageDualEquiv P).symm x
    have hθ : θ.comp P.coordinates = E.symm y.val :=
      (stageDualEquiv_val P θ).symm.trans
        ((congrArg Subtype.val ((stageDualEquiv P).apply_symm_apply x)).trans hx)
    change compactBruhatFourierCoeff μ (E.symm y.val) (P.val.inclusion u) =
      c * f.val (p.equiv θ).toAdd
    calc
      _ = compactBruhatFourierCoeff μ (θ.comp P.coordinates) (P.val.inclusion u) :=
        congrArg (fun φ ↦ compactBruhatFourierCoeff μ φ (P.val.inclusion u)) hθ.symm
      _ = c * elementaryFourierPairing ν θ u := compactBruhatFourierCoeff_stage P μ θ u
      _ = _ := congrArg (c * ·) (hf θ).symm
  · intro χ hχ
    have hx : E.symm χ ∉ H := fun h ↦ hχ (Subgroup.mem_map_equiv.mpr h)
    have hnon : ∃ a ∈ P.val.1.kernel, E.symm χ a ≠ 1 := by
      by_contra! h
      exact hx ((mem_lcaAnnihilator_iff _ _).mpr fun a ↦ h a.val a.property)
    exact compactBruhatFourierCoeff_eq_zero_off_stage_annihilator μ P u (E.symm χ) hnon

/-- The normalized Fourier coefficient function of a compact Schwartz–Bruhat
test belongs to the full discrete Schwartz–Bruhat space of the dual group. -/
theorem compactBruhatFourierCoeff_mem_bruhat (μ : Measure G) [μ.IsHaarMeasure]
    (f : BruhatSchwartz G) (E : T ≃ₜ* L) :
    (fun χ : L ↦ compactBruhatFourierCoeff μ (E.symm χ) f) ∈ bruhatSchwartzSubmodule := by
  obtain ⟨P, u, rfl⟩ := exists_compactBruhat_wholeStage f
  exact compactBruhatFourierCoeff_mem_bruhat_stage P μ u E

end Compact

section Cyclic

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (γ : G)

local notation "Q" => G ⧸ Subgroup.zpowers γ

private theorem cyclicAnnihilator_eq :
    lcaAnnihilator (Subgroup.zpowers γ) = MonogenicAnnihilator γ := by
  ext χ
  refine (mem_lcaAnnihilator_iff _ χ).trans
    (Iff.trans ?_ (mem_monogenicAnnihilator_iff (show CircleCharacter G from χ) γ).symm)
  constructor
  · intro h n
    exact h ⟨γ ^ n, Subgroup.zpow_mem_zpowers γ n⟩
  · intro h x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.property
    rw [← hn]
    exact h n

/-- Lemma 4.4.2.6(2a). The normalized cyclic coefficients form one
Schwartz–Bruhat function on the actual annihilator. -/
theorem modulatedCyclicFourierCoeff_exists_bruhat
    (m : G →ₜ* Multiplicative ℝ) (hγ : 0 < (m γ).toAdd)
    [T2Space Q] [LocallyCompactSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (ν : Measure Q) [ν.IsHaarMeasure] (f : BruhatSchwartz Q) :
    ∃ e : PontryaginDual Q ≃ₜ* MonogenicAnnihilator γ,
      (∀ θ x, (e θ).val x = θ (QuotientGroup.mk x)) ∧
      (letI := e.toHomeomorph.discreteTopology
       ∃! v : BruhatSchwartz (MonogenicAnnihilator γ),
         (∀ θ, v.val (e θ) = compactBruhatFourierCoeff ν θ f) ∧
         (∀ χ n, v.val (e (modulatedCyclicCharacter m γ hγ χ n)) =
           modulatedCyclicFourierCoeff m γ hγ ν χ n f)) := by
  obtain ⟨e, he⟩ : ∃ e : PontryaginDual Q ≃ₜ* MonogenicAnnihilator γ,
      ∀ θ x, (e θ).val x = θ (QuotientGroup.mk x) := by
    rw [← cyclicAnnihilator_eq γ]
    exact lcaQuotientDual_equiv_annihilator _ (modulatedCyclicSubgroup_isClosed m γ hγ)
  letI := e.toHomeomorph.discreteTopology
  let v : BruhatSchwartz (MonogenicAnnihilator γ) :=
    ⟨_, compactBruhatFourierCoeff_mem_bruhat ν f e⟩
  have hv (θ : PontryaginDual Q) : v.val (e θ) = compactBruhatFourierCoeff ν θ f :=
    congrArg (fun ψ : PontryaginDual Q ↦ compactBruhatFourierCoeff ν ψ f) (e.symm_apply_apply θ)
  refine ⟨e, he, v, ⟨hv, fun χ n ↦ (hv (modulatedCyclicCharacter m γ hγ χ n)).trans
    (modulatedCyclicFourierCoeff_eq_compact m γ hγ ν χ n f).symm⟩, ?_⟩
  rintro w ⟨hw, _⟩
  apply Subtype.ext
  funext x
  obtain ⟨θ, rfl⟩ := e.surjective x
  exact (hw θ).trans (hv θ).symm

end Cyclic

end

end Masullo
