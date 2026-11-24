import BruhatCyclicIsotypicPeriodization
import CompactBruhatFourierSynthesis

open Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 8

section Compact

variable {Q : Type*} [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [T2Space Q] [CompactSpace Q] [LocallyCompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
  (ν : Measure Q) [ν.IsHaarMeasure]

/-- A Fourier coefficient of a translation eigenvector vanishes when the
pairing character does not cancel the eigenvalue. -/
theorem compactBruhatFourierCoeff_eq_zero_of_leftEigen (χ : PontryaginDual Q)
    (f : BruhatSchwartz Q) (a : Q) (c : ℂ)
    (hf : ∀ q, f.val (a * q) = c * f.val q) (hχ : c * (χ a : ℂ) ≠ 1) :
    compactBruhatFourierCoeff ν χ f = 0 := by
  let g (q : Q) := f.val q * (χ q : ℂ)
  have hshift (q : Q) : g (a * q) = (c * (χ a : ℂ)) * g q := by
    dsimp [g]
    rw [hf, map_mul, Circle.coe_mul]
    ring
  have h := integral_mul_left_eq_self (μ := ν) g a
  have h' : (c * (χ a : ℂ)) * (∫ q, g q ∂ν) = ∫ q, g q ∂ν := by
    rw [← integral_const_mul]
    exact (integral_congr_ae (.of_forall fun q ↦ (hshift q).symm)).trans h
  have hz : (c * (χ a : ℂ) - 1) * (∫ q, g q ∂ν) = 0 := by
    rw [sub_mul, one_mul, h', sub_self]
  have hzero := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hχ)
  exact (congrArg ((ν.real univ : ℂ)⁻¹ * ·) hzero).trans (mul_zero _)

variable [SecondCountableTopology Q]

/-- A closed, projected Fourier component keeps exactly the basis vectors
whose coefficients can be nonzero on the component. -/
theorem compactBruhatFourier_component_basis (V : Submodule ℂ (BruhatSchwartz Q))
    (P : BruhatSchwartz Q →L[ℂ] V) (hP : ∀ f : V, P f.val = f)
    (eAll : ℕ ≃ PontryaginDual Q) (e : ℕ → PontryaginDual Q) (he : Injective e)
    (hvec : ∀ n, compactBruhatCharacter (e n)⁻¹ ∈ V)
    (hzero : ∀ χ ∉ range e, ∀ f : V, compactBruhatFourierCoeff ν χ f.val = 0) :
    let x (n : ℕ) : V := ⟨compactBruhatCharacter (e n)⁻¹, hvec n⟩
    let a (n : ℕ) : StrongDual ℂ V := (compactBruhatFourierCoeff ν (e n)).comp V.subtypeL
    IsSchauderBasis x a ∧ IsAbsolute x a ∧ IsShrinking x a ∧
      IsUnconditional a (fun n ↦ strongBidualEvaluation (x n)) := by
  classical
  dsimp only
  let X := BruhatSchwartz Q
  let x (n : ℕ) : V := ⟨compactBruhatCharacter (e n)⁻¹, hvec n⟩
  let a (n : ℕ) : StrongDual ℂ V := (compactBruhatFourierCoeff ν (e n)).comp V.subtypeL
  have hPx (n : ℕ) : P (compactBruhatCharacter (e n)⁻¹) = x n := hP (x n)
  have horth (m n : ℕ) : a m (x n) = if m = n then 1 else 0 := by
    change compactBruhatFourierCoeff ν (e m) (compactBruhatCharacter (e n)⁻¹) = _
    rw [compactBruhatFourierCoeff_character]
    simp [he.eq_iff, eq_comm]
  have hb : IsSchauderBasis x a := by
    refine ⟨horth, fun f ↦ ?_⟩
    have h := hasSum_compactBruhatFourierSeries ν f.val
    have hs := (he.hasSum_iff (fun χ hχ ↦ by rw [hzero χ hχ f, zero_smul])).2 h
    have ht := P.hasSum hs
    rw [hP f] at ht
    have hu : HasSum (fun n ↦ a n f • x n) f :=
      ht.congr_fun (fun n ↦ by
        change _ = P (compactBruhatFourierCoeff ν (e n) f.val • compactBruhatCharacter (e n)⁻¹)
        rw [map_smul, hPx]
        rfl)
    exact Tendsto.mono_left hu (SummationFilter.conditional ℕ).le_atTop
  obtain ⟨_, haAll, _, huAll⟩ := compactBruhatFourierSeries_absoluteBasis ν eAll
  have ha : IsAbsolute x a := by
    intro q hq
    obtain ⟨r, hr, hbound⟩ := haAll (q.comp P.toLinearMap) (hq.comp P.continuous)
    refine ⟨r.comp V.subtype, hr.comp continuous_subtype_val, fun f ↦ ?_⟩
    let j (n : ℕ) := eAll.symm (e n)
    have hj : Injective j := eAll.symm.injective.comp he
    let b (n : ℕ) := q (P (compactBruhatFourierCoeff ν (eAll n) f.val •
      compactBruhatCharacter (eAll n)⁻¹))
    have hval (n : ℕ) : b (j n) = q (a n f • x n) := by
      dsimp only [b, j]
      rw [eAll.apply_symm_apply, map_smul, hPx]
      rfl
    obtain ⟨hs, hle⟩ := hbound f.val
    have hs' : Summable b := hs
    have hbzero (n : ℕ) (hn : n ∉ range j) : b n = 0 := by
      have hn' : eAll n ∉ range e := fun ⟨k, hk⟩ ↦
        hn ⟨k, eAll.injective ((eAll.apply_symm_apply (e k)).trans hk)⟩
      simp only [b, hzero (eAll n) hn' f, zero_smul, map_zero]
    have ht := (hj.hasSum_iff hbzero).2 hs'.hasSum
    have hg := ht.congr_fun (fun n ↦ (hval n).symm)
    exact ⟨hg.summable, hg.tsum_eq.le.trans hle⟩
  have hu : IsUnconditional a (fun n ↦ strongBidualEvaluation (x n)) := by
    intro g
    let u : StrongDual ℂ X := g.comp P
    let R : StrongDual ℂ X →L[ℂ] StrongDual ℂ V := V.subtypeL.precomp ℂ
    have hR : R u = g := ContinuousLinearMap.ext fun f ↦ congrArg g (hP f)
    have h := R.hasSum (huAll u)
    have hs : HasSum (fun χ : PontryaginDual Q ↦
      u (compactBruhatCharacter χ⁻¹) • (compactBruhatFourierCoeff ν χ).comp V.subtypeL) g := by
      apply eAll.hasSum_iff.mp
      rw [← hR]
      refine h.congr_fun fun n ↦ ?_
      simp only [R, Function.comp_def, map_smul, ContinuousLinearMap.precomp_apply, strongBidualEvaluation_apply]
    have ht := (he.hasSum_iff (fun χ hχ ↦ by
      have hz : (compactBruhatFourierCoeff ν χ).comp V.subtypeL = 0 :=
        ContinuousLinearMap.ext fun f ↦ hzero χ hχ f
      rw [hz, smul_zero])).2 hs
    refine ht.congr_fun fun n ↦ ?_
    change g (x n) • a n = g (P (compactBruhatCharacter (e n)⁻¹)) • a n
    rw [hPx]
  refine ⟨hb, ha, ⟨fun m n ↦ ?_, fun g ↦ ?_⟩, hu⟩
  · change a n (x m) = _
    rw [horth]
    simp [eq_comm]
  · exact Tendsto.mono_left (hu g) (SummationFilter.conditional ℕ).le_atTop

end Compact

section Cyclic

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (γ : G) (hγ : 0 < (m γ).toAdd)


variable [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]
  [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker] (μ : Measure m.toMonoidHom.ker) [μ.IsHaarMeasure] (ω : PontryaginDual m.toMonoidHom.ker)

include hm hγ μ in
omit [SecondCountableTopology G] in
/-- Periodization after an invariant cutoff lift gives a continuous
projection onto a prescribed character component of the cyclic quotient. -/
theorem exists_cyclicFourierIsotype_projection (hms : Surjective m) :
    ∃ P : BruhatSchwartz (G ⧸ Subgroup.zpowers γ) →L[ℂ] bruhatCyclicQuotientIsotype m γ ω,
      ∀ f : bruhatCyclicQuotientIsotype m γ ω, P f.val = f := by
  let B := bruhatCyclicPeriodization m hm γ hγ hms
  let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
  obtain ⟨b, hb, C, hC, hs, hright⟩ := exists_weightedCyclicPeriodization_cutoffSection
    m hm hms γ hγ B (bruhatCyclicPeriodization_apply m hm γ hγ hms) univ (mem_univ 0)
  let R := bruhatCyclicDecayCutoffLift m hm hms γ hγ univ b hb C hC hs
  obtain ⟨T, _, _, _, hT⟩ := exists_bruhatCyclic_homogeneousPeriodization
    m hm hms γ hγ μ ω univ (mem_univ 0)
  refine ⟨(μ.real univ : ℂ)⁻¹ • (T.comp R), fun f ↦ ?_⟩
  have hR : R f.val ∈ modulatedDecayIsotype m ω univ := by
    intro a x
    have hma : m a.val = 1 := a.property
    have hlog : (m (a.val⁻¹ * x)).toAdd = (m x).toAdd := by rw [map_mul, map_inv, hma, inv_one, one_mul]
    have hval (z : G) :
        (R f.val).val z = b (m z).toAdd * f.val.val (QuotientGroup.mk z) :=
      bruhatCyclicCutoffLift_apply m hm hms γ hγ b hb C hC hs f.val z
    change (R f.val).val (a.val⁻¹ * x) = (ω a : ℂ) * (R f.val).val x
    rw [hval, hval, hlog, QuotientGroup.mk_mul, f.property a (QuotientGroup.mk x), mul_left_comm]
  letI : CompactSpace m.toMonoidHom.ker := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (show IsCompact ({1} : Set (Multiplicative ℝ)) from isCompact_singleton))
  have hn : (μ.real univ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr measureReal_univ_ne_zero
  apply Subtype.ext
  change (μ.real univ : ℂ)⁻¹ • (T (R f.val)).val = f.val
  rw [hT _ hR, show B (J (R f.val)) = f.val from hright f.val, smul_smul, inv_mul_cancel₀ hn, one_smul]

variable [CompactSpace (G ⧸ Subgroup.zpowers γ)] [SecondCountableTopology (G ⧸ Subgroup.zpowers γ)] [MeasurableSpace (G ⧸ Subgroup.zpowers γ)] [BorelSpace (G ⧸ Subgroup.zpowers γ)]
  (ν : Measure (G ⧸ Subgroup.zpowers γ)) [ν.IsHaarMeasure]

include hm in
omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
  [SecondCountableTopology (G ⧸ Subgroup.zpowers γ)] in
theorem cyclicFourierIsotype_modes
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (lift : CircleCharacter m.toMonoidHom.ker → CircleCharacter G)
    (hlift : ∀ η, (lift η).comp (modulatedKernelInclusion m) = η)
    (e : ℕ ≃ ℤ) :
    let θ (n : ℕ) : PontryaginDual (G ⧸ Subgroup.zpowers γ) :=
      modulatedCyclicCharacter m γ hγ (lift ω) (e n)
    Injective θ ∧
      (∀ n, compactBruhatCharacter (θ n)⁻¹ ∈ bruhatCyclicQuotientIsotype m γ ω) ∧
      ∀ ψ ∉ range θ, ∀ f : bruhatCyclicQuotientIsotype m γ ω,
        compactBruhatFourierCoeff ν ψ f.val = 0 := by
  classical
  dsimp only
  let param (j : CircleCharacter m.toMonoidHom.ker × ℤ) : PontryaginDual (G ⧸ Subgroup.zpowers γ) :=
    modulatedCyclicCharacter m γ hγ (lift j.1) j.2
  let B := Equiv.ofBijective param (modulatedCyclicCharacter_bijective m hm τ hτ γ hγ lift hlift)
  let θ (n : ℕ) : PontryaginDual (G ⧸ Subgroup.zpowers γ) := param (ω, e n)
  have he : Injective θ := by
    intro i j hij
    exact e.injective (congrArg Prod.snd (B.injective hij))
  have hrestrict (j : CircleCharacter m.toMonoidHom.ker × ℤ) (a : m.toMonoidHom.ker) :
      param j (QuotientGroup.mk a.val) = j.1 a := by
    have hma : m a.val = 1 := a.property
    change lift j.1 a.val * Circle.exp (_ * (m a.val).toAdd) = j.1 a
    rw [hma, toAdd_one, mul_zero, Circle.exp_zero, mul_one]
    exact DFunLike.congr_fun (hlift j.1) a
  have hv (n : ℕ) : compactBruhatCharacter (θ n)⁻¹ ∈ bruhatCyclicQuotientIsotype m γ ω := by
    intro a q
    change (((θ n (QuotientGroup.mk a.val⁻¹ * q))⁻¹ : Circle) : ℂ) =
      (ω a : ℂ) * (((θ n q)⁻¹ : Circle) : ℂ)
    have h : (θ n (QuotientGroup.mk a.val⁻¹ * q))⁻¹ = ω a * (θ n q)⁻¹ := by
      rw [QuotientGroup.mk_inv, map_mul, map_inv, mul_inv, inv_inv, hrestrict (ω, e n)]
      rfl
    exact (congrArg (fun z : Circle ↦ (z : ℂ)) h).trans (Circle.coe_mul _ _)
  have hz (ψ : PontryaginDual (G ⧸ Subgroup.zpowers γ)) (hψ : ψ ∉ range θ) (f : bruhatCyclicQuotientIsotype m γ ω) :
      compactBruhatFourierCoeff ν ψ f.val = 0 := by
    obtain ⟨j, rfl⟩ := B.surjective ψ
    have hj : j.1 ≠ ω := by
      intro heq
      apply hψ
      refine ⟨e.symm j.2, congrArg param (Prod.ext heq.symm (e.apply_symm_apply j.2))⟩
    have ha : ∃ a : m.toMonoidHom.ker, j.1 a ≠ ω a := by
      by_contra! h
      exact hj (ContinuousMonoidHom.ext h)
    obtain ⟨a, ha⟩ := ha
    apply compactBruhatFourierCoeff_eq_zero_of_leftEigen ν (param j) f.val
      (QuotientGroup.mk a.val⁻¹) (ω a : ℂ) (f.property a)
    intro hc
    have hqa : param j (QuotientGroup.mk a.val⁻¹) = (j.1 a)⁻¹ := by
      rw [QuotientGroup.mk_inv, map_inv, hrestrict]
    rw [hqa, Circle.coe_inv] at hc
    apply ha
    apply Subtype.ext
    exact ((mul_inv_eq_one₀ (j.1 a).coe_ne_zero).mp hc).symm
  exact ⟨he, hv, hz⟩

end Cyclic

end

end Masullo
