import SLocalOrbitalFourierJets
import SLocalPaleyWienerOrbitalQuotient
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev P := HeightOneSpectrum (𝓞 F)
private abbrev E := sLocalBruhatImage F
private abbrev X := mixedEmbedding.mixedSpace F

variable (S : Finset (P F))

open scoped ContDiff in
private theorem exists_sLocalTest_eval_zero_ne_zero :
    ∃ f : E F S, GlobalBruhat.evaluation F 0 f.val ≠ 0 := by
  let b : ContDiffBump (0 : X F) := ⟨1, 2, by norm_num, by norm_num⟩
  let p (x : X F) : ℂ := (b x : ℝ)
  have hC : HasCompactSupport p := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hD : ContDiff ℝ ∞ p := Complex.ofRealCLM.contDiff.comp b.contDiff
  let φ := hC.toSchwartzMap hD
  let ψ := locallyConstantTestPiProduct (fun v : S ↦ finiteCompletionIntegerRingTest F v.val)
  let f := sLocalBruhatPure F S φ ψ
  refine ⟨f, ?_⟩
  have hφ : φ 0 = 1 := by
    change (b 0 : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), Complex.ofReal_one]
  have hψ (v : S) : (finiteCompletionIntegerRingTest F v.val).val 0 = 1 := by
    change (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)).indicator
      (fun _ ↦ (1 : ℂ)) 0 = 1
    exact indicator_of_mem (zero_mem _) _
  have hRestr : sLocalBruhatRestriction F S f.val 0 = 1 := by
    change sLocalBruhatRestriction F S (sLocalBruhatPure F S φ ψ).val 0 = 1
    rw [sLocalBruhatPure_restrict, locallyConstantTestPiProduct_apply]
    change φ ((InfiniteAdeleRing.ringEquiv_mixedSpace F) 0) * (∏ v : S,
      (finiteCompletionIntegerRingTest F v.val).val 0) = 1
    simp only [map_zero, hφ, hψ, Finset.prod_const_one, mul_one]
  have h : GlobalBruhat.evaluation F 0 f.val = 1 := by
    rw [sLocalBruhatRestriction_reconstruct, map_zero, hRestr]
    rw [ite_eq_left (show ∀ v ∉ S, (0 : Adeles F).2 v ∈ v.adicCompletionIntegers F from
      fun v _ ↦ zero_mem (v.adicCompletionIntegers F)), mul_one]
  exact h.trans_ne one_ne_zero

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩

variable (νG : Measure (normOneIdeleClass F)) [νG.IsHaarMeasure]

private abbrev G (ω : PontryaginDual (normOneIdeleClass F)) (f : E F S) :=
  globalZetaContinued F νG f.val (compactIdeleClassCharacter F ω) 0

private theorem sLocalTest_trivial_order_zero_neg_one (f : E F S)
    (hf : GlobalBruhat.evaluation F 0 f.val ≠ 0) :
    meromorphicOrderAt (G F S νG 1 f) 0 = (-1 : ℤ) := by
  let χ := compactIdeleClassCharacter F 1
  have hmass : (νG.real univ : ℂ) ≠ 0 := by
    letI := normOneIdeleClass_compact F
    letI : IsFiniteMeasure νG := ⟨isCompact_univ.measure_lt_top⟩
    exact_mod_cast (measureReal_univ_pos (μ := νG)).ne'
  have he : (∫ k : normOneIdeleClass F, (χ k.val : ℂ) ∂νG) = (νG.real univ : ℂ) := by
    simpa only [χ, ite_eq_left rfl, ite_true] using compactIdeleClassCharacter_integral F νG 1
  have hx := (globalZetaContinued_pole_order F νG f.val χ
    (compactIdeleClassCharacter_unitary F 1) 0).1
  simp only [neg_zero, he, ite_eq_right
    (mul_ne_zero hmass hf : (νG.real univ : ℂ) * (GlobalBruhat.algebraicEquiv F f.val).val 0 ≠ 0)] at hx
  exact hx

variable [∀ v : P F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : P F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : P F, Measure (v.adicCompletion F)ˣ)
  [∀ v : P F, (μ v).IsHaarMeasure] [∀ v : P F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
  (hνG : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F νG))
variable (ω : PontryaginDual (normOneIdeleClass F))
  (hs : Surjective (sIdeleClassInclusion F S))
  (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev K := SLocalThetaNormOne F S
private abbrev σ := sLocalNormOneCharacterOfGlobal F ω S hs hu

private abbrev N (f : E F S) :=
  sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val) (σ F S ω hs hu) f

include hνG in
/-- In the trivial component the pole-clearing normalization adds
one to the global order at zero, including for tests with vanishing moments. -/
theorem sLocalOrbital_trivial_order_zero
    (hs₁ : Surjective (sIdeleClassInclusion F S))
    (hu₁ : globalNormOneCharacter F (1 : PontryaginDual (normOneIdeleClass F)) ∈
      (sUnramified F S : Set (QuasiCharacter (IdeleClass F)))) (f : E F S) :
    meromorphicOrderAt (G F S νG 1 f) 0 =
      ((-1 : ℤ) : WithTop ℤ) + meromorphicOrderAt (N F S μ 1 hs₁ hu₁ f) 0 := by
  obtain ⟨r, _, _, _, _, hRef⟩ :=
    exists_globalMellin_order_reference F η 1 S hs₁ hu₁ μ νG hνG
  obtain ⟨u, hu⟩ := exists_sLocalTest_eval_zero_ne_zero F S
  have hr : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (G F S νG 1 r) 0 := by
    have h := (globalZetaContinued_pole_order F νG r.val (compactIdeleClassCharacter F 1)
      (compactIdeleClassCharacter_unitary F 1) 0).1
    simp only [neg_zero] at h
    split_ifs at h
    · exact (WithTop.coe_le_coe.mpr (by decide : (-1 : ℤ) ≤ 0)).trans h.meromorphicOrderAt_nonneg
    · exact h.ge
  have hnu : 0 ≤ meromorphicOrderAt (N F S μ 1 hs₁ hu₁ u) 0 :=
    (sLocalEulerNormalizedMellin_entire F S (fun v ↦ μ v.val) _ u 0
      (mem_univ _)).meromorphicOrderAt_nonneg
  have hl : meromorphicOrderAt (G F S νG 1 r) 0 ≤ (-1 : ℤ) := by
    calc
      _ ≤ meromorphicOrderAt (G F S νG 1 r) 0 + meromorphicOrderAt (N F S μ 1 hs₁ hu₁ u) 0 :=
        le_add_of_nonneg_right hnu
      _ = _ := (hRef u 0).symm.trans (sLocalTest_trivial_order_zero_neg_one F S νG u hu)
  rw [hRef, le_antisymm hl hr]


variable (νS : Measure (K F S)) [νS.IsHaarMeasure]
  (hνS : IsWeilQuotientMeasure (sUnitImage F S)
    (sLocalZetaProductMeasure F S (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F))
    Measure.count (sLocalClassHaar F S νS))

private abbrev Z (χ : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S (fun v ↦ μ v.val) χ
    (sLocalRealArchParameters F S χ) (sLocalComplexArchParameters F S χ) f

include hνG hνS in
/-- The lowest reflected Fourier coordinate at zero vanishes throughout
the trivial two-moment space, before any principal-value quotient. -/
theorem sLocalOrbital_trivial_fourier_value_at_zero
    (hω : ω = 1) (f : E F S) (hf : GlobalBruhat.polarEvaluation F f.val = 0) :
    Z F S μ (σ F S ω hs hu)⁻¹ (sLocalFourierCompression F S f) 1 = 0 := by
  obtain rfl := hω
  have h₀ := ((globalMellin_nonneg_orders_iff F 1 νG f.val).mpr (Or.inr hf)).1
  change (0 : WithTop ℤ) ≤ meromorphicOrderAt (G F S νG 1 f) 0 at h₀
  rw [sLocalOrbital_trivial_order_zero F S νG μ η hνG hs hu f] at h₀
  have he : (1 : WithTop ℤ) ≤ meromorphicOrderAt (N F S μ 1 hs hu f) 0 := by
    have ht : ((-1 : ℤ) : WithTop ℤ) + (1 : WithTop ℤ) = 0 := by
      change ((-1 : ℤ) : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_add]
      norm_num
    apply (WithTop.add_le_add_iff_left (x := ((-1 : ℤ) : WithTop ℤ)) (by simp)).mp
    rw [ht]
    exact h₀
  have hj := (sLocalOrbitalCompressedJet_vanish_iff_normalized_order F S μ η νG hνG
    1 hs hu νS hνS f 0 (by simp) 1).mpr he 0 (by decide)
  simpa only [iteratedDeriv_zero, sub_zero] using hj

omit [∀ v : P F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : P F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem restriction_one (hω : ω = 1) : σ F S ω hs hu = 1 := by
  obtain rfl := hω
  apply ContinuousMonoidHom.ext
  intro q
  obtain ⟨k, rfl⟩ := globalNormOneToSLocal_surjective F S hs q
  exact sLocalNormOneCharacterOfGlobal_match F 1 S hs hu k

omit [∀ v : P F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : P F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem trivial_finitePhase (v : S) (u : (v.val.adicCompletion F)ˣ) :
    sLocalFiniteZetaPhases F S 1 v u = 1 := by
  apply Circle.coe_injective
  change sLocalZetaWeight F S 1 0 (QuotientGroup.mk (sLocalFiniteZetaInsert F S v u)) = 1
  simp [sLocalZetaWeight]

omit [∀ v : P F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : P F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- Every selected place contributes one to the zero multiplicity for the
trivial character. -/
theorem sLocalSelectedFinitePoleCount_trivial_zero (W : Finset S) :
    sLocalSelectedFinitePoleCount F S 1 W 0 = W.card := by
  unfold sLocalSelectedFinitePoleCount
  congr 1
  apply Finset.filter_true_of_mem
  intro v _
  have hU : finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S 1 v) :=
    fun u _ ↦ trivial_finitePhase F S v u
  simp [finiteZetaWeilMultiplier, hU, finiteZetaRatio, trivial_finitePhase]

include hνG hνS in
/-- On tests with both moments zero the principal-value range is detected
by the reflected Fourier jets. The trivial character requires one extra
jet at zero because its global Euler reference has a simple pole there. -/
theorem sLocalOrbitalCompressedJets_ker_eq_polar_principalValue_range
    (W : Finset S) (f : E F S) (hf : GlobalBruhat.polarEvaluation F f.val = 0) :
    let A := σ F S ω hs hu
    let M := sLocalHomogeneousThetaKernel F S νS A
    let t := sLocalSelectedFinitePoleCount F S A W
    let n (c : ℂ) := t c + (if ω = 1 ∧ c = 0 then 1 else 0)
    M.mkQ f ∈ range (fun g : {g : E F S // GlobalBruhat.polarEvaluation F g.val = 0} ↦
      M.mkQ (sLocalWeilPrincipalValues F S W g.val)) ↔
      ∀ c : ℂ, c.re = 0 → ∀ k < n c,
        iteratedDeriv k (fun z ↦ Z F S μ A⁻¹ (sLocalFourierCompression F S f) (1-z)) c = 0 := by
  intro A M t n
  let o (c : ℂ) := meromorphicOrderAt (N F S μ ω hs hu f) c
  let g (c : ℂ) := meromorphicOrderAt (G F S νG ω f) c
  have hn (c : ℂ) : 0 ≤ o c :=
    (sLocalEulerNormalizedMellin_entire F S (fun v ↦ μ v.val) A f c
      (mem_univ _)).meromorphicOrderAt_nonneg
  have ht (c : ℂ) (hc : c.re ≠ 0) : t c = 0 := by
    apply Nat.eq_zero_of_not_pos
    exact fun h ↦ hc (sLocalSelectedFinitePoleCount_re_zero F S A W c h)
  have hn' (c : ℂ) (hc : c.re ≠ 0) : n c = 0 := by
    have hc' : c ≠ 0 := fun h ↦ hc (by simp [h])
    change t c + (if ω = 1 ∧ c = 0 then 1 else 0) = 0
    simp [ht c hc, hc']
  have h1 : (t 1 : WithTop ℤ) ≤ g 1 := by
    rw [ht 1 (by simp), Nat.cast_zero]
    exact ((globalMellin_nonneg_orders_iff F ω νG f.val).mpr (Or.inr hf)).2
  let ordinary := ∀ c : ℂ, (t c : WithTop ℤ) ≤ o c
  let enhanced := ∀ c : ℂ, (n c : WithTop ℤ) ≤ o c
  obtain ⟨_, _, _, _, _, hRange⟩ :=
    exists_globalMellin_polar_selected_order_iff_principalValue_range
      F η ω S hs hu μ νG hνG νS hνS
  have hBasic :
      (∀ c : ℂ, 0 < t c → ∀ k : ℕ, sLocalPoleCount F S A c - t c < k →
        k ≤ sLocalPoleCount F S A c →
        sLocalLaurentCoeff F S (fun v ↦ μ v.val) A c k f = 0) ↔ ordinary := by
    change _ ↔ ∀ c, (t c : WithTop ℤ) ≤ o c
    apply forall_congr'
    intro c
    by_cases hc : 0 < t c
    · have hband : (∀ k : ℕ, sLocalPoleCount F S A c - t c < k →
          k ≤ sLocalPoleCount F S A c →
          sLocalLaurentCoeff F S (fun v ↦ μ v.val) A c k f = 0) ↔
          ∀ k : ℕ, sLocalPoleCount F S A c - t c < k →
            sLocalLaurentCoeff F S (fun v ↦ μ v.val) A c k f = 0 := by
        refine ⟨fun h k hk ↦ ?_, fun h k hk _ ↦ h k hk⟩
        by_cases hkd : k ≤ sLocalPoleCount F S A c
        · exact h k hk hkd
        · have hbound := sLocalZeta_poleOrder_le_euler F S (fun v ↦ μ v.val) A f c
          rw [sLocalEulerFactor_order F S A c, sLocalAllowedPoleOrder_eq_count F S A c] at hbound
          exact (sLocalLaurentCoeff_vanish_iff F S (fun v ↦ μ v.val) A c _ f).mpr
            hbound k (lt_of_not_ge hkd)
      exact (⟨fun h ↦ h hc, fun h _ ↦ h⟩ : (_ → _) ↔ _).trans
        (hband.trans (sLocal_removedLaurent_iff_normalized_order F S (fun v ↦ μ v.val) A W f c))
    · rw [show t c = 0 from Nat.eq_zero_of_not_pos hc, Nat.cast_zero]
      exact iff_of_true (fun h ↦ (lt_irrefl _ h).elim) (hn c)
  have hAdd : (ordinary ∧ (t 0 : WithTop ℤ) ≤ g 0) ↔ enhanced := by
    by_cases hω : ω = 1
    · obtain rfl := hω
      have h0 : (t 0 : WithTop ℤ) ≤ g 0 ↔ ((t 0 + 1 : ℕ) : WithTop ℤ) ≤ o 0 := by
        change _ ≤ meromorphicOrderAt (G F S νG 1 f) 0 ↔ _
        rw [sLocalOrbital_trivial_order_zero F S νG μ η hνG hs hu f]
        have hc (m : ℕ) : (m : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) + ((m + 1 : ℕ) : WithTop ℤ) := by
          rw [Nat.cast_add, Nat.cast_one]
          rw [← add_assoc, add_comm ((-1 : ℤ) : WithTop ℤ), add_assoc]
          norm_num
        conv_lhs => lhs; rw [hc]
        exact WithTop.add_le_add_iff_left (by simp)
      refine ⟨fun ⟨h, h'⟩ c ↦ ?_, fun h ↦ ⟨fun c ↦ ?_, ?_⟩⟩
      · by_cases hc : c = 0
        · subst c
          simpa only [n, true_and, ite_true] using h0.mp h'
        · simpa only [n, true_and, hc, ite_false, add_zero] using h c
      · exact (Nat.cast_le.mpr (Nat.le_add_right _ _)).trans (h c)
      · exact h0.mpr (by simpa only [n, true_and, ite_true] using h 0)
    · have hN : n = t := by
        funext c
        simp [n, hω]
      have h0 (h : ordinary) : (t 0 : WithTop ℤ) ≤ g 0 := by
        obtain ⟨r, _, _, _, _, hRef⟩ :=
          exists_globalMellin_order_reference F η ω S hs hu μ νG hνG
        have hr : 0 ≤ meromorphicOrderAt (G F S νG ω r) 0 :=
          ((globalMellin_nonneg_orders_iff F ω νG r.val).mpr (Or.inl hω)).1
        change _ ≤ meromorphicOrderAt (G F S νG ω f) 0
        rw [hRef]
        exact (h 0).trans (le_add_of_nonneg_left hr)
      have he : enhanced = ordinary := by rw [show enhanced = (∀ c, (n c : WithTop ℤ) ≤ o c) from rfl, hN]
      rw [he]
      exact ⟨And.left, fun h ↦ ⟨h, h0 h⟩⟩
  refine (hRange W f).2.1.trans ?_
  rw [hBasic]
  refine ((and_congr_right fun _ ↦ and_iff_left h1).trans hAdd).trans ?_
  constructor
  · intro h c hc
    exact (sLocalOrbitalCompressedJet_vanish_iff_normalized_order F S μ η νG hνG ω hs hu νS hνS
      f c hc (n c)).mpr (h c)
  · intro h c
    by_cases hc : c.re = 0
    · exact (sLocalOrbitalCompressedJet_vanish_iff_normalized_order F S μ η νG hνG ω hs hu νS hνS
        f c hc (n c)).mp (h c hc)
    · rw [hn' c hc, Nat.cast_zero]
      exact hn c


include hνG hνS in
/-- At a positive selected multiplicity at zero, the ordinary reflected
Fourier jets fail to separate the zero-moment orbital classes. -/
theorem exists_sLocalOrdinaryJetKernel_ne_polar_range
    (hω : ω = 1) (W : Finset S)
    (hW : 0 < sLocalSelectedFinitePoleCount F S (σ F S ω hs hu) W 0) :
    let A := σ F S ω hs hu
    let M := sLocalHomogeneousThetaKernel F S νS A
    ∃ f : E F S, GlobalBruhat.polarEvaluation F f.val = 0 ∧
      (∀ c : ℂ, ∀ k < sLocalSelectedFinitePoleCount F S A W c,
        iteratedDeriv k (fun z ↦ Z F S μ A⁻¹ (sLocalFourierCompression F S f) (1-z)) c = 0) ∧
      M.mkQ f ∉ range (fun g : {g : E F S // GlobalBruhat.polarEvaluation F g.val = 0} ↦
        M.mkQ (sLocalWeilPrincipalValues F S W g.val)) := by
  obtain rfl := hω
  intro A M
  obtain ⟨u, hu₀⟩ := exists_sLocalTest_eval_zero_ne_zero F S
  let a := sLocalExpSection F S (Multiplicative.ofAdd (1 : ℝ))
  let b := (sLocalEmbed F S a).val
  have hb : 1 < ideleNorm F b := by
    change 1 < sLocalIdeleNorm F S a
    rw [sLocalIdeleNorm_expSection]
    exact Real.one_lt_exp_iff.mpr zero_lt_one
  let g := sLocalBruhatLeftTranslate F S a u - (ideleNorm F b : ℂ) • u
  let p := GlobalBruhat.polarEvaluation F
  have hgp : p g.val = ((1 - (ideleNorm F b : ℂ)) * (p u.val).1, 0) := by
    change p (GlobalBruhat.leftTranslate F b u.val - (ideleNorm F b : ℂ) • u.val) = _
    rw [map_sub, map_smul]
    change GlobalBruhat.polarEvaluation F (GlobalBruhat.leftTranslate F b u.val) -
      (ideleNorm F b : ℂ) • p u.val = _
    rw [polarEvaluation_leftTranslate]
    apply Prod.ext
    · change (p u.val).1 - (ideleNorm F b : ℂ) * (p u.val).1 = _
      ring
    · change (ideleNorm F b : ℝ) • (p u.val).2 - (ideleNorm F b : ℂ) * (p u.val).2 = 0
      rw [Complex.real_smul, sub_self]
  have hg₀ : GlobalBruhat.evaluation F 0 g.val ≠ 0 := by
    change (p g.val).1 ≠ 0
    rw [hgp]
    exact mul_ne_zero (sub_ne_zero.mpr fun h ↦ hb.ne (by exact_mod_cast h)) hu₀
  have ho₀ := sLocalTest_trivial_order_zero_neg_one F S νG g hg₀
  have ho₁ : 0 ≤ meromorphicOrderAt (G F S νG 1 g) 1 := by
    have hh := (globalZetaContinued_pole_order F νG g.val (compactIdeleClassCharacter F 1)
      (compactIdeleClassCharacter_unitary F 1) 0).2
    have hgp₁ : (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F g.val)).val 0 = 0 :=
      congrArg Prod.snd hgp
    simp only [hgp₁, mul_zero, sub_zero, ite_true] at hh
    exact hh.meromorphicOrderAt_nonneg
  let f := sLocalWeilPrincipalValues F S W g
  let t := sLocalSelectedFinitePoleCount F S A W
  have hOrder (c : ℂ) : meromorphicOrderAt (G F S νG 1 f) c =
      (t c : WithTop ℤ) + meromorphicOrderAt (G F S νG 1 g) c := by
    change meromorphicOrderAt (globalZetaContinued F νG (sLocalWeilPrincipalValues F S W g).val
      (compactIdeleClassCharacter F 1) 0) c = _
    rw [← globalWeilPrincipalValues_stage]
    exact globalWeilPrincipalValues_order F η 1 S hs hu μ νG hνG W g.val c
  have hOrdZero : 0 ≤ meromorphicOrderAt (G F S νG 1 f) 0 := by
    rw [hOrder, ho₀]
    change ((0 : ℤ) : WithTop ℤ) ≤ ((t 0 : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ)
    rw [← WithTop.coe_add, WithTop.coe_le_coe]
    have ht : 0 < t 0 := hW
    omega
  have hOrdOne : 0 ≤ meromorphicOrderAt (G F S νG 1 f) 1 := by
    rw [hOrder]
    exact add_nonneg (by positivity) ho₁
  have hf : p f.val = 0 := ((globalMellin_nonneg_orders_iff F 1 νG f.val).mp
    ⟨hOrdZero, hOrdOne⟩).resolve_left (not_not_intro rfl)
  refine ⟨f, hf, ?_, ?_⟩
  · apply (sLocalOrbitalCompressedJets_ker_eq_principalValue_range F S μ η νG hνG
      1 hs hu νS hνS W f).mp
    refine ⟨f, ?_, rfl⟩
    rw [← sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace]
    exact ⟨g, rfl⟩
  · intro hm
    obtain ⟨_, _, _, _, _, hRange⟩ :=
      exists_globalMellin_polar_selected_order_iff_principalValue_range
        F η 1 S hs hu μ νG hνG νS hνS
    have hp := ((hRange W f).2.1.mp hm).2.1
    change (t 0 : WithTop ℤ) ≤ meromorphicOrderAt (G F S νG 1 f) 0 at hp
    rw [hOrder, ho₀] at hp
    change ((t 0 : ℤ) : WithTop ℤ) ≤ ((t 0 : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) at hp
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at hp
    omega

include hνG hνS in
/-- The enhanced jet test on zero-moment representatives descends to
the actual ambient Paley–Wiener orbital quotient. -/
theorem sLocalPaleyWienerOrbitalClass_eq_zero_iff_polarJets
    (W : Finset S)
    (hU : ∀ v ∈ W, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S (σ F S ω hs hu) v))
    (f : E F S) (hf : GlobalBruhat.polarEvaluation F f.val = 0) :
    let A := σ F S ω hs hu
    let M := sLocalHomogeneousThetaKernel F S νS A
    let H := sLocalPaleyWienerMomentImage F νS A
    let R := sLocalPaleyWienerOrbitalRange F νS A W
    let q : H := ⟨M.mkQ f, Submodule.mem_map.mpr ⟨f, hf, rfl⟩⟩
    R.mkQ q = 0 ↔
      ∀ c : ℂ, c.re = 0 →
        ∀ k < sLocalSelectedFinitePoleCount F S A W c + (if ω = 1 ∧ c = 0 then 1 else 0),
          iteratedDeriv k (fun z ↦ Z F S μ A⁻¹ (sLocalFourierCompression F S f) (1-z)) c = 0 := by
  intro A M H R q
  let ρ := sLocalZetaProductMeasure F S (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
  letI : ρ.IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
  have he := sLocalPaleyWienerOrbitalRange_image F νS A ρ hνS W hU
  have hj := sLocalOrbitalCompressedJets_ker_eq_polar_principalValue_range F S νG μ η hνG
    ω hs hu νS hνS W f hf
  refine (Submodule.Quotient.mk_eq_zero R).trans (Iff.trans ?_ hj)
  constructor
  · intro h
    have hm : q.val ∈ H.subtype '' (R : Set H) := ⟨q, h, rfl⟩
    exact he ▸ hm
  · intro h
    have hm : q.val ∈ H.subtype '' (R : Set H) := he.symm ▸ h
    obtain ⟨x, hx, heq⟩ := hm
    have hq : x = q := Subtype.ext heq
    exact hq ▸ hx

include hνG hνS in
/-- The ordinary Fourier jets miss a nonzero class of the ambient
zero-moment orbital quotient in every nonempty trivial-character case. -/
theorem exists_sLocalPaleyWienerOrbitalClass_ordinaryJets_zero
    (hω : ω = 1) (W : Finset S) (hW : W.Nonempty) :
    let A := σ F S ω hs hu
    let M := sLocalHomogeneousThetaKernel F S νS A
    let H := sLocalPaleyWienerMomentImage F νS A
    let R := sLocalPaleyWienerOrbitalRange F νS A W
    ∃ (f : E F S) (q : H), q.val = M.mkQ f ∧ R.mkQ q ≠ 0 ∧
      (∀ c : ℂ, ∀ k < sLocalSelectedFinitePoleCount F S A W c,
        iteratedDeriv k (fun z ↦ Z F S μ A⁻¹ (sLocalFourierCompression F S f) (1-z)) c = 0) := by
  intro A M H R
  have hA : A = 1 := restriction_one F S ω hs hu hω
  have hCount : 0 < sLocalSelectedFinitePoleCount F S A W 0 := by
    rw [hA, sLocalSelectedFinitePoleCount_trivial_zero]
    exact Finset.card_pos.mpr hW
  obtain ⟨f, hf, hj, hn⟩ := exists_sLocalOrdinaryJetKernel_ne_polar_range F S νG μ
    η hνG ω hs hu νS hνS hω W hCount
  let q : H := ⟨M.mkQ f, Submodule.mem_map.mpr ⟨f, hf, rfl⟩⟩
  refine ⟨f, q, rfl, ?_, hj⟩
  intro hz
  have hr := (Submodule.Quotient.mk_eq_zero R).mp hz
  let ρ := sLocalZetaProductMeasure F S (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
  letI : ρ.IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
  have hU : ∀ v ∈ W, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S A v) := by
    rw [hA]
    exact fun v _ u _ ↦ trivial_finitePhase F S v u
  have hm : q.val ∈ H.subtype '' (R : Set H) := ⟨q, hr, rfl⟩
  have he := sLocalPaleyWienerOrbitalRange_image F νS A ρ hνS W hU
  exact hn (he ▸ hm)

end

end Masullo
