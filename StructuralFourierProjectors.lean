/-
The normalized cutoff and averaging identities adapt RiemannMasullo
AppD_SchwartzBruhat/Sec1c.lean at 1d8742feacca560ae3a2beedfb0e743b1efd8bfe
(Apache-2.0). See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import StructuralPairs
import WeilOpenSubgroup
import WeilSigmaCompactLocalization

open Filter Function MeasureTheory Set Topology
open scoped ComplexConjugate ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

omit [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)] in
/-- A compact Haar average of a continuous integrable function is integrable,
including on groups whose Haar measure is not sigma-finite. -/
theorem integrable_compactAverage (K : Subgroup G) (hK : IsCompact (K : Set G))
    (η : Measure K) [IsFiniteMeasure η] {f : G → ℂ} (hf : Integrable f μ)
    (hcont : Continuous f) : Integrable (fun x => ∫ k : K, f (x * k.val) ∂η) μ := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨J, hJo, hJσ, hfj⟩ := exists_open_sigmaCompact_subgroup_of_integrable μ hf
  letI : SigmaCompactSpace J := isSigmaCompact_iff_sigmaCompactSpace.mp hJσ
  let C (n : ℕ) : Set G := Subtype.val '' compactCovering J n ∪ K
  have hC (n : ℕ) : IsCompact (C n) :=
    ((isCompact_compactCovering J n).image continuous_subtype_val).union hK
  obtain ⟨H, hHo, hHσ, hCH⟩ :=
    exists_open_sigmaCompact_subgroup_of_compact_sequence C hC
  have hKH : K ≤ H := fun x hx => hCH 0 (Or.inr hx)
  have hJH : J ≤ H := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_mem_compactCovering (⟨x, hx⟩ : J)
    exact hCH n (Or.inl ⟨⟨x, hx⟩, hn, rfl⟩)
  have hzero (x : G) (hx : x ∉ H) (k : K) : f (x * k.val) = 0 := by
    by_contra hne
    exact hx ((H.mul_mem_cancel_right (hKH k.property)).mp (hJH (hfj hne)))
  letI : SigmaCompactSpace H := isSigmaCompact_iff_sigmaCompactSpace.mp hHσ
  let D (n : ℕ) : Set G := Subtype.val '' compactCovering H n
  have hD (n : ℕ) : IsCompact (D n) :=
    (isCompact_compactCovering H n).image continuous_subtype_val
  have hDH (n : ℕ) : D n ⊆ (H : Set G) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.property
  choose b hb hbs _ _ using fun n =>
    exists_continuousMap_one_of_isCompact_subset_isOpen (hD n) hHo (hDH n)
  let M (p : G × K) := f (p.1 * p.2.val)
  have hMcont : Continuous M := hcont.comp (continuous_fst.mul
    (continuous_subtype_val.comp continuous_snd))
  let Mn (n : ℕ) (p : G × K) := (b n p.1 : ℂ) * M p
  have hMn (n : ℕ) : StronglyMeasurable (Mn n) := by
    apply HasCompactSupport.stronglyMeasurable_of_prod
    · exact (Complex.continuous_ofReal.comp ((b n).continuous.comp continuous_fst)).mul hMcont
    · refine HasCompactSupport.intro ((hbs n).prod (isCompact_univ (X := K))) ?_
      intro p hp
      have h : p.1 ∉ tsupport (b n : G → ℝ) := fun h => hp ⟨h, mem_univ _⟩
      simp [Mn, image_eq_zero_of_notMem_tsupport h]
  have hlim (p : G × K) : Tendsto (fun n => Mn n p) atTop (𝓝 (M p)) := by
    by_cases hp : p.1 ∈ H
    · obtain ⟨n, hn⟩ := exists_mem_compactCovering (⟨p.1, hp⟩ : H)
      refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨n, fun m hm => ?_⟩)
      have hbm := hb m ⟨⟨p.1, hp⟩, compactCovering_subset H hm hn, rfl⟩
      simp [Mn, hbm]
    · simp [Mn, M, hzero p.1 hp p.2]
  have hM : StronglyMeasurable M := by
    rw [show M = fun p => limUnder atTop (fun n => Mn n p) from
      funext fun p => (hlim p).limUnder_eq.symm]
    exact StronglyMeasurable.limUnder hMn
  let N (x : G) := ∫⁻ k : K, ‖M (x, k)‖ₑ ∂η
  letI : SigmaFinite (μ.restrict (H : Set G)) := sigmaFinite_restrict_of_isSigmaCompact μ hHσ
  have hN : ∫⁻ x, N x ∂μ = η univ * ∫⁻ x, ‖f x‖ₑ ∂μ := calc
    _ = ∫⁻ x in (H : Set G), N x ∂μ := by
      symm
      apply setLIntegral_eq_of_support_subset
      intro x hx
      by_contra hn
      exact hx (by simp [N, M, hzero x hn])
    _ = ∫⁻ k : K, ∫⁻ x in (H : Set G), ‖M (x, k)‖ₑ ∂μ ∂η :=
      lintegral_lintegral_swap hM.enorm.aemeasurable
    _ = ∫⁻ k : K, ∫⁻ x, ‖M (x, k)‖ₑ ∂μ ∂η := by
      apply lintegral_congr
      intro k
      exact setLIntegral_eq_of_support_subset (fun x hx => by
        by_contra hn
        exact hx (by simp [M, hzero x hn k]))
    _ = _ := by simp only [M, lintegral_mul_right_eq_self (fun x => ‖f x‖ₑ),
      lintegral_const, mul_comm]
  refine ⟨hM.integral_prod_right'.aestronglyMeasurable, ?_⟩
  apply hasFiniteIntegral_iff_enorm.mpr
  refine (lintegral_mono fun x => enorm_integral_le_lintegral_enorm _).trans_lt ?_
  change (∫⁻ x, N x ∂μ) < ∞
  rw [hN]
  exact ENNReal.mul_lt_top (measure_lt_top η _) (hasFiniteIntegral_iff_enorm.mp hf.2)

omit [μ.IsHaarMeasure] in
/-- The Fourier transform of an open-subgroup cutoff averages over its compact
annihilator, with probability Haar measure. -/
theorem lcaFourier_openCutoff (J : Subgroup G) (hJ : IsOpen (J : Set G))
    (η : Measure (lcaAnnihilator J)) [η.IsHaarMeasure] [IsProbabilityMeasure η] [η.Regular]
    {f : G → ℂ} (hf : Integrable f μ) (χ : PontryaginDual G) :
    lcaFourier μ ((J : Set G).indicator f) χ =
      ∫ ψ : lcaAnnihilator J, lcaFourier μ f (χ * ψ.val) ∂η := by
  classical
  let ν := η.map (Subtype.val : lcaAnnihilator J → PontryaginDual G)
  have hclosed := (isCompact_lcaAnnihilator J hJ).isClosed
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map continuous_subtype_val.aemeasurable
  letI : ν.InnerRegular := Measure.InnerRegular.map_of_continuous continuous_subtype_val
  letI : ν.Regular := inferInstance
  have hmap (u : PontryaginDual G → ℂ) :
      (∫ ψ, u ψ ∂ν) = ∫ ψ : lcaAnnihilator J, u ψ.val ∂η :=
    hclosed.isClosedEmbedding_subtypeVal.integral_map u
  let t (x : G) := f x * star (χ x : ℂ)
  have ht : Integrable t μ := integrable_fourierIntegrand μ hf χ
  have htwist (ψ : PontryaginDual G) : lcaFourier μ t ψ = lcaFourier μ f (χ * ψ) := by
    apply integral_congr_ae
    exact .of_forall fun x => by
      change (f x * star (χ x : ℂ)) * star (ψ x : ℂ) =
        f x * star ((χ x : ℂ) * (ψ x : ℂ))
      rw [star_mul]
      ring
  have heval (x : G) : (∫ ψ : PontryaginDual G, (ψ x : ℂ) ∂ν) =
      (J : Set G).indicator 1 x := by
    rw [hmap]
    by_cases hx : x ∈ J
    · rw [indicator_of_mem hx]
      simp [fun ψ : lcaAnnihilator J =>
        (mem_lcaAnnihilator_iff J ψ.val).mp ψ.property ⟨x, hx⟩]
    · rw [indicator_of_notMem hx]
      have hn : x ∉ lcaDualAnnihilator (lcaAnnihilator J) := by
        rwa [lcaDualAnnihilator_annihilator J (J.isClosed_of_isOpen hJ)]
      obtain ⟨ψ, hψ⟩ := not_forall.mp (mt (mem_lcaDualAnnihilator_iff _ x).mpr hn)
      have htranslate := integral_mul_left_eq_self (μ := η)
        (fun z : lcaAnnihilator J => (z.val x : ℂ)) ψ
      change (∫ z : lcaAnnihilator J, (ψ.val x : ℂ) * (z.val x : ℂ) ∂η) = _ at htranslate
      rw [integral_const_mul] at htranslate
      by_contra hnonzero
      exact hψ (Circle.ext ((mul_eq_right₀ hnonzero).mp htranslate))
  have hpair := lcaInverseFourier_integral_pairing μ ν (u := fun _ => 1)
    (integrable_const _) ht
  simp only [one_mul, htwist] at hpair
  rw [hmap] at hpair
  simp_rw [heval] at hpair
  have hconj := congrArg star hpair
  simp only [Complex.star_def, ← integral_conj, map_mul, starRingEnd_self_apply] at hconj
  refine Eq.trans ?_ hconj
  apply integral_congr_ae
  exact .of_forall fun x => by
    by_cases hx : x ∈ J <;> simp [hx, t]

omit [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)] in
/-- Probability averaging over a compact subgroup cuts the transform down
to its annihilator. Weil integration supplies the normalization. -/
theorem lcaFourier_compactAverage (K : Subgroup G) (hK : IsCompact (K : Set G))
    (η : Measure K) [η.IsHaarMeasure] [IsProbabilityMeasure η] [η.Regular]
    {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hav : ∀ x, g x = ∫ k : K, f (x * k.val) ∂η) (χ : PontryaginDual G) :
    lcaFourier μ g χ = (lcaAnnihilator K : Set (PontryaginDual G)).indicator
      (lcaFourier μ f) χ := by
  classical
  have hinv (x : G) (k : K) : g (x * k.val) = g x := by
    rw [hav, hav]
    simpa only [Subgroup.coe_mul, mul_assoc] using
      integral_mul_left_eq_self (μ := η) (fun h : K => f (x * h.val)) k
  by_cases hχ : χ ∈ lcaAnnihilator K
  · rw [indicator_of_mem hχ]
    obtain ⟨μQ, hQ, -⟩ := weilQuotientMeasure_existsUnique K hK.isClosed μ η
    have hgt := integrable_fourierIntegrand μ hg χ
    have hft := integrable_fourierIntegrand μ hf χ
    unfold lcaFourier
    refine (weilQuotientIntegral_L1 K hK.isClosed μ η μQ hQ hgt).2.2.trans ?_
    refine Eq.trans ?_ (weilQuotientIntegral_L1 K hK.isClosed μ η μQ hQ hft).2.2.symm
    apply integral_congr_ae
    exact .of_forall fun z => by
      have hχk (k : K) : χ (z.out * k.val) = χ z.out := by
        rw [map_mul, (mem_lcaAnnihilator_iff K χ).mp hχ k, mul_one]
      change (∫ k : K, g (z.out * k.val) * star (χ (z.out * k.val) : ℂ) ∂η) =
        ∫ k : K, f (z.out * k.val) * star (χ (z.out * k.val) : ℂ) ∂η
      simp_rw [hχk, hinv, integral_mul_const]
      simp [hav]
  · rw [indicator_of_notMem hχ]
    obtain ⟨k, hk⟩ := not_forall.mp (mt (mem_lcaAnnihilator_iff K χ).mpr hχ)
    have htranslate := lcaFourier_translate μ g k.val χ
    rw [show (fun x => g (k.val * x)) = g from funext fun x => by rw [mul_comm, hinv]]
      at htranslate
    by_contra hn
    exact hk (Circle.ext ((mul_eq_right₀ hn).mp htranslate.symm))

omit [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)] in
private theorem structuralCutoffAverage_aux (P : LCAStructuralPair G)
    (η : Measure P.kernel) [IsFiniteMeasure η] {f : G → ℂ} (hf : Continuous f) :
    let g := (P.upper.val : Set G).indicator (fun x => ∫ k : P.kernel, f (x * k.val) ∂η)
    Continuous g ∧ g = fun x =>
      ∫ k : P.kernel, (P.upper.val : Set G).indicator f (x * k.val) ∂η := by
  classical
  have hcompact : IsCompact (P.kernel : Set G) := by
    rw [← lcaDualAnnihilator_annihilator P.kernel P.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ P.annihilator_open
  letI : CompactSpace P.kernel := isCompact_iff_compactSpace.mp hcompact
  have hopen := P.upper.property.1
  have hclopen : IsClopen (P.upper.val : Set G) :=
    ⟨P.upper.val.isClosed_of_isOpen hopen, hopen⟩
  have hav : Continuous (fun x => ∫ k : P.kernel, f (x * k.val) ∂η) := by
    rw [← continuousOn_univ]
    apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
    · exact (hf.comp (continuous_fst.mul
        (continuous_subtype_val.comp continuous_snd))).continuousOn
    · simp
  refine ⟨hclopen.continuous_indicator hav, funext fun x => ?_⟩
  have hmem (k : P.kernel) : x * k.val ∈ P.upper.val ↔ x ∈ P.upper.val :=
    P.upper.val.mul_mem_cancel_right (P.kernel_le k.property)
  by_cases hx : x ∈ P.upper.val
  · rw [indicator_of_mem hx]
    simp [hmem, hx]
  · rw [indicator_of_notMem hx]
    simp [hmem, hx]

/-- The two normalized structural projectors intertwine under the forward
Fourier transform on continuous integrable functions. -/
theorem lcaFourier_structuralProjector (P : LCAStructuralPair G)
    (η : Measure P.kernel) [η.IsHaarMeasure] [IsProbabilityMeasure η] [η.Regular]
    (θ : Measure (lcaAnnihilator P.upper.val)) [θ.IsHaarMeasure]
    [IsProbabilityMeasure θ] [θ.Regular]
    {f : G → ℂ} (hf : Integrable f μ) (hcont : Continuous f) :
    let g := (P.upper.val : Set G).indicator (fun x => ∫ k : P.kernel, f (x * k.val) ∂η)
    Integrable g μ ∧ Continuous g ∧
    lcaFourier μ g =
      (lcaAnnihilator P.kernel : Set (PontryaginDual G)).indicator
        (fun χ => ∫ ψ : lcaAnnihilator P.upper.val, lcaFourier μ f (χ * ψ.val) ∂θ) := by
  classical
  intro g
  have hcompact : IsCompact (P.kernel : Set G) := by
    rw [← lcaDualAnnihilator_annihilator P.kernel P.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ P.annihilator_open
  let c := (P.upper.val : Set G).indicator f
  have hclopen : IsClopen (P.upper.val : Set G) :=
    ⟨P.upper.val.isClosed_of_isOpen P.upper.property.1, P.upper.property.1⟩
  have hc : Integrable c μ := hf.indicator P.upper.property.1.measurableSet
  obtain ⟨hgcont, hav⟩ := structuralCutoffAverage_aux P η hcont
  have hg : Integrable g μ := by
    change Integrable ((P.upper.val : Set G).indicator _) μ
    rw [hav]
    exact integrable_compactAverage μ P.kernel hcompact η hc (hclopen.continuous_indicator hcont)
  refine ⟨hg, hgcont, ?_⟩
  funext χ
  rw [lcaFourier_compactAverage μ P.kernel hcompact η hc hg (congrFun hav)]
  congr 1
  funext ψ
  exact lcaFourier_openCutoff μ P.upper.val P.upper.property.1 θ hf ψ

/-- Corrected (D.1.6.25). The physical projector equals the inverse Fourier
integral of the transform of the open-subgroup cutoff, restricted to the
annihilator of the kernel. -/
theorem structuralProjector_inverseFourier (P : LCAStructuralPair G)
    (η : Measure P.kernel) [η.IsHaarMeasure] [IsProbabilityMeasure η] [η.Regular]
    (θ : Measure (lcaAnnihilator P.upper.val)) [θ.IsHaarMeasure]
    [IsProbabilityMeasure θ] [θ.Regular]
    (ν : Measure (PontryaginDual G)) (hν : IsLCAPlancherelMeasure μ ν)
    {f : G → ℂ} (hf : Integrable f μ) (hcont : Continuous f)
    (hF : Integrable (lcaFourier μ f) ν) (x : G) :
    (P.upper.val : Set G).indicator (fun y => ∫ k : P.kernel, f (y * k.val) ∂η) x =
      ∫ χ in (lcaAnnihilator P.kernel : Set (PontryaginDual G)),
        lcaFourier μ ((P.upper.val : Set G).indicator f) χ * (χ x : ℂ) ∂ν := by
  classical
  letI : ν.IsHaarMeasure := hν.1
  letI : ν.Regular := hν.2.1
  obtain ⟨hg, hgc, hFg⟩ := lcaFourier_structuralProjector μ P η θ hf hcont
  have hmeas := P.annihilator_open.measurableSet
  have hi := integrable_compactAverage ν _ (isCompact_lcaAnnihilator _ P.upper.property.1)
    θ hF (continuous_lcaFourier μ hf)
  have hFi : Integrable (lcaFourier μ _) ν := hFg ▸ (hi.indicator hmeas)
  obtain ⟨g, hga, hginv⟩ := lcaFourier_plancherel_inversion μ ν hν hg hFi
  have hgeq := Measure.eq_of_ae_eq hga g.continuous hgc
  rw [← hgeq, hginv, hFg, ← integral_indicator hmeas]
  apply integral_congr_ae
  exact .of_forall fun χ => by
    by_cases hχ : χ ∈ lcaAnnihilator P.kernel
    · simpa only [indicator_of_mem hχ] using
        congrArg (fun z : ℂ => z * (χ x : ℂ))
          (lcaFourier_openCutoff μ P.upper.val P.upper.property.1 θ hf χ).symm
    · simp [hχ]

end
end Masullo
