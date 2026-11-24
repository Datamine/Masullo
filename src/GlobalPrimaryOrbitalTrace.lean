import PeriodicOrbitalMoments
import OrbitalConvolutionJets
import HilbertOrbitalTrace

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical CompactlySupported InnerProductSpace NNReal NumberField SchwartzMap

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev zAt (ξ : ℝ) : ℂ := (↑(-2 * Real.pi * ξ) : ℂ) * Complex.I

local instance primaryTraceQMeasure : MeasurableSpace (Q F) := borel _
local instance primaryTraceQBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance primaryTraceQT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance primaryTraceQLC : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance primaryTraceQSecondCountable : SecondCountableTopology (Q F) := ideleClass_secondCountable F

variable (μ : Measure (Q F)) [μ.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)

private abbrev H (ω : PontryaginDual (K F)) := globalOrbitalSobolevIsotype F μ s hs ω
private abbrev R (A : Finset (Place F)) (ω : PontryaginDual (K F)) :=
  globalWeilIsotypeClosedRange F μ s hs A ω
private abbrev I (A : Finset (Place F)) (ω : PontryaginDual (K F)) :=
  globalWeilMomentIndices F A ω

local instance primaryTraceHComplete (ω : PontryaginDual (K F)) : CompleteSpace (H F μ s hs ω) :=
  (globalOrbitalSobolevIsotype_isClosed F μ s hs ω).completeSpace_coe
local instance primaryTraceRClosed (A : Finset (Place F)) (ω : PontryaginDual (K F)) :
    IsClosed (R F μ s hs A ω : Set (H F μ s hs ω)) :=
  Submodule.isClosed_topologicalClosure _

/-- Convolution compressed to the orthogonal realization of the closed-range quotient. -/
def primaryOrbitalCompressedConvolution (A : Finset (Place F)) (ω : PontryaginDual (K F))
    (φ : C_c(Q F, ℂ)) : (R F μ s hs A ω)ᗮ →L[ℂ] (R F μ s hs A ω)ᗮ :=
  (R F μ s hs A ω)ᗮ.orthogonalProjectionOnto.comp
    ((globalIsotypicOrbitalConvolution F μ s hs ω φ).comp (R F μ s hs A ω)ᗮ.subtypeL)

private abbrev representative (A : Finset (Place F)) (hdeg : 2 * (A.card : ℝ) ≤ s)
    (ω : PontryaginDual (K F)) (i : I F A ω) : (R F μ s hs A ω)ᗮ :=
  ⟨globalWeilMomentRepresentative F μ s hs A hdeg ω i,
    globalWeilMomentRepresentative_mem_orthogonal F μ s hs A hdeg ω i⟩

private abbrev momentCLM (A : Finset (Place F)) (hdeg : 2 * (A.card : ℝ) ≤ s)
    (ω : PontryaginDual (K F)) (i : I F A ω) : (R F μ s hs A ω)ᗮ →L[ℂ] ℂ :=
  innerSL ℂ (representative F μ s hs A hdeg ω i)

private abbrev lowerIndex (A : Finset (Place F)) (ω : PontryaginDual (K F))
    (i : I F A ω) (j : Fin (i.val.2+1)) : I F A ω :=
  ⟨(i.val.1,j.val), (Nat.le_of_lt_succ j.isLt).trans_lt i.property⟩

private theorem canonical_admissible (A : Finset (Place F)) (hdeg : 2 * (A.card : ℝ) ≤ s)
    (ω : PontryaginDual (K F)) (i : I F A ω) :
    (i.val.2 : ℝ) < (s-1)/2 :=
  globalWeilMoment_admissible F s A ω (normOneEulerCharacter F ω) (zAt i.val.1)
    hdeg i.val.2 i.property

private theorem canonical_z_re (ξ : ℝ) : (zAt ξ).re = 0 := by simp [Complex.mul_re]

private theorem representative_inner_ambient (A : Finset (Place F)) (hdeg : 2 * (A.card : ℝ) ≤ s)
    (ω : PontryaginDual (K F)) (i : I F A ω) (u : H F μ s hs ω) :
    ⟪globalWeilMomentRepresentative F μ s hs A hdeg ω i,u⟫_ℂ =
      orbitalSobolevMomentCLM F μ s hs (normOneEulerCharacter F ω) (zAt i.val.1)
        (canonical_z_re i.val.1) i.val.2 (canonical_admissible F s A hdeg ω i) u.val := rfl

set_option maxHeartbeats 1400000 in
private theorem primaryOrbitalConvolution_row (A : Finset (Place F)) (hdeg : 2 * (A.card : ℝ) ≤ s)
    (ω : PontryaginDual (K F)) (φ : C_c(Q F, ℂ)) (i : I F A ω) :
    (momentCLM F μ s hs A hdeg ω i).comp (primaryOrbitalCompressedConvolution F μ s hs A ω φ) =
      ∑ j : Fin (i.val.2+1), ((i.val.2.choose j : ℂ) *
        orbitalConvolutionCoefficient F μ φ (normOneEulerCharacter F ω) (zAt i.val.1) (i.val.2-j)) •
          momentCLM F μ s hs A hdeg ω (lowerIndex F A ω i j) := by
  ext u : 1
  let B := globalIsotypicOrbitalConvolution F μ s hs ω φ
  change ⟪representative F μ s hs A hdeg ω i,(R F μ s hs A ω)ᗮ.orthogonalProjectionOnto (B u.val)⟫_ℂ =
    (∑ j : Fin (i.val.2+1), ((i.val.2.choose j : ℂ) *
      orbitalConvolutionCoefficient F μ φ (normOneEulerCharacter F ω) (zAt i.val.1) (i.val.2-j)) •
      momentCLM F μ s hs A hdeg ω (lowerIndex F A ω i j)) u
  rw [(R F μ s hs A ω)ᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left]
  change ⟪globalWeilMomentRepresentative F μ s hs A hdeg ω i,B u.val⟫_ℂ = _
  rw [representative_inner_ambient]
  change orbitalSobolevMomentCLM F μ s hs (normOneEulerCharacter F ω) (zAt i.val.1)
    (canonical_z_re i.val.1) i.val.2 (canonical_admissible F s A hdeg ω i)
    (globalHardySobolevConvolution F μ 0 0 s hs φ u.val.val) = _
  rw [orbitalSobolevMomentCLM_convolution]
  simp only [sum_apply, _root_.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change _ = ⟪globalWeilMomentRepresentative F μ s hs A hdeg ω (lowerIndex F A ω i j),u.val⟫_ℂ
  rw [representative_inner_ambient, orbitalSobolevMomentCLM_apply]


private theorem primaryOrbitalMoment_norm_bound (A : Finset (Place F))
    (hdeg : 2 * (A.card : ℝ) ≤ s) (hs' : 1 < s) (ω : PontryaginDual (K F)) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : I F A ω, ‖momentCLM F μ s hs A hdeg ω i‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := imaginaryOrbitalSobolevMoments_uniform_norm F μ hs'
  refine ⟨C,hC,fun i ↦ ?_⟩
  let χ := normOneEulerCharacter F ω
  let z := zAt i.val.1
  let hi := canonical_admissible F s A hdeg ω i
  obtain ⟨hm, _, hu⟩ := h χ z (canonical_z_re _) i.val.2 hi
  rw [show ‖momentCLM F μ s hs A hdeg ω i‖ =
      ‖representative F μ s hs A hdeg ω i‖ from innerSL_apply_norm ℂ _]
  change ‖globalOrbitalMomentRieszVector F μ s hs χ z (canonical_z_re _) i.val.2 hi‖ ≤ C
  rw [globalOrbitalMomentRieszVector_norm F μ s hs χ z (canonical_z_re _) i.val.2 hi hm]
  exact hu

set_option maxHeartbeats 900000 in
/-- Absolute summability of the Haar jet coefficients gives the orbital trace
of the actual convolution on the orthogonal realization of the quotient. -/
theorem primaryOrbitalConvolution_trace_of_summable (A : Finset (Place F))
    {p : ℕ} (hp : p.Prime)
    (hA : ∀ v ∈ A, v.asIdeal.under ℤ = Ideal.span {(p : ℤ)})
    (hdeg : 2 * (A.card : ℝ) ≤ s) (hs' : 1 < s) (ω : PontryaginDual (K F)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : C_c(Q F, ℂ))
      (_hSummable : ∀ k ∈ Finset.range (A.card+1), Summable (fun i : I F A ω ↦
        ‖orbitalConvolutionCoefficient F μ φ (normOneEulerCharacter F ω) (zAt i.val.1) k‖)),
      ∃ T : TraceClass ((R F μ s hs A ω)ᗮ),
        T.toOperator = primaryOrbitalCompressedConvolution F μ s hs A ω φ ∧
        ‖T‖ ≤ C * ∑ k ∈ Finset.range (A.card+1), ∑' i : I F A ω,
          ‖orbitalConvolutionCoefficient F μ φ (normOneEulerCharacter F ω) (zAt i.val.1) k‖ ∧
        Summable (fun i : I F A ω ↦
          ‖orbitalConvolutionCoefficient F μ φ (normOneEulerCharacter F ω) (zAt i.val.1) 0‖) ∧
        T.traceValue = ∑' i : I F A ω,
          orbitalConvolutionCoefficient F μ φ (normOneEulerCharacter F ω) (zAt i.val.1) 0 := by
  obtain ⟨B,hB,q,hq,hbi⟩ := exists_globalPrimaryMoment_bounded_interpolation F s hs μ A hdeg hp hA ω
  obtain ⟨D,hD,hn⟩ := primaryOrbitalMoment_norm_bound F μ s hs A hdeg hs' ω
  let n := A.card
  let C := B * ((n+1 : ℕ) : ℝ) * (2 : ℝ)^n * D
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun φ hSummable ↦ ?_⟩
  let W := R F μ s hs A ω
  let X := I F A ω
  letI : CompleteSpace Wᗮ := W.isClosed_orthogonal.completeSpace_coe
  let P := Wᗮ.orthogonalProjectionOnto
  let v (i : X) := P (q i)
  let f : X → StrongDual ℂ Wᗮ := momentCLM F μ s hs A hdeg ω
  let L := primaryOrbitalCompressedConvolution F μ s hs A ω φ
  let a (i : X) (k : ℕ) := orbitalConvolutionCoefficient F μ φ (normOneEulerCharacter F ω) (zAt i.val.1) k
  letI : Countable X := (globalWeilMomentIndices_countable F A ω).to_subtype
  have hv (i : X) : ‖v i‖ ≤ B := (Wᗮ.norm_orthogonalProjectionOnto_apply_le _).trans (hq i)
  have hb (i j : X) : f i (v j) = if i = j then 1 else 0 := by
    change ⟪representative F μ s hs A hdeg ω i,P (q j)⟫_ℂ = _
    exact (Wᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left _ _).trans (hbi j i)
  have ht (u : Wᗮ) (hu : ∀ i, f i u = 0) : u = 0 := by
    have hh := (mem_globalWeilIsotypeClosedRange_iff_inner F μ s hs A hdeg ω u.val).mpr hu
    exact Subtype.ext (inner_self_eq_zero.mp ((Submodule.mem_orthogonal W u.val).mp u.property u.val hh))
  have hr (i : X) : (f i).comp L =
      ∑ j : Fin (i.val.2+1), ((i.val.2.choose j : ℂ) * a i (i.val.2-j)) • f (lowerIndex F A ω i j) :=
    primaryOrbitalConvolution_row F μ s hs A hdeg ω φ i
  have hncard (i : X) : i.val.2 ≤ n := by
    have h := i.property
    change i.val.2 < (A.filter _).card at h
    exact h.le.trans (Finset.card_filter_le _ _)
  have hLast (i : X) : lowerIndex F A ω i (Fin.last i.val.2) = i := Subtype.ext rfl
  have hOther (i : X) (j : Fin (i.val.2+1)) (hj : j ≠ Fin.last i.val.2) :
      lowerIndex F A ω i j ≠ i :=
    fun h ↦ hj (Fin.ext (congrArg (fun k : X ↦ k.val.2) h))
  have hf (i : X) : ‖f i‖ ≤ D := hn i
  refine traceClass_of_triangular_jet_rows (H := Wᗮ) (ι := X) L v (f := f)
    hb ht (fun i : X ↦ i.val.2) n hncard (lowerIndex F A ω)
    hLast hOther a hr B D hB hD hv ?_ hSummable
  exact hf

/-- The compact continuous density underlying a compact Bruhat test. -/
def primaryOrbitalBruhatDensity (φ : BruhatCompactTest (Q F)) : C_c(Q F, ℂ) :=
  ⟨⟨φ.val.val, bruhatSchwartz_continuous φ.val⟩,(BruhatCompactTest.algebraicEquiv φ).property⟩

local instance primaryTraceKMeasure : MeasurableSpace (K F) := borel _
local instance primaryTraceKBorel : BorelSpace (K F) := ⟨rfl⟩
local instance primaryTraceKCompact : CompactSpace (K F) := normOneIdeleClass_compact F

variable (ν : Measure (K F)) [ν.IsHaarMeasure]

local instance primaryTraceSplitHaar : (globalClassMeasure F ν).IsHaarMeasure :=
  globalClassMeasure_isHaar F ν

set_option maxHeartbeats 1200000 in
/-- The untruncated primary trace is bounded by a continuous seminorm of
the actual compact Bruhat test. The diagonal is the order-zero Haar coefficient. -/
theorem primaryOrbitalBruhat_trace_split (A : Finset (Place F))
    {p : ℕ} (hp : p.Prime)
    (hA : ∀ v ∈ A, v.asIdeal.under ℤ = Ideal.span {(p : ℤ)})
    (hdeg : 2 * (A.card : ℝ) ≤ s) (hs' : 1 < s) (ω : PontryaginDual (K F)) :
    ∃ P : Seminorm ℂ (BruhatCompactTest (Q F)), Continuous P ∧
      ∀ φ : BruhatCompactTest (Q F),
      ∃ T : TraceClass ((R F (globalClassMeasure F ν) s hs A ω)ᗮ),
        T.toOperator = primaryOrbitalCompressedConvolution F (globalClassMeasure F ν) s hs A ω
          (primaryOrbitalBruhatDensity F φ) ∧
        ‖T‖ ≤ P φ ∧
        Summable (fun i : I F A ω ↦ ‖orbitalConvolutionSchwartzCoefficients F ν ω 0 φ i.val.1‖) ∧
        T.traceValue = ∑' i : I F A ω, orbitalConvolutionSchwartzCoefficients F ν ω 0 φ i.val.1 := by
  let σ := globalClassMeasure F ν
  obtain ⟨C,hC,hTr⟩ := primaryOrbitalConvolution_trace_of_summable F σ s hs A hp hA hdeg hs' ω
  obtain ⟨D,hD,hS⟩ := globalPrimaryMoment_samples_bound F A hp hA ω
  let c := orbitalConvolutionSchwartzCoefficients F ν ω
  let q (k : ℕ) : Seminorm ℂ (BruhatCompactTest (Q F)) :=
    ((SchwartzMap.seminorm ℂ 0 0 + SchwartzMap.seminorm ℂ 2 0) : Seminorm ℂ 𝓢(ℝ, ℂ)).comp
      (c k).toLinearMap
  let N : ℕ := ⌈C*D⌉₊
  let P : Seminorm ℂ (BruhatCompactTest (Q F)) := N • (∑ k ∈ Finset.range (A.card+1), q k)
  have hq (k : ℕ) : Continuous (q k) := by
    exact (((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (0,0)).add
      ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (2,0))).comp (c k).continuous
  have hPapply (φ : BruhatCompactTest (Q F)) : P φ =
      (N : ℝ) * ∑ k ∈ Finset.range (A.card+1), q k φ := by
    simp only [P, _root_.smul_apply, sum_apply, nsmul_eq_mul]
  have hP : Continuous P := by
    have heq : (P : BruhatCompactTest (Q F) → ℝ) =
        fun φ ↦ (N : ℝ) * ∑ k ∈ Finset.range (A.card+1), q k φ := funext hPapply
    rw [heq]
    exact continuous_const.mul (continuous_finsetSum _ fun k _ ↦ hq k)
  refine ⟨P,hP,fun φ ↦ ?_⟩
  have he (k : ℕ) (i : I F A ω) : c k φ i.val.1 =
      orbitalConvolutionCoefficient F σ (primaryOrbitalBruhatDensity F φ)
        (normOneEulerCharacter F ω) (zAt i.val.1) k :=
    orbitalConvolutionSchwartzCoefficients_apply F ν ω k φ i.val.1
  obtain ⟨T,hT,hN,hSummable,htrace⟩ := hTr (primaryOrbitalBruhatDensity F φ)
    (fun k _ ↦ by simpa only [he k] using (hS (c k φ)).1)
  refine ⟨T,hT,hN.trans ?_,?_,?_⟩
  · calc
      _ ≤ C * ∑ k ∈ Finset.range (A.card+1), D * q k φ := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply Finset.sum_le_sum
        intro k _
        have h := (hS (c k φ)).2
        change _ ≤ D * q k φ at h
        simpa only [he k] using h
      _ ≤ P φ := by
        rw [hPapply, ← Finset.mul_sum, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Finset.sum_nonneg fun k _ ↦ apply_nonneg _ _)
  · exact (hS (c 0 φ)).1
  · change T.traceValue = ∑' i : I F A ω, c 0 φ i.val.1
    simpa only [he 0] using htrace


omit [ν.IsHaarMeasure] in
set_option maxHeartbeats 1500000 in
/-- The orbital trace and continuous seminorm estimate apply to arbitrary Haar
normalizations on the idele class group. -/
theorem primaryOrbitalBruhat_trace (A : Finset (Place F))
    {p : ℕ} (hp : p.Prime)
    (hA : ∀ v ∈ A, v.asIdeal.under ℤ = Ideal.span {(p : ℤ)})
    (hdeg : 2 * (A.card : ℝ) ≤ s) (hs' : 1 < s) (ω : PontryaginDual (K F)) :
    ∃ P : Seminorm ℂ (BruhatCompactTest (Q F)), Continuous P ∧
      ∀ φ : BruhatCompactTest (Q F),
        ∃ T : TraceClass ((R F μ s hs A ω)ᗮ),
          T.toOperator = primaryOrbitalCompressedConvolution F μ s hs A ω
            (primaryOrbitalBruhatDensity F φ) ∧ ‖T‖ ≤ P φ ∧
          Summable (fun i : I F A ω ↦ ‖orbitalConvolutionCoefficient F μ φ.val.val
            (normOneEulerCharacter F ω) (zAt i.val.1) 0‖) ∧
          T.traceValue = ∑' i : I F A ω, orbitalConvolutionCoefficient F μ φ.val.val
            (normOneEulerCharacter F ω) (zAt i.val.1) 0 := by
  obtain ⟨η,hη,he⟩ := exists_globalClassMeasure_of_haar F μ
  letI : η.IsHaarMeasure := hη
  let σ := globalClassMeasure F η
  obtain ⟨P,hP,h⟩ := primaryOrbitalBruhat_trace_split F s hs η A hp hA hdeg hs' ω
  refine ⟨P,hP,fun φ ↦ ?_⟩
  have h' (ρ : Measure (Q F)) [ρ.IsHaarMeasure] (he' : σ = ρ) :
      ∃ T : TraceClass ((R F ρ s hs A ω)ᗮ),
        T.toOperator = primaryOrbitalCompressedConvolution F ρ s hs A ω
          (primaryOrbitalBruhatDensity F φ) ∧ ‖T‖ ≤ P φ ∧
        Summable (fun i : I F A ω ↦ ‖orbitalConvolutionCoefficient F ρ φ.val.val
          (normOneEulerCharacter F ω) (zAt i.val.1) 0‖) ∧
        T.traceValue = ∑' i : I F A ω, orbitalConvolutionCoefficient F ρ φ.val.val
          (normOneEulerCharacter F ω) (zAt i.val.1) 0 := by
    subst ρ
    obtain ⟨T,hT,hN,hSum,hTr⟩ := h φ
    have hcoe (i : I F A ω) : orbitalConvolutionSchwartzCoefficients F η ω 0 φ i.val.1 =
        orbitalConvolutionCoefficient F σ φ.val.val (normOneEulerCharacter F ω) (zAt i.val.1) 0 :=
      orbitalConvolutionSchwartzCoefficients_apply F η ω 0 φ i.val.1
    refine ⟨T,hT,hN,?_,hTr.trans (tsum_congr hcoe)⟩
    simp_rw [← hcoe]
    exact hSum
  exact h' μ he


end
end Masullo
