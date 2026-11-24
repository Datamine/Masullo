import ModulatedSobolevMellin

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped TensorProduct ENNReal

namespace Masullo

noncomputable section

variable {K : Type*} [MeasurableSpace K] (μ : Measure K) [SFinite μ]

omit [SFinite μ] in
private theorem lpTwoRadialSupport_mem_iff_indicator {ν : Measure ℝ}
    (U : Set ℝ) (f : Lp ℂ 2 (μ.prod ν)) :
    f ∈ lpTwoRadialSupport μ ν U ↔
      (f : K × ℝ → ℂ) =ᵐ[μ.prod ν] (Prod.snd ⁻¹' U).indicator (f : K × ℝ → ℂ) := by
  change (∀ᵐ p ∂μ.prod ν, p.2 ∉ U → f p = 0) ↔ _
  constructor
  · intro h
    filter_upwards [h] with p hp
    by_cases hU : p ∈ Prod.snd ⁻¹' U
    · exact (indicator_of_mem hU _).symm
    · exact (hp hU).trans (indicator_of_notMem hU _).symm
  · intro h
    filter_upwards [h] with p hp hU
    exact hp.trans (indicator_of_notMem (show p ∉ Prod.snd ⁻¹' U from hU) _)

omit [SFinite μ] in
private theorem lpTwoRadialSupport_eq_of_ae {ν : Measure ℝ} [SFinite ν]
    {U V : Set ℝ} (h : ∀ᵐ x ∂ν, x ∈ U ↔ x ∈ V) :
    lpTwoRadialSupport μ ν U = lpTwoRadialSupport μ ν V := by
  have he := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae h
  ext f
  change (∀ᵐ p ∂μ.prod ν, p.2 ∉ U → f p = 0) ↔ (∀ᵐ p ∂μ.prod ν, p.2 ∉ V → f p = 0)
  constructor
  · intro hU
    filter_upwards [hU, he] with p hp hUV hn
    exact hp (fun hmem => hn (hUV.mp hmem))
  · intro hV
    filter_upwards [hV, he] with p hp hUV hn
    exact hp (fun hmem => hn (hUV.mpr hmem))

omit [SFinite μ] in
/-- The supported row on the product weighted space. The closed endpoint
cutoffs of the manuscript agree almost everywhere with the open intervals. -/
theorem modulatedSobolev_sourceExact (b s c : ℝ) (hc : c ≤ 0) :
    let ν := stripMeasure b b s
    let L := lpTwoRadialSupport μ ν (Ioo c 0)
    let M := lpTwoRadialSupport μ ν (Ioi c)
    let R := lpTwoRadialSupport μ ν (Ioi 0)
    ∃ (i : L →L[ℂ] M) (p : M →L[ℂ] R),
      (∀ f, (i f).val = f.val) ∧
      (∀ f, ((p f).val : K × ℝ → ℂ) =ᵐ[μ.prod ν]
        (Prod.snd ⁻¹' Ici 0).indicator (f.val : K × ℝ → ℂ)) ∧
      Injective i ∧ IsClosed (range i) ∧ Exact i p ∧ Surjective p ∧ IsOpenMap p := by
  intro ν L M R
  have ha : ∀ r : ℝ, ∀ᵐ x ∂ν, x ≠ r := fun r =>
    (amplitudeMeasure_absolutelyContinuous (volume : Measure ℝ)
      (stripSobolevAmplitude b b s)).ae_le ((volume : Measure ℝ).ae_ne r)
  have hnull : μ.prod ν ((Prod.snd : K × ℝ → ℝ) ⁻¹' {0}) = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr
      ((Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae (ha 0))
  obtain ⟨L', M', R', i, p, hL, hM, hR, hi, hp, hclosed⟩ :=
    lpTwo_cutoff_exact (μ.prod ν) Prod.snd measurable_snd c hc hnull
  have hL' : L' = lpTwoRadialSupport μ ν (Icc c 0) := by
    ext f
    exact (Set.ext_iff.mp hL f).trans (lpTwoRadialSupport_mem_iff_indicator μ (Icc c 0) f).symm
  have hM' : M' = lpTwoRadialSupport μ ν (Ici c) := by
    ext f
    exact (Set.ext_iff.mp hM f).trans (lpTwoRadialSupport_mem_iff_indicator μ (Ici c) f).symm
  have hR' : R' = lpTwoRadialSupport μ ν (Ici 0) := by
    ext f
    exact (Set.ext_iff.mp hR f).trans (lpTwoRadialSupport_mem_iff_indicator μ (Ici 0) f).symm
  have hLC : (lpTwoRadialSupport μ ν (Icc c 0)) = L := by
    apply lpTwoRadialSupport_eq_of_ae
    filter_upwards [ha c, ha 0] with x hxc hx0
    simp only [mem_Icc, mem_Ioo]
    exact ⟨fun h => ⟨lt_of_le_of_ne h.1 (Ne.symm hxc), lt_of_le_of_ne h.2 hx0⟩,
      fun h => ⟨h.1.le, h.2.le⟩⟩
  have hMC : (lpTwoRadialSupport μ ν (Ici c)) = M := by
    apply lpTwoRadialSupport_eq_of_ae
    filter_upwards [ha c] with x hxc
    simp only [mem_Ici, mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h (Ne.symm hxc), le_of_lt⟩
  have hRC : (lpTwoRadialSupport μ ν (Ici 0)) = R := by
    apply lpTwoRadialSupport_eq_of_ae
    filter_upwards [ha 0] with x hx0
    simp only [mem_Ici, mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h (Ne.symm hx0), le_of_lt⟩
  have eL := hL'.trans hLC
  have eM := hM'.trans hMC
  have eR := hR'.trans hRC
  clear hL' hM' hR' hLC hMC hRC hL hM hR
  subst L' M' R'
  exact ⟨i, p, hi, hp, hclosed⟩

private def completedTmul {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] (u : E) (v : F) :
    Completion (E ⊗[ℂ] F) := (u ⊗ₜ[ℂ] v : E ⊗[ℂ] F)

set_option maxHeartbeats 2400000 in
/-- The weighted product cutoff row and the row on completed Mellin Hilbert
tensors are short exact, with the Mellin isometries as vertical arrows. -/
theorem modulatedSobolev_mellinCutoffDiagram (b : ℝ) (N : ℕ) (c : ℝ) (hc : c ≤ 0) :
    let ν := stripMeasure b b (2 * (N : ℝ))
    let L := lpTwoRadialSupport μ ν (Ioo c 0)
    let M := lpTwoRadialSupport μ ν (Ioi c)
    let R := lpTwoRadialSupport μ ν (Ioi 0)
    let L' := Completion (Lp ℂ 2 μ ⊗[ℂ] supportedMellinLineCompletion b N (Ioo c 0))
    let M' := Completion (Lp ℂ 2 μ ⊗[ℂ] supportedMellinLineCompletion b N (Ioi c))
    let R' := Completion (Lp ℂ 2 μ ⊗[ℂ] supportedMellinLineCompletion b N (Ioi 0))
    let L₀ := supportedMellinLineCompletion b N (Ioo c 0)
    let M₀ := supportedMellinLineCompletion b N (Ioi c)
    let R₀ := supportedMellinLineCompletion b N (Ioi 0)
    ∃ (i : L →L[ℂ] M) (p : M →L[ℂ] R) (i' : L' →L[ℂ] M') (p' : M' →L[ℂ] R'),
      (∀ f, (i f).val = f.val) ∧
      (∀ f, ((p f).val : K × ℝ → ℂ) =ᵐ[μ.prod ν]
        (Prod.snd ⁻¹' Ici 0).indicator (f.val : K × ℝ → ℂ)) ∧
      (∀ f, modulatedSupportedMellinEquiv μ b N isOpen_Ioi (i f) =
        i' (modulatedSupportedMellinEquiv μ b N isOpen_Ioo f)) ∧
      (∀ f, modulatedSupportedMellinEquiv μ b N isOpen_Ioi (p f) =
        p' (modulatedSupportedMellinEquiv μ b N isOpen_Ioi f)) ∧
      (Injective i ∧ IsClosed (range i) ∧ Exact i p ∧ Surjective p ∧ IsOpenMap p) ∧
      (Injective i' ∧ IsClosed (range i') ∧ Exact i' p' ∧ Surjective p' ∧ IsOpenMap p') ∧
      ∃ (j : L₀ →L[ℂ] M₀) (q : M₀ →L[ℂ] R₀),
        (∀ (v : L₀) (z : {z : ℂ // z.re < b}),
          lowerLineRealization b N c hc (j v) z = compactLineRealization b N c v z.val) ∧
        (∀ (u : Lp ℂ 2 μ) (v : L₀), i' (completedTmul u v) = completedTmul u (j v)) ∧
        (∀ (u : Lp ℂ 2 μ) (v : M₀), p' (completedTmul u v) = completedTmul u (q v)) ∧
        ∃ P : StripSobolev b b (2 * (N : ℝ)) →L[ℂ] StripSobolev b b (2 * (N : ℝ)),
          (∀ f, (P f : ℝ → ℂ) =ᵐ[volume] (Ioi 0).indicator (f : ℝ → ℂ)) ∧
          ∀ f : supportedSobolevCompletion b b (2 * (N : ℝ)) (Ioi c),
            ((supportedMellinLineEquiv b N (Ioi 0)).symm (q
              (supportedMellinLineEquiv b N (Ioi c) f))).val = P f.val := by
  intro ν L M R L' M' R' L₀ M₀ R₀
  obtain ⟨i, p, hi, hp, hinj, hclosed, hex, hsurj, hopen⟩ :=
    modulatedSobolev_sourceExact μ b (2 * (N : ℝ)) c hc
  let el : L ≃L[ℂ] L' :=
    (modulatedSupportedMellinEquiv μ b N isOpen_Ioo).toContinuousLinearEquiv
  let em : M ≃L[ℂ] M' :=
    (modulatedSupportedMellinEquiv μ b N isOpen_Ioi).toContinuousLinearEquiv
  let er : R ≃L[ℂ] R' :=
    (modulatedSupportedMellinEquiv μ b N isOpen_Ioi).toContinuousLinearEquiv
  let i' := em.toContinuousLinearMap.comp (i.comp el.symm.toContinuousLinearMap)
  let p' := er.toContinuousLinearMap.comp (p.comp em.symm.toContinuousLinearMap)
  have hi' (f : L') : i' f = em (i (el.symm f)) := rfl
  have hp' (f : M') : p' f = er (p (em.symm f)) := rfl
  refine ⟨i, p, i', p', hi, hp, ?_, ?_, ⟨hinj, hclosed, hex, hsurj, hopen⟩, ?_, ?_⟩
  · intro f
    change em (i f) = i' (el f)
    rw [hi', el.symm_apply_apply]
  · intro f
    change er (p f) = p' (em f)
    rw [hp', em.symm_apply_apply]
  · refine ⟨em.injective.comp (hinj.comp el.symm.injective), ?_, ?_,
      er.surjective.comp (hsurj.comp em.symm.surjective),
      er.toHomeomorph.isOpenMap.comp (hopen.comp em.symm.toHomeomorph.isOpenMap)⟩
    · have he : range i' = em '' range i := by
        ext f
        constructor
        · rintro ⟨g, rfl⟩
          exact ⟨i (el.symm g), ⟨el.symm g, rfl⟩, (hi' g).symm⟩
        · rintro ⟨g, ⟨f, rfl⟩, rfl⟩
          exact ⟨el f, by rw [hi', el.symm_apply_apply]⟩
      rw [he]
      exact em.toHomeomorph.isClosedMap _ hclosed
    · intro f
      rw [hp', ← er.map_zero, er.injective.eq_iff, hex]
      constructor
      · rintro ⟨v, hv⟩
        exact ⟨el v, by rw [hi', el.symm_apply_apply, hv, em.apply_symm_apply]⟩
      · rintro ⟨v, rfl⟩
        exact ⟨el.symm v, by rw [hi', em.symm_apply_apply]⟩

  · obtain ⟨_, _, _, _, _, _, _, j₀, q₀, j, q, hj₀, hq₀, hj, hq, hborder, _, _⟩ :=
      hardySobolev_paleyWiener_exact_sequence b N c hc
    let s : ℝ := 2 * (N : ℝ)
    let AL := modulatedSupportedTensorEquiv μ b s (U := Ioo c 0) isOpen_Ioo
    let AM := modulatedSupportedTensorEquiv μ b s (U := Ioi c) isOpen_Ioi
    let AR := modulatedSupportedTensorEquiv μ b s (U := Ioi 0) isOpen_Ioi
    let jl := supportedMellinLineEquiv b N (Ioo c 0)
    let jm := supportedMellinLineEquiv b N (Ioi c)
    let jr := supportedMellinLineEquiv b N (Ioi 0)
    have hi₀ (u : Lp ℂ 2 μ) (v : supportedSobolevCompletion b b s (Ioo c 0)) :
        i (AL (completedTmul u v)) = AM (completedTmul u (j₀ v)) := by
      apply Subtype.ext
      rw [hi]
      simp only [AL, AM, completedTmul, modulatedSupportedTensorEquiv_tmul, hj₀]
    refine ⟨j, q, hborder, ?_, ?_, ?_⟩
    · intro u v
      obtain ⟨w, rfl⟩ := jl.surjective v
      have hL : el (AL (completedTmul u w)) = completedTmul u (jl w) :=
        modulatedSupportedMellinEquiv_tmul μ b N isOpen_Ioo u w
      have hM : em (AM (completedTmul u (j₀ w))) = completedTmul u (jm (j₀ w)) :=
        modulatedSupportedMellinEquiv_tmul μ b N isOpen_Ioi u (j₀ w)
      rw [← hL, hi', el.symm_apply_apply, hi₀, hM, hj]
    · intro u v
      obtain ⟨w, rfl⟩ := jm.surjective v
      have hcut : p (AM (completedTmul u w)) = AR (completedTmul u (q₀ w)) := by
        apply Subtype.ext
        have hsrc := hp (AM (completedTmul u w))
        have hs : (AM (completedTmul u w)).val = lpTwoProduct u w.val :=
          modulatedSupportedTensorEquiv_tmul μ b s isOpen_Ioi u w
        have ht : (AR (completedTmul u (q₀ w))).val = lpTwoProduct u (q₀ w).val :=
          modulatedSupportedTensorEquiv_tmul μ b s isOpen_Ioi u (q₀ w)
        rw [ht]
        apply Lp.ext
        rw [hs] at hsrc
        have hac := amplitudeMeasure_absolutelyContinuous (volume : Measure ℝ)
          (stripSobolevAmplitude b b s)
        have hν := Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)
        filter_upwards [hsrc, lpTwoProduct_ae u w.val, lpTwoProduct_ae u (q₀ w).val,
          hν.ae_eq_comp (hac.ae_le (hq₀ w)),
          hν.ae (hac.ae_le ((volume : Measure ℝ).ae_ne 0))] with x hx hs' ht' hq' hzero
        change (q₀ w).val x.2 = (Ioi (0 : ℝ)).indicator (w.val : ℝ → ℂ) x.2 at hq'
        rw [hx, ht', hq']
        by_cases hx' : 0 < x.2
        · rw [indicator_of_mem (show x ∈ Prod.snd ⁻¹' Ici (0 : ℝ) from hx'.le),
            indicator_of_mem (show x.2 ∈ Ioi (0 : ℝ) from hx'), hs']
        · have hlt : x.2 < 0 := lt_of_le_of_ne (le_of_not_gt hx') hzero
          rw [indicator_of_notMem (show x ∉ Prod.snd ⁻¹' Ici (0 : ℝ) from not_le.mpr hlt),
            indicator_of_notMem (show x.2 ∉ Ioi (0 : ℝ) from hx'), mul_zero]
      have hM : em (AM (completedTmul u w)) = completedTmul u (jm w) :=
        modulatedSupportedMellinEquiv_tmul μ b N isOpen_Ioi u w
      have hR : er (AR (completedTmul u (q₀ w))) = completedTmul u (jr (q₀ w)) :=
        modulatedSupportedMellinEquiv_tmul μ b N isOpen_Ioi u (q₀ w)
      rw [← hM, hp', em.symm_apply_apply, hcut, hR, hq]
    · obtain ⟨P, _, _, _, _, hP⟩ := supportedSobolevCompletion_eq_cutoff b b s (U := Ioi 0) isOpen_Ioi
      refine ⟨P, hP, fun f => ?_⟩
      rw [← hq f, LinearIsometryEquiv.symm_apply_apply]
      exact Lp.ext ((amplitudeMeasure_absolutelyContinuous volume
        (stripSobolevAmplitude b b s)).ae_le ((hq₀ f).trans (hP f.val).symm))

end

end Masullo
