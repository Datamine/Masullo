import VectorLaurentContours

/-! The vector residue theorem for finite contour cycles. Adapted from the
Apache-2.0 RiemannMasullo proof at 4f78774. -/

open Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

/-- Paper: Cycle convention before Theorem C.5.4.1, p. 740. A cycle is a finite
formal integer combination of positively oriented simple contours. -/
abbrev ComplexContourCycle := PositiveSimpleContour →₀ ℤ

/-- Paper: Cycle convention before Theorem C.5.4.1, p. 740. The trace of a cycle
is the union of the traces of its terms with nonzero coefficients. -/
def ComplexContourCycle.trace (Γ : ComplexContourCycle) : Set ℂ :=
  ⋃ γ ∈ Γ.support, γ.val.trace

/-- Paper: (C.5.4.1), p. 741. Integration over a cycle uses the integer-weighted
sum of the contour measures. -/
def ComplexContourCycle.measure (Γ : ComplexContourCycle) : VectorMeasure ℂ ℂ :=
  Γ.sum (fun γ n ↦ n • γ.val.measure)

/-- Paper: Winding number in Theorem C.5.4.1, p. 741. The index of a cycle off its
trace is the integer-weighted sum of the indices of its constituent contours. -/
def ComplexContourCycle.index (Γ : ComplexContourCycle) (z : ℂ) : ℂ :=
  Γ.sum (fun γ n ↦ n • γ.val.index z)

/-- Paper: Cycle convention before Theorem C.5.4.1, p. 740. A cycle with one
contour and nonzero multiplicity has its trace and scales its measure and index.
Deviation: This is a sanity check for the cycle operations. -/
theorem complexContourCycle_single (γ : PositiveSimpleContour) {n : ℤ} (hn : n ≠ 0) (z : ℂ) :
    let Γ : ComplexContourCycle := Finsupp.single γ n
    Γ.trace = γ.val.trace ∧ Γ.measure = n • γ.val.measure ∧ Γ.index z = n • γ.val.index z := by
  refine ⟨?_, ?_, ?_⟩
  · simp [ComplexContourCycle.trace, Finsupp.support_single _ hn]
  · simp [ComplexContourCycle.measure, Finsupp.sum_single_index]
  · simp [ComplexContourCycle.index, Finsupp.sum_single_index]

/-- Represented complex Pettis integrals respect linear combinations.
In particular this applies to the two sides of the cycle formula on the
common no-pole domain. -/
theorem HasPettisIntegral.complexLinearCombination
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {μ : VectorMeasure ℂ ℂ} {f g : ℂ → E} {x y : E}
    (hf : HasPettisIntegral μ f x) (hg : HasPettisIntegral μ g y) (a b : ℂ) :
    HasPettisIntegral μ (a • f + b • g) (a • x + b • y) := by
  have hsmul (c : ℂ) (q : ℂ → ℂ) :
      complexMeasureIntegral μ (c • q) = c • complexMeasureIntegral μ q := by
    unfold complexMeasureIntegral VectorMeasure.integral
    apply setToFun_smul
    intro d s v
    by_cases hs : MeasurableSet s
    · change (d * v) * μ s = d * (v * μ s)
      exact mul_assoc _ _ _
    · rw [VectorMeasure.not_measurable (μ.transpose (ContinuousLinearMap.mul ℝ ℂ)) hs]
      simp
  intro ℓ
  have he : ℓ ∘ (a • f + b • g) = a • (ℓ ∘ f) + b • (ℓ ∘ g) := by
    funext w
    change ℓ (a • f w + b • g w) = a • ℓ (f w) + b • ℓ (g w)
    rw [map_add, map_smul, map_smul]
  rw [he, map_add, map_smul, map_smul, (hf ℓ).2, (hg ℓ).2, ← hsmul, ← hsmul]
  have ha := (hf ℓ).1.smul a
  have hb := (hg ℓ).1.smul b
  exact ⟨ha.add hb, (VectorMeasure.integral_add ha hb).symm⟩


section ResidueTheorem

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E]
  [QuasiCompleteSpace ℂ E]
variable {Ω D : Set ℂ} {f : ℂ → E}

/-- The closure of the set on which a null-homologous cycle has nonzero index
is a compact subset of its domain. -/
private theorem ComplexContourCycle.compact_index_support (Γ : ComplexContourCycle)
    (htrace : Γ.trace ⊆ Ω) (hnull : ∀ x ∉ Ω, Γ.index x = 0) :
    IsCompact (tsupport Γ.index) ∧ tsupport Γ.index ⊆ Ω := by
  classical
  have ho : ∀ᶠ x in cocompact ℂ, Γ.index x = 0 := by
    filter_upwards [Γ.support.eventually_all.mpr fun γ _ ↦ γ.eventually_index_zero] with x hx
    exact Finset.sum_eq_zero fun γ hγ ↦ by simp [hx γ hγ]
  refine ⟨hasCompactSupport_iff_eventuallyEq.mpr (by rwa [coclosedCompact_eq_cocompact]), ?_⟩
  intro x hx
  by_contra h
  have hloc := Γ.support.eventually_all.mpr fun γ hγ ↦ γ.eventually_index_eq (x := x)
    (fun hxt ↦ h (htrace (mem_iUnion₂.mpr ⟨γ, hγ, hxt⟩)))
  apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx
  filter_upwards [hloc] with y hy
  exact (Finset.sum_congr rfl fun γ hγ ↦ congrArg (Γ γ • ·) (hy γ hγ)).trans (hnull x h)

/-- A regular point has a Taylor expansion and hence cannot have negative order. -/
private theorem IsVectorMeromorphicOn.not_pole_of_regular (hf : IsVectorMeromorphicOn f Ω D)
    {x : ℂ} (hx : x ∈ Ω \ D) : ¬ IsVectorPoleAt f x := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hf.2.2.1.mem_nhds hx)
  have hw := vectorHolomorphicOn_weaklyHolomorphic Metric.isOpen_ball (hf.2.2.2.1.mono hsub)
  obtain ⟨b, hb⟩ := (weaklyHolomorphicOn_iff_taylor Metric.isOpen_ball).mp hw x (Metric.mem_ball_self hr)
  have he : EqOn f (fun w ↦ (w - x) ^ (0 : ℕ) • f w) (Metric.ball x r \ {x}) := by
    intro _ _; simp
  have ha := hasVectorLaurentSeriesAt_of_taylor hr hb he
  rintro ⟨k, hk, a, hL, hne, -⟩
  rw [hL.coeff_unique ha] at hne
  simp [hk.not_ge] at hne

private theorem ComplexContourCycle.finite_poles (Γ : ComplexContourCycle)
    (hf : IsVectorMeromorphicOn f Ω D) (htrace : Γ.trace ⊆ Ω)
    (hnull : ∀ x ∉ Ω, Γ.index x = 0) :
    {x : Ω | IsVectorPoleAt f x ∧ Γ.index x ≠ 0}.Finite := by
  obtain ⟨hK, hsub⟩ := Γ.compact_index_support htrace hnull
  let K := tsupport Γ.index
  have hKD : (K \ (Ω \ D)).Finite :=
    (hK.inter_right hf.2.2.1.isClosed_compl).finite (hf.2.1.mono (fun x hx ↦ by
      by_contra hn
      exact hx.2 ⟨hsub hx.1, hn⟩))
  refine (hKD.preimage Subtype.val_injective.injOn).subset ?_
  intro x hx
  exact ⟨subset_tsupport _ hx.2, fun h ↦ hf.not_pole_of_regular h hx.1⟩

/-- Integration against the cycle measure sums the ordinary contour integrals
with their integer multiplicities. -/
private theorem ComplexContourCycle.scalarIntegral_eq_sum (Γ : ComplexContourCycle)
    {q : ℂ → ℂ} (hq : ContinuousOn q Γ.trace) :
    Integrable q Γ.measure.variation ∧
      complexMeasureIntegral Γ.measure q =
        ∑ γ ∈ Γ.support, (Γ γ : ℂ) * complexMeasureIntegral γ.val.measure q := by
  have hi γ (hγ : γ ∈ Γ.support) : γ.val.measure.Integrable q :=
    (γ.val.scalarIntegral_eq_intervalIntegral (hq.mono (subset_iUnion₂_of_subset γ hγ Subset.rfl))).1
  have hm : Γ.measure = ∑ γ ∈ Γ.support, (Γ γ : ℝ) • γ.val.measure := by
    exact Finset.sum_congr rfl fun γ _ ↦ (Int.cast_smul_eq_zsmul ℝ (Γ γ) γ.val.measure).symm
  have hscaled γ (hγ : γ ∈ Γ.support) := (hi γ hγ).smul_vectorMeasure (Γ γ : ℝ)
  refine ⟨?_, ?_⟩
  · change Γ.measure.Integrable q
    rw [hm]
    exact VectorMeasure.Integrable.finsetSum_vectorMeasure hscaled
  · simp only [complexMeasureIntegral, hm, VectorMeasure.integral_finsetSum_vectorMeasure hscaled,
      VectorMeasure.integral_smul_vectorMeasure, Complex.real_smul, Complex.ofReal_intCast]

/-- An isolating contour gives the residue of any representative which agrees
with the original function off the exceptional set. -/
private theorem IsVectorMeromorphicOn.exists_residue_contour (hf : IsVectorMeromorphicOn f Ω D)
    (hΩ : IsOpen Ω) {g : ℂ → E} (hgf : EqOn g f (Ω \ D)) (z : Ω) :
    ∃ γ : PositiveSimpleContour, γ.val.trace ⊆ Ω \ D ∧ γ.val.index z = 1 ∧
      (∀ x ∉ Ω \ (D ∩ {w | IsVectorPoleAt f w}), x ≠ z → γ.val.index x = 0) ∧
      ∀ φ : StrongDual ℂ E, complexMeasureIntegral γ.val.measure (φ ∘ g) =
        (2 * (Real.pi : ℂ) * Complex.I) * φ (vectorResidue (hf.existsUnique_laurentSeries hΩ z.2).exists) := by
  obtain ⟨_, r, _, hr, hsub, _, _⟩ := hf.exists_cleared z.2
  obtain ⟨γ, htr, hin, hnb⟩ := exists_positiveSimpleContour_mem_nhds
    Metric.isOpen_ball (Metric.mem_ball_self (x := (z : ℂ)) hr)
  have href : z.val ∈ γ.interior := mem_of_mem_nhds hnb
  have ht : γ.val.trace ⊆ Ω \ D := fun w hw ↦
    hsub ⟨htr hw, ne_of_mem_of_not_mem hw href.1⟩
  have hi {w : ℂ} (hw : w ∈ γ.interior) (hne : w ≠ z) : w ∈ Ω \ D :=
    hsub ⟨hin hw, hne⟩
  have hΩi : γ.interior ⊆ Ω := fun w hw ↦ by
    rcases eq_or_ne w (z : ℂ) with rfl | hne
    · exact z.2
    · exact (hi hw hne).1
  obtain ⟨G, hGf, _, hG⟩ := hasPettisIntegral_vectorResidue hΩ hf γ
    (ht.trans sdiff_subset) hΩi href (fun _ hw ↦ hf.not_pole_of_regular (ht hw))
    (fun _ hw hp ↦ by_contra fun hne ↦ hf.not_pole_of_regular (hi hw hne) hp)
  refine ⟨γ, ht, href.2, ?_, fun φ ↦ ?_⟩
  · intro x hx hne
    have hnot (h : x ∈ Ω \ D) := hx ⟨h.1, fun h' ↦ h.2 h'.1⟩
    have hxt : x ∉ γ.val.trace := fun h ↦ hnot (ht h)
    exact (γ.property.2 x hxt).resolve_right fun h ↦ hnot (hi ⟨hxt, h⟩ hne)
  · have he := (hG φ).2
    change φ (_ • _) = complexMeasureIntegral γ.val.measure (φ ∘ G) at he
    rw [map_smul, smul_eq_mul] at he
    rw [he]
    apply VectorMeasure.integral_congr_ae
    filter_upwards [γ.val.ae_mem_trace] with w hw using congrArg φ ((hgf (ht hw)).trans (hGf (ht hw)).symm)

/-- Paper: Theorem C.5.4.1, p. 741. The normalized cycle integral equals the
finite sum of residues weighted by winding numbers.
Deviation: Null homology uses the planar winding-number condition outside Ω.
A representative extending across removable points supplies the contour values.
The identity is pointwise on meromorphic functions satisfying the pole avoidance condition. -/
theorem vectorResidueTheorem (hΩ : IsOpen Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (Γ : ComplexContourCycle) (htrace : Γ.trace ⊆ Ω)
    (hnull : ∀ z ∉ Ω, Γ.index z = 0)
    (havoid : ∀ z ∈ Γ.trace, ¬ IsVectorPoleAt f z) :
    ∃ (g : ℂ → E) (S : Finset Ω),
      EqOn g f (Ω \ D) ∧ DifferentiableOn ℂ g (Ω \ {z | IsVectorPoleAt f z}) ∧
      (∀ z : Ω, z ∈ S ↔ IsVectorPoleAt f z ∧ Γ.index z ≠ 0) ∧
      HasPettisIntegral Γ.measure g
        ((2 * (Real.pi : ℂ) * Complex.I) •
          ∑ z ∈ S, Γ.index z • vectorResidue (hf.existsUnique_laurentSeries hΩ z.property).exists) :=
  by
  classical
  let U := Ω \ (D ∩ {z | IsVectorPoleAt f z})
  obtain ⟨hU, g, heq, hg⟩ := hf.exists_holomorphic_representative hΩ
  have htr : Γ.trace ⊆ U := fun x hx ↦ ⟨htrace hx, fun hp ↦ havoid x hx hp.2⟩
  let S := (Γ.finite_poles hf htrace hnull).toFinset
  have hS (x : Ω) : x ∈ S ↔ IsVectorPoleAt f x ∧ Γ.index x ≠ 0 := Set.Finite.mem_toFinset _
  refine ⟨g, S, heq, hg.mono (fun x hx ↦ ⟨hx.1, fun hp ↦ hx.2 hp.2⟩), hS, ?_⟩
  choose σ hσtr hσone hσzero hσint using hf.exists_residue_contour hΩ heq
  -- Subtract an isolating contour around each pole with its original winding number.
  let γ : Γ.support ⊕ S → PositiveSimpleContour := Sum.elim Subtype.val (fun z ↦ σ z.val)
  let c : Γ.support ⊕ S → ℂ := Sum.elim (fun i ↦ (Γ i.val : ℂ)) (fun z ↦ -Γ.index z.val)
  have ht (i : Γ.support ⊕ S) (_ : i ∈ Finset.univ) : (γ i).val.trace ⊆ U := by
    cases i with
    | inl i => exact (subset_iUnion₂_of_subset i.val i.2 Subset.rfl).trans htr
    | inr z => exact fun w hw ↦ ⟨(hσtr _ hw).1, fun hp ↦ (hσtr _ hw).2 hp.1⟩
  have hind (x : ℂ) (hx : x ∉ U) : ∑ i, c i * (γ i).val.index x = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [c, γ, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
    rw [Finset.sum_coe_sort Γ.support (fun i ↦ (Γ i : ℂ) * i.val.index x),
      Finset.sum_coe_sort S (fun z ↦ Γ.index z * (σ z).val.index x)]
    have hfirst : (∑ i ∈ Γ.support, (Γ i : ℂ) * i.val.index x) = Γ.index x := by
      simp [ComplexContourCycle.index, Finsupp.sum, zsmul_eq_mul]
    rw [hfirst, ← sub_eq_add_neg, sub_eq_zero]
    by_cases hxΩ : x ∈ Ω
    · let z : Ω := ⟨x, hxΩ⟩
      have hp : IsVectorPoleAt f x := by by_contra hn; exact hx ⟨hxΩ, fun h ↦ hn h.2⟩
      rw [Finset.sum_eq_single z, hσone, mul_one]
      · intro y _ hy
        rw [hσzero y x hx (fun h ↦ hy (Subtype.ext h.symm)), mul_zero]
      · intro hz
        have h0 : Γ.index x = 0 := by by_contra h; exact hz ((hS z).mpr ⟨hp, h⟩)
        simp [z, h0]
    · rw [hnull x hxΩ]
      exact (Finset.sum_eq_zero fun z _ ↦ by rw [hσzero z x hx (fun h ↦ hxΩ (h ▸ z.2)), mul_zero]).symm
  let C : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let res (z : Ω) := vectorResidue (hf.existsUnique_laurentSeries hΩ z.2).exists
  have hsc (φ : StrongDual ℂ E) := vectorHolomorphicOn_weaklyHolomorphic hU hg φ
  have hm (φ : StrongDual ℂ E) := Γ.scalarIntegral_eq_sum ((hsc φ).continuousOn.mono htr)
  intro φ
  refine ⟨(hm φ).1, ?_⟩
  change φ (C • ∑ z ∈ S, Γ.index z • res z) = complexMeasureIntegral Γ.measure (φ ∘ g)
  have h := sum_scalarIntegral_eq_zero Finset.univ γ c hU ht hind (hsc φ)
  rw [Fintype.sum_sum_type] at h
  simp only [c, γ, Sum.elim_inl, Sum.elim_inr, neg_mul,
    Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero, hσint] at h
  rw [Finset.sum_coe_sort Γ.support (fun i ↦ (Γ i : ℂ) *
    complexMeasureIntegral i.val.measure (φ ∘ g)),
    Finset.sum_coe_sort S (fun z ↦ Γ.index z * (C * φ (res z)))] at h
  rw [(hm φ).2, h, map_smul, smul_eq_mul, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ ↦ by rw [map_smul, smul_eq_mul]; ring

end ResidueTheorem

end

end Masullo
