import ElementarySchwartz
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

open Filter Function Set Topology
open scoped ContDiff Uniformity ENNReal

namespace Masullo

noncomputable section

private abbrev Fibre (m n : ℕ) :=
  EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)

private abbrev Derivative (m n k : ℕ) := Fibre m n [×k]→L[ℝ] ℂ

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F]
  [DiscreteTopology F] [Finite F]

private theorem elementary_cauchy_tail {u : ℕ → ElementarySchwartz m n r F}
    (hu : CauchySeq u) (i : ElementarySchwartzIndex m n r) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ j ≥ N, ∀ l ≥ N, elementarySchwartzSeminorm i (u j - u l) < ε := by
  let p : Seminorm ℂ (ElementarySchwartz m n r F) := elementarySchwartzSeminorm i
  have hp : Continuous p := elementarySchwartz_withSeminorms.continuous_seminorm i
  have hU : {z : ElementarySchwartz m n r F × ElementarySchwartz m n r F |
      p (z.1 - z.2) < ε} ∈ 𝓤 (ElementarySchwartz m n r F) := by
    rw [uniformity_eq_comap_nhds_zero_swapped]
    have hV : {f | p f < ε} ∈ 𝓝 (0 : ElementarySchwartz m n r F) :=
      hp.continuousAt (x := 0) (Iio_mem_nhds (by simpa using hε))
    exact preimage_mem_comap hV
  exact cauchySeq_iff.mp hu _ hU

private theorem fibre_coordinate_norm_le (v : Fibre m n) (j : Fin m ⊕ Fin n) :
    ‖(elementaryFibreBasis m n).repr v j‖ ≤ ‖v‖ := by
  cases j with
  | inl i =>
    rw [elementaryFibreBasis, Module.Basis.prod_repr_inl]
    change ‖v.1 i‖ ≤ ‖v‖
    exact (PiLp.norm_apply_le v.1 i).trans (norm_fst_le v)
  | inr i =>
    rw [elementaryFibreBasis, Module.Basis.prod_repr_inr]
    change ‖v.2 i‖ ≤ ‖v‖
    exact (PiLp.norm_apply_le v.2 i).trans (norm_snd_le v)

/-- It suffices to control the multilinear map on the finitely many tuples of
standard fibre basis vectors. -/
private theorem elementary_derivative_norm_le {k : ℕ} (D : Derivative m n k)
    (c : ℝ) (hc : 0 ≤ c)
    (hD : ∀ t : Fin k → Fin m ⊕ Fin n, ‖D (fun i ↦ elementaryFibreBasis m n (t i))‖ ≤ c) :
    ‖D‖ ≤ (Fintype.card (Fin k → Fin m ⊕ Fin n) : ℝ) * c := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  let B := elementaryFibreBasis m n
  have hsum : D v = ∑ t : Fin k → Fin m ⊕ Fin n,
      (∏ i, B.repr (v i) (t i)) • D (fun i ↦ B (t i)) := by
    change D.toMultilinearMap v = _
    conv_lhs => rw [show v = (fun i ↦ ∑ j, B.repr (v i) j • B j) from
      funext fun i ↦ (B.sum_repr (v i)).symm]
    rw [D.toMultilinearMap.map_sum]
    simp only [D.toMultilinearMap.map_smul_univ, ContinuousMultilinearMap.coe_coe]
  rw [hsum]
  calc
    _ ≤ ∑ t : Fin k → Fin m ⊕ Fin n,
        ‖(∏ i, B.repr (v i) (t i)) • D (fun i ↦ B (t i))‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin k → Fin m ⊕ Fin n, (∏ i, ‖v i‖) * c := by
      apply Finset.sum_le_sum
      intro t _
      rw [norm_smul, norm_prod]
      exact mul_le_mul
        (Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ fibre_coordinate_norm_le _ _))
        (hD t) (norm_nonneg _) (by positivity)
    _ = _ := by simp [nsmul_eq_mul]; ring

private theorem elementaryPartial_sub (f g : ElementarySchwartz m n r F)
    (β : Fin m → ℕ) (γ : Fin n → ℕ) (x : Fibre m n) (a : Fin r → ℤ) (b : F) :
    elementaryPartial (f - g).val β γ x a b =
      elementaryPartial f.val β γ x a b - elementaryPartial g.val β γ x a b := by
  change elementaryPartial (f.val - g.val) β γ x a b = _
  rw [sub_eq_add_neg f.val, ← neg_one_smul ℂ g.val]
  have hg (a : Fin r → ℤ) (b : F) :
      ContDiff ℝ ∞ (fun x ↦ ((-1 : ℂ) • g.val) (elementaryCover x a b)) := by
    simpa only [Pi.smul_apply] using (g.property.1 a b).const_smul (-1 : ℂ)
  rw [elementaryPartial_add f.property.1 hg, elementaryPartial_smul (-1) g.property.1]
  simp [sub_eq_add_neg]

private theorem smooth_fibre_cauchy {u : ℕ → ElementarySchwartz m n r F}
    (hu : CauchySeq u) (k : ℕ) (a : Fin r → ℤ) (b : F) :
    UniformCauchySeqOn (fun j ↦ iteratedFDeriv ℝ k (fun x ↦ u j (elementaryCover x a b)))
      atTop univ := by
  classical
  let T := Fin k → Fin m ⊕ Fin n
  choose β γ hβ using fun t : T ↦ elementaryIteratedFDeriv_basis (r := r) (F := F) t
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  let c := ε / ((Fintype.card T : ℝ) + 1)
  have hc : 0 < c := div_pos hε (by positivity)
  choose N hN using fun t : T ↦ elementary_cauchy_tail hu (0, β t, γ t, 0) hc
  let M := Finset.univ.sup N
  refine ⟨M, fun j hj l hl x _ ↦ ?_⟩
  let D : Derivative m n k :=
    iteratedFDeriv ℝ k (fun x ↦ u j (elementaryCover x a b)) x -
      iteratedFDeriv ℝ k (fun x ↦ u l (elementaryCover x a b)) x
  have hD (t : T) : ‖D (fun i ↦ elementaryFibreBasis m n (t i))‖ ≤ c := by
    have hj' : N t ≤ j := (Finset.le_sup (Finset.mem_univ t)).trans hj
    have hl' : N t ≤ l := (Finset.le_sup (Finset.mem_univ t)).trans hl
    have h := monomial_partial_le_seminorm (0 : Fin m → ℕ) (β t) (γ t)
      (0 : Fin r → ℕ) (u j - u l) x a b
    have h' : ‖elementaryPartial (u j - u l).val (β t) (γ t) x a b‖ ≤
        elementarySchwartzSeminorm (0, β t, γ t, 0) (u j - u l) := by
      simpa only [Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul] using h
    change ‖(iteratedFDeriv ℝ k (fun z ↦ u j (elementaryCover z a b)) x -
      iteratedFDeriv ℝ k (fun z ↦ u l (elementaryCover z a b)) x)
        (fun i ↦ elementaryFibreBasis m n (t i))‖ ≤ c
    rw [ContinuousMultilinearMap.sub_apply,
      hβ t (u j).val a b ((u j).property.1 a b), hβ t (u l).val a b ((u l).property.1 a b)]
    rw [← elementaryPartial_sub]
    exact h'.trans (hN t j hj' l hl').le
  rw [dist_eq_norm]
  have hNorm := elementary_derivative_norm_le D c hc.le hD
  refine hNorm.trans_lt ?_
  change (Fintype.card T : ℝ) * c < ε
  have hunit : ((Fintype.card T : ℝ) + 1) * c = ε := by
    dsimp [c]
    field_simp
  nlinarith

private theorem fibre_taylor_limit {u : ℕ → Fibre m n → ℂ}
    (hs : ∀ j, ContDiff ℝ ∞ (u j)) {p : (k : ℕ) → Fibre m n → Derivative m n k}
    (hU : ∀ k, TendstoUniformly (fun j ↦ iteratedFDeriv ℝ k (u j)) (p k) atTop) :
    HasFTaylorSeriesUpTo ∞ (fun x ↦ (p 0 x).curry0) (fun x k ↦ p k x) := by
  refine ⟨fun _ ↦ rfl, ?_, ?_⟩
  · intro k hk x
    refine hasFDerivAt_of_tendstoUniformly
      (f' := fun j x ↦ (iteratedFDeriv ℝ (k + 1) (u j) x).curryLeft)
      (g' := fun x ↦ (p (k + 1) x).curryLeft) ?_ ?_ (hU k).tendsto_at x
    · let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Fibre m n) ℂ
      exact curry.isometry.uniformContinuous.comp_tendstoUniformly (hU (k + 1))
    · intro j y
      exact (hs j).ftaylorSeries.fderiv k hk y
  · intro k hk
    exact (hU k).continuous
      (Eventually.of_forall (fun j ↦ (hs j).ftaylorSeries.cont k hk)).frequently

private def elementaryWeightedPartial (i : ElementarySchwartzIndex m n r)
    (f : ElementaryLCAModel m n r F → ℂ) (x : Fibre m n) (a : Fin r → ℤ) (b : F) : ℂ :=
  ((∏ j, (x.1 j : ℂ) ^ i.1 j) * (∏ j, (a j : ℂ) ^ i.2.2.2 j)) *
    elementaryPartial f i.2.1 i.2.2.1 x a b

private theorem elementaryWeightedPartial_sub (i : ElementarySchwartzIndex m n r)
    (f g : ElementarySchwartz m n r F) (x : Fibre m n) (a : Fin r → ℤ) (b : F) :
    elementaryWeightedPartial i (f - g).val x a b =
      elementaryWeightedPartial i f.val x a b - elementaryWeightedPartial i g.val x a b := by
  unfold elementaryWeightedPartial
  rw [elementaryPartial_sub, mul_sub]

/-- A Cauchy sequence converges smoothly on each lifted fibre. Its weighted
derivative bounds pass to the limit uniformly across the discrete fibres. -/
theorem completeSpace_elementarySchwartz : CompleteSpace (ElementarySchwartz m n r F) := by
  classical
  let E := ElementarySchwartz m n r F
  let hp := elementarySchwartz_withSeminorms (m := m) (n := n) (r := r) (F := F)
  letI : FirstCountableTopology E := hp.firstCountableTopology
  have : (𝓤 E).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero E]
    infer_instance
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  let d (j k : ℕ) (a : Fin r → ℤ) (b : F) :=
    iteratedFDeriv ℝ k (fun x ↦ u j (elementaryCover x a b))
  choose p hp0 using fun k a b x ↦
    cauchySeq_tendsto_of_complete ((smooth_fibre_cauchy hu k a b).cauchySeq (mem_univ x))
  have hU (k : ℕ) (a : Fin r → ℤ) (b : F) :
      TendstoUniformly (fun j ↦ d j k a b) (p k a b) atTop :=
    tendstoUniformlyOn_univ.mp
      ((smooth_fibre_cauchy hu k a b).tendstoUniformlyOn_of_tendsto fun x _ ↦ hp0 k a b x)
  let t (y : ElementaryLCAModel m n r F) :=
    (elementaryCover_surjective y.2.2.1 y.2.2.2 y.1 y.2.1).choose
  let g (y : ElementaryLCAModel m n r F) :=
    (p 0 y.2.2.1 y.2.2.2 (y.1, t y)).curry0
  have ht (y : ElementaryLCAModel m n r F) : elementaryCover (y.1, t y) y.2.2.1 y.2.2.2 = y :=
    (elementaryCover_surjective y.2.2.1 y.2.2.2 y.1 y.2.1).choose_spec
  have hzero (x : Fibre m n) (a : Fin r → ℤ) (b : F) :
      Tendsto (fun j ↦ u j (elementaryCover x a b)) atTop (𝓝 (p 0 a b x).curry0) := by
    have h := ((continuousMultilinearCurryFin0 ℝ (Fibre m n) ℂ).continuous.tendsto
      (p 0 a b x)).comp ((hU 0 a b).tendsto_at x)
    simpa only [Function.comp_def, d, continuousMultilinearCurryFin0_apply,
      iteratedFDeriv_zero_apply, ContinuousMultilinearMap.curry0] using h
  have hPoint (y : ElementaryLCAModel m n r F) :
      Tendsto (fun j ↦ u j y) atTop (𝓝 (g y)) := by
    simpa only [ht y, g] using hzero (y.1, t y) y.2.2.1 y.2.2.2
  have hgEq (a : Fin r → ℤ) (b : F) : (fun x ↦ g (elementaryCover x a b)) =
      fun x ↦ (p 0 a b x).curry0 :=
    funext fun x ↦ tendsto_nhds_unique (hPoint _) (hzero x a b)
  have hSeries (a : Fin r → ℤ) (b : F) :
      HasFTaylorSeriesUpTo ∞ (fun x ↦ g (elementaryCover x a b))
        (fun x k ↦ p k a b x) := by
    rw [hgEq]
    exact fibre_taylor_limit (fun j ↦ (u j).property.1 a b) (fun k ↦ hU k a b)
  have hPartial (β : Fin m → ℕ) (γ : Fin n → ℕ) (x : Fibre m n)
      (a : Fin r → ℤ) (b : F) :
      Tendsto (fun j ↦ elementaryPartial (u j).val β γ x a b) atTop
        (𝓝 (elementaryPartial g β γ x a b)) := by
    unfold elementaryPartial
    dsimp only
    rw [← (hSeries a b).eq_iteratedFDeriv (by exact_mod_cast le_top) x]
    exact (ContinuousMultilinearMap.apply ℝ _ ℂ _).continuous.tendsto _ |>.comp
      ((hU _ a b).tendsto_at x)
  have hclose (i : ElementarySchwartzIndex m n r) {ε : ℝ} (hε : 0 < ε) :
      ∃ N, ∀ j ≥ N, ∀ x a b, ‖elementaryWeightedPartial i (u j).val x a b -
        elementaryWeightedPartial i g x a b‖ ≤ ε := by
    obtain ⟨N, hN⟩ := elementary_cauchy_tail hu i hε
    refine ⟨N, fun j hj x a b ↦ ?_⟩
    have hlim : Tendsto (fun l : ℕ ↦ elementaryWeightedPartial i (u l).val x a b)
        atTop (𝓝 (elementaryWeightedPartial i g x a b)) :=
      tendsto_const_nhds.mul (hPartial i.2.1 i.2.2.1 x a b)
    refine le_of_tendsto (tendsto_const_nhds.sub hlim).norm ?_
    filter_upwards [eventually_ge_atTop N] with l hl
    change ‖elementaryWeightedPartial i (u j).val x a b -
      elementaryWeightedPartial i (u l).val x a b‖ ≤ ε
    rw [← elementaryWeightedPartial_sub]
    exact (monomial_partial_le_seminorm i.1 i.2.1 i.2.2.1 i.2.2.2
      (u j - u l) x a b).trans (hN j hj l hl).le
  let f : E := (⟨g, fun a b ↦ (hSeries a b).contDiff, by
    intro i
    obtain ⟨N, hN⟩ := hclose i zero_lt_one
    refine lt_of_le_of_lt (b := ENNReal.ofReal (elementarySchwartzSeminorm i (u N) + 1))
      (iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_) ENNReal.ofReal_lt_top
    change ‖elementaryWeightedPartial i g x a b‖ₑ ≤ _
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    exact (norm_le_norm_add_norm_sub (elementaryWeightedPartial i (u N).val x a b)
      (elementaryWeightedPartial i g x a b)).trans
        (add_le_add (monomial_partial_le_seminorm i.1 i.2.1 i.2.2.1 i.2.2.2 (u N) x a b)
          (hN N le_rfl x a b))⟩ : elementarySchwartzSubmodule m n r F)
  refine ⟨f, (hp.tendsto_nhds_atTop _ _).mpr ?_⟩
  intro i ε hε
  obtain ⟨N, hN⟩ := hclose i (half_pos hε)
  refine ⟨N, fun j hj ↦ lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  change (elementarySchwartzBound (u j - f).val i).toReal ≤ ε / 2
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_)).trans_eq
      (ENNReal.toReal_ofReal (half_pos hε).le)
  change ‖elementaryWeightedPartial i (u j - f).val x a b‖ₑ ≤ _
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  rw [elementaryWeightedPartial_sub]
  exact hN j hj x a b

/-- Paper: D.1.3.5(2), p. 752. The elementary Schwartz space is Fréchet. -/
theorem elementarySchwartz_isFrechet :
    T2Space (ElementarySchwartz m n r F) ∧ PolynormableSpace ℂ (ElementarySchwartz m n r F) ∧
      TopologicalSpace.MetrizableSpace (ElementarySchwartz m n r F) ∧ CompleteSpace (ElementarySchwartz m n r F) := by
  let E := ElementarySchwartz m n r F
  let hp := elementarySchwartz_withSeminorms (m := m) (n := n) (r := r) (F := F)
  letI : T2Space E := elementarySchwartz_t2
  letI : FirstCountableTopology E := hp.firstCountableTopology
  letI : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact ⟨inferInstance, inferInstance, UniformSpace.metrizableSpace, completeSpace_elementarySchwartz⟩

end
end Masullo
