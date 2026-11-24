import ComplexSchwartzMonomialJets

open Filter Function Set Topology
open scoped Distributions ContDiff SchwartzMap

namespace Masullo

noncomputable section

private abbrev S := 𝓢(ℂ, ℂ)

private theorem complexTempered_kills_jets
    (T : S →L[ℂ] ℂ) (N : ℕ) (hN : testDistributionOrderLE (T.comp smoothTestToSchwartz) N)
    (hT : Distribution.IsVanishingOn (⇑T) ({0} : Set ℂ)ᶜ)
    (f : S) (hf : ∀ j ≤ N, iteratedFDeriv ℝ j (f : ℂ → ℂ) 0 = 0) :
    T f = 0 := by
  let b : ContDiffBump (0 : ℂ) := ⟨1/2, 1, by norm_num, by norm_num⟩
  let χ : ℂ → ℂ := fun z ↦ (b z : ℂ)
  have hχc : HasCompactSupport χ := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hχ : χ.HasTemperateGrowth :=
    hχc.hasTemperateGrowth (Complex.ofRealCLM.contDiff.comp b.contDiff)
  let g := SchwartzMap.smulLeftCLM ℂ χ f
  have hg : HasCompactSupport g :=
    hχc.of_isClosed_subset isClosed_closure ((SchwartzMap.tsupport_smulLeftCLM_subset _ _).trans
      inter_subset_right)
  have hloc : (g : ℂ → ℂ) =ᶠ[𝓝 0] (f : ℂ → ℂ) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1/2)] with z hz
    rw [SchwartzMap.smulLeftCLM_apply_apply hχ, show χ z = 1 by
      change ((b z : ℝ) : ℂ) = 1
      rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), Complex.ofReal_one], one_smul]
  have hs : tsupport (f-g) ⊆ ({0} : Set ℂ)ᶜ := by
    have h : (fun z ↦ f z - g z : ℂ → ℂ) =ᶠ[𝓝 0] 0 := by
      filter_upwards [hloc] with z hz
      change f z - g z = 0
      rw [hz, sub_self]
    have h₀ := notMem_tsupport_iff_eventuallyEq.mpr h
    intro z hz hz'
    have hzero : z = 0 := hz'
    subst z
    exact h₀ hz
  have hfg := hT (f-g) hs
  rw [map_sub, sub_eq_zero] at hfg
  rw [hfg]
  let gtest : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ) :=
    ⟨g, g.smooth', hg, subset_univ _⟩
  let p := ContinuousLinearMap.id ℝ ℂ
  have hplane : {z | p z = 0} = ({0} : Set ℂ) := by ext z; rfl
  have hvan : Distribution.IsVanishingOn (⇑(T.comp smoothTestToSchwartz)) {z | p z = 0}ᶜ := by
    intro u hu
    rw [hplane] at hu
    exact hT (smoothTestToSchwartz u) hu
  change (T.comp smoothTestToSchwartz) gtest = 0
  apply coordinatePlane_distribution_kills_vanishing_jets p p (fun _ ↦ rfl)
    ContinuousLinearMap.norm_id_le ContinuousLinearMap.norm_id_le _ N hN hvan
  intro z hz k hk
  change z = 0 at hz
  subst z
  change iteratedFDeriv ℝ k (g : ℂ → ℂ) 0 = 0
  exact (hloc.iteratedFDeriv ℝ k).eq_of_nhds.trans (hf k hk)

/-- The finite set of mixed jets of total order at most N. -/
def complexPointJetIndices (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N+1)).product (Finset.range (N+1))).filter (fun p ↦ p.1 + p.2 ≤ N)

@[simp] theorem mem_complexPointJetIndices (N : ℕ) (p : ℕ × ℕ) :
    p ∈ complexPointJetIndices N ↔ p.1 + p.2 ≤ N := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, h⟩

/-- A distribution of order at most N supported at zero is determined by
its mixed Wirtinger jets through order N. -/
theorem complexPointTemperedDistribution_eq_sum_WirtingerJets_of_order
    (T : S →L[ℂ] ℂ) (hT : Distribution.dsupport (⇑T) ⊆ {0})
    (N : ℕ) (hN : testDistributionOrderLE (T.comp smoothTestToSchwartz) N) :
    ∃ c : ℕ × ℕ → ℂ, ∀ f : S,
      T f = ∑ p ∈ complexPointJetIndices N, c p * complexSchwartzPointJet p.1 p.2 f := by
  classical
  have hvan := temperedDistribution_isVanishingOn_compl_of_dsupport_subset T hT
  choose u hu using fun p : ℕ × ℕ ↦ exists_complexSchwartz_single_pointJet p.1 p.2
  refine ⟨fun p ↦ T (u p), fun f ↦ ?_⟩
  let v := ∑ p ∈ complexPointJetIndices N, complexSchwartzPointJet p.1 p.2 f • u p
  have he (q : ℕ × ℕ) (hq : q ∈ complexPointJetIndices N) :
      complexSchwartzPointJet q.1 q.2 v = complexSchwartzPointJet q.1 q.2 f := by
    dsimp [v]
    rw [map_sum, Finset.sum_eq_single q]
    · rw [map_smul, hu, ite_eq_left ⟨rfl, rfl⟩, smul_eq_mul, mul_one]
    · intro p _ hp
      rw [map_smul, hu, ite_eq_right (fun h ↦ hp (Prod.ext h.1.symm h.2.symm)), smul_zero]
    · intro h
      exact (h hq).elim
  have hf : T (f - v) = 0 := by
    apply complexTempered_kills_jets T N hN hvan
    apply (complexSchwartzPointJet_vanishing_iff N _).mp
    intro a b hab
    rw [map_sub, he (a,b) ((mem_complexPointJetIndices N (a,b)).mpr hab), sub_self]
  rw [map_sub, sub_eq_zero] at hf
  rw [hf]
  dsimp [v]
  simp only [map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- A tempered distribution supported at zero on the complex Schwartz space
has a finite mixed Wirtinger expansion. -/
theorem complexPointTemperedDistribution_eq_sum_WirtingerJets
    (T : S →L[ℂ] ℂ) (hT : Distribution.dsupport (⇑T) ⊆ {0}) :
    ∃ N, ∃ c : ℕ × ℕ → ℂ, ∀ f : S,
      T f = ∑ p ∈ complexPointJetIndices N, c p * complexSchwartzPointJet p.1 p.2 f := by
  obtain ⟨N, hN⟩ := exists_order_tempered_on_smoothTests T
  exact ⟨N, complexPointTemperedDistribution_eq_sum_WirtingerJets_of_order T hT N hN⟩

/-- In a finite mixed expansion, the order bound is equivalent to the
vanishing of the coefficients above that total degree. -/
theorem complexPointTemperedDistribution_order_iff
    (T : S →L[ℂ] ℂ) (hT : Distribution.dsupport (⇑T) ⊆ {0}) (N M : ℕ)
    (c : ℕ × ℕ → ℂ)
    (he : ∀ f : S, T f = ∑ p ∈ complexPointJetIndices N, c p * complexSchwartzPointJet p.1 p.2 f) :
    testDistributionOrderLE (T.comp smoothTestToSchwartz) M ↔
      ∀ p ∈ complexPointJetIndices N, M < p.1 + p.2 → c p = 0 := by
  classical
  constructor
  · intro h p hp hMp
    obtain ⟨d, hd⟩ := complexPointTemperedDistribution_eq_sum_WirtingerJets_of_order T hT M h
    obtain ⟨f, hf⟩ := exists_complexSchwartz_single_pointJet p.1 p.2
    have hz : T f = 0 := by
      rw [hd]
      apply Finset.sum_eq_zero
      intro q hq
      have hqp : ¬ (q.1 = p.1 ∧ q.2 = p.2) := by
        intro hdiff
        have hq' := (mem_complexPointJetIndices M q).mp hq
        omega
      rw [hf, ite_eq_right hqp, mul_zero]
    rw [he, Finset.sum_eq_single p] at hz
    · simpa [hf] using hz
    · intro q _ hq
      rw [hf, ite_eq_right (fun hh ↦ hq (Prod.ext hh.1 hh.2)), mul_zero]
    · intro hpn
      exact (hpn hp).elim
  · intro h K
    refine ⟨∑ p ∈ complexPointJetIndices N, ‖c p‖, by positivity, fun f _ B hB hj ↦ ?_⟩
    change ‖T (smoothTestToSchwartz f)‖ ≤ _
    rw [he, Finset.sum_mul]
    apply (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p hp ↦ ?_))
    by_cases hp' : p.1+p.2 ≤ M
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((norm_complexSchwartzPointJet_le p.1 p.2 _).trans
        (hj _ hp' 0)) (norm_nonneg _)
    · simp [h p hp (lt_of_not_ge hp')]

end
end Masullo
