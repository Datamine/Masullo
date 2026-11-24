import VectorMeromorphic
import VectorHolomorphyDerivatives
import Mathlib.Analysis.Analytic.Order

open Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
  [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E]

/-- Corrected formula in C.5.3.3(3). Clearing the pole by the full
power shifts the residue to Taylor index one less than that power. -/
theorem HasVectorLaurentSeriesAt.residue_eq_cleared_derivative
    {f g : ℂ → E} {z : ℂ} {a : ℤ → E}
    (ha : HasVectorLaurentSeriesAt f z a) {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r)
    (hg : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (ℓ ∘ g) (Metric.ball z r))
    (heq : EqOn g (fun w ↦ (w - z) ^ n • f w) (Metric.ball z r \ {z})) :
    a (-1) = ((n - 1).factorial : ℂ)⁻¹ • (deriv^[n - 1] g) z := by
  have hderiv := (weaklyHolomorphicOn_iff_all_derivatives Metric.isOpen_ball).mp hg
  have hz : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hj : (((n - 1 : ℕ) : ℤ) - n) = -1 := by omega
  apply (weakBidualEval_isEmbedding E).injective
  change (weakBidualEval E (a (-1)) : Module.Dual ℂ (StrongDual ℂ E)) =
    (weakBidualEval E (((n - 1).factorial : ℂ)⁻¹ • (deriv^[n - 1] g) z) :
      Module.Dual ℂ (StrongDual ℂ E))
  refine LinearMap.ext fun ℓ ↦ ?_
  change ℓ (a (-1)) = ℓ (((n - 1).factorial : ℂ)⁻¹ • (deriv^[n - 1] g) z)
  have hcoeff := ha.coeff_eq_derivative_of_cleared ℓ n (n - 1) hr (hg ℓ) (by
    intro w hw
    simp only [Function.comp_apply, heq hw, map_smul, smul_eq_mul])
  rw [hj, eval_iteratedDeriv_eq Metric.isOpen_ball hderiv ℓ (n - 1) hz] at hcoeff
  simp only [hcoeff, map_smul, smul_eq_mul, div_eq_inv_mul, Function.comp_apply]

/-! The Laurent and contour results below adapt the Apache-2.0
RiemannMasullo proofs at 4f78774. -/

variable {Ω D : Set ℂ} {f : ℂ → E} {z : ℂ}

/-- Paper: Definition C.5.3.1, p. 739. A meromorphic pair is holomorphic off a
discrete exceptional set, and at each exceptional point a power of the local
coordinate times the function extends holomorphically.
Deviation: Uses the paper's parenthetical pole-clearing criterion. The punctured
domain is explicitly open, so the exceptional set is relatively closed. -/
def IsVectorMeromorphicOn (f : ℂ → E) (Ω D : Set ℂ) : Prop :=
  D ⊆ Ω ∧ IsDiscrete D ∧ IsOpen (Ω \ D) ∧ DifferentiableOn ℂ f (Ω \ D) ∧
    ∀ z ∈ D, ∃ (n : ℕ) (r : ℝ) (g : ℂ → E),
      0 < r ∧ Metric.ball z r \ {z} ⊆ Ω \ D ∧ DifferentiableOn ℂ g (Metric.ball z r) ∧
      EqOn g (fun w ↦ (w - z) ^ n • f w) (Metric.ball z r \ {z})

/-- Paper: Definition C.5.3.1(1), p. 739. A finite order is the least Laurent
exponent with nonzero coefficient.
Deviation: This is a relation for finite order. The zero germ has no finite order. -/
def HasVectorMeromorphicOrderAt (f : ℂ → E) (z : ℂ) (k : ℤ) : Prop :=
  ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a ∧ a k ≠ 0 ∧ ∀ j < k, a j = 0

/-- Paper: Definition C.5.3.1(2), p. 739. A point is a pole if its Laurent order
is strictly negative. -/
def IsVectorPoleAt (f : ℂ → E) (z : ℂ) : Prop :=
  ∃ k : ℤ, k < 0 ∧ HasVectorMeromorphicOrderAt f z k

/-- A holomorphic function is weakly holomorphic. -/
theorem vectorHolomorphicOn_weaklyHolomorphic {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ → E} (hg : DifferentiableOn ℂ g U) : WeaklyHolomorphicOn g U := by
  intro φ v hv
  have h := vectorHolomorphic_hasDerivAt_comp hg hU φ ⟨v, hv⟩
  exact h.differentiableAt.differentiableWithinAt

/-- Uniform convergence in the target is preserved by multiplication with a scalar
function bounded on the set. -/
private theorem tendstoUniformlyOn_bounded_smul {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → E} {g : ℂ → E} {s : Set ℂ} (h : TendstoUniformlyOn F g l s)
    (c : ℂ → ℂ) (hB : ∃ B : ℝ, ∀ w ∈ s, ‖c w‖ ≤ B) :
    TendstoUniformlyOn (fun i w ↦ c w • F i w) (fun w ↦ c w • g w) l s := by
  apply tendstoUniformlyOn_of_forall_continuous_seminorm
  intro q hq ε hε
  obtain ⟨B, hB⟩ := hB
  have hM : 0 < max B 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hsmall := h {p : E × E | p.2 - p.1 ∈ q.ball 0 (ε / max B 1)}
    (by
      rw [uniformity_eq_comap_nhds_zero E]
      exact preimage_mem_comap (q.ball_mem_nhds hq (div_pos hε hM)))
  filter_upwards [hsmall] with i hi w hw
  have hlt : q (F i w - g w) < ε / max B 1 := by
    simpa only [mem_ofPred_eq, Seminorm.mem_ball_zero] using hi w hw
  rw [← smul_sub, map_smul_eq_mul]
  calc
    _ ≤ max B 1 * q (F i w - g w) :=
      mul_le_mul_of_nonneg_right ((hB w hw).trans (le_max_left _ _)) (apply_nonneg q _)
    _ < ε := (lt_div_iff₀' hM).mp hlt

/-- A holomorphic Taylor expansion, divided by a power of the local coordinate,
is a Laurent expansion of the cleared function. -/
theorem hasVectorLaurentSeriesAt_of_taylor {g : ℂ → E} {b : ℕ → E} {n : ℕ} {r : ℝ}
    (hr : 0 < r)
    (hb : ∀ ρ : ℝ, 0 < ρ → Metric.closedBall z ρ ⊆ Metric.ball z r →
      TendstoUniformlyOn (fun m w ↦ ∑ k ∈ Finset.range m, (w - z) ^ k • b k)
        g atTop (Metric.closedBall z ρ))
    (heq : EqOn g (fun w ↦ (w - z) ^ n • f w) (Metric.ball z r \ {z})) :
    HasVectorLaurentSeriesAt f z
      (fun k : ℤ ↦ if -(n : ℤ) ≤ k then b (k + n).toNat else 0) := by
  let N : ℤ := -(n : ℤ)
  let a : ℤ → E := fun k ↦ if N ≤ k then b (k - N).toNat else 0
  have ha_eq : a = fun k : ℤ ↦ if -(n : ℤ) ≤ k then b (k + n).toNat else 0 := by
    funext k
    simp only [a, N, sub_eq_add_neg, neg_neg]
  rw [← ha_eq]
  refine ⟨N, r, hr, fun k hk ↦ by simp [a, hk.not_ge], fun K hK hKcomp ↦ ?_⟩
  obtain ⟨ρ, hρ0, hρr, hKρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ K ⊆ Metric.closedBall z ρ := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨r / 2, by positivity, by linarith, by simp⟩
    · obtain ⟨w, hw, hmax⟩ := hKcomp.exists_isMaxOn hne
        (continuous_id.dist continuous_const).continuousOn
      exact ⟨dist w z, dist_pos.mpr (hK hw).2, Metric.mem_ball.mp (hK hw).1,
        fun x hx ↦ Metric.mem_closedBall.mpr (hmax hx)⟩
  have huni := (hb ρ hρ0 (Metric.closedBall_subset_ball hρr)).mono hKρ
  let c : ℂ → ℂ := fun w ↦ (w - z) ^ N
  have hcne : ∀ w ∈ K, w - z ≠ 0 := fun w hw ↦ sub_ne_zero.mpr (hK hw).2
  have hB : ∃ B : ℝ, ∀ w ∈ K, ‖c w‖ ≤ B :=
    ⟨_, hKcomp.exists_bound_of_continuousOn ((continuousOn_id.sub continuousOn_const).zpow₀ _ fun w hw ↦ Or.inl (hcne w hw)) |>.choose_spec⟩
  have hsmul := tendstoUniformlyOn_bounded_smul huni c hB
  have hpartial : ∀ m : ℕ, EqOn
      (fun w ↦ c w • ∑ j ∈ Finset.range m, (w - z) ^ j • b j)
      (fun w ↦ ∑ j ∈ Finset.range m, (w - z) ^ (N + (j : ℤ)) • a (N + (j : ℤ))) K := by
    intro m w hw
    show c w • (∑ j ∈ Finset.range m, (w - z) ^ j • b j) =
      ∑ j ∈ Finset.range m, (w - z) ^ (N + (j : ℤ)) • a (N + (j : ℤ))
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hle : N ≤ N + (j : ℤ) := by omega
    have hidx : (N + (j : ℤ) - N).toNat = j := by
      rw [add_sub_cancel_left, Int.toNat_natCast]
    simp only [a, ite_eq_left hle, hidx, smul_smul]
    rw [← zpow_natCast (w - z) j, zpow_add₀ (hcne w hw)]
  have hlim : EqOn (fun w ↦ c w • g w) f K := by
    intro w hw
    show c w • g w = f w
    have hgw : g w = (w - z) ^ n • f w := heq ⟨(hK hw).1, (hK hw).2⟩
    have hne := hcne w hw
    rw [hgw]
    change (w - z) ^ N • ((w - z) ^ n • f w) = f w
    rw [smul_smul, ← zpow_natCast (w - z) n, ← zpow_add₀ hne]
    have hexp : N + (n : ℤ) = 0 := by simp [N]
    rw [hexp, zpow_zero, one_smul]
  exact TendstoUniformlyOn.congr_right
    (TendstoUniformlyOn.congr hsmul (Eventually.of_forall hpartial)) hlim

/-- Paper: Definition C.5.3.1, p. 739. Every point of the domain of a meromorphic
pair has a unique local Laurent expansion in the original target.
Deviation: Includes the ordinary Taylor expansion at points outside the exceptional set. -/
theorem IsVectorMeromorphicOn.existsUnique_laurentSeries (hΩ : IsOpen Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (hz : z ∈ Ω) :
    ∃! a : ℤ → E, HasVectorLaurentSeriesAt f z a := by
  have : IsOpen Ω := hΩ
  suffices ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a by
    obtain ⟨a, ha⟩ := this
    exact existsUnique_of_exists_of_unique ⟨a, ha⟩ fun a₁ a₂ ha₁ ha₂ ↦
      HasVectorLaurentSeriesAt.coeff_unique ha₁ ha₂
  by_cases hzD : z ∈ D
  · obtain ⟨n, r, g, hr, -, hg, heq⟩ := hf.2.2.2.2 z hzD
    have hweak : WeaklyHolomorphicOn g (Metric.ball z r) :=
      vectorHolomorphicOn_weaklyHolomorphic Metric.isOpen_ball hg
    obtain ⟨b, hb⟩ :=
      (weaklyHolomorphicOn_iff_taylor Metric.isOpen_ball).mp
      hweak z (Metric.mem_ball_self hr)
    exact ⟨_, hasVectorLaurentSeriesAt_of_taylor hr hb heq⟩
  · have hopen : IsOpen (Ω \ D) := hf.2.2.1
    obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_ball.mem_iff.mp (hopen.mem_nhds ⟨hz, hzD⟩)
    have hg : DifferentiableOn ℂ f (Metric.ball z r) := hf.2.2.2.1.mono hsub
    have hweak : WeaklyHolomorphicOn f (Metric.ball z r) :=
      vectorHolomorphicOn_weaklyHolomorphic Metric.isOpen_ball hg
    obtain ⟨b, hb⟩ :=
      (weaklyHolomorphicOn_iff_taylor Metric.isOpen_ball).mp
      hweak z (Metric.mem_ball_self hr)
    have heq : EqOn f (fun w ↦ (w - z) ^ (0 : ℕ) • f w) (Metric.ball z r \ {z}) := by
      intro w _
      simp
    exact ⟨_, hasVectorLaurentSeriesAt_of_taylor hr hb heq⟩

/-- Paper: Coefficient notation in Lemma C.5.3.2, p. 740. A coefficient is read
from the local Laurent expansion, with existence supplied as evidence. -/
def vectorLaurentCoeff (h : ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a) (k : ℤ) : E :=
  Classical.choose h k

/-- If the Laurent series has a nonzero negative term, its first nonzero term gives a pole. -/
private theorem HasVectorLaurentSeriesAt.eq_zero_of_not_pole {a : ℤ → E}
    (ha : HasVectorLaurentSeriesAt f z a) (hz : ¬ IsVectorPoleAt f z) {k : ℤ} (hk : k < 0) :
    a k = 0 := by
  classical
  by_contra hne
  obtain ⟨N, _, _, hzero, _⟩ := (show HasVectorLaurentSeriesAt f z a from ha)
  obtain ⟨m, hm, hmin⟩ := Int.exists_least_of_bdd (P := fun j ↦ a j ≠ 0)
    ⟨N, fun j hj ↦ le_of_not_gt fun h ↦ hj (hzero j h)⟩ ⟨k, hne⟩
  exact hz ⟨m, (hmin k hne).trans_lt hk, ⟨a, ha, hm, fun j hj ↦ by
    by_contra hj'
    exact hj.not_ge (hmin j hj')⟩⟩

/-- At a removable point, each scalar evaluation extends across the center with
value equal to the scalar evaluation of the Laurent coefficient at zero. -/
private theorem HasVectorLaurentSeriesAt.exists_analyticAt_of_not_pole {a : ℤ → E}
    (ha : HasVectorLaurentSeriesAt f z a) (hz : ¬ IsVectorPoleAt f z)
    {h : ℂ → E} {s : ℝ} (hs : 0 < s) (hh : DifferentiableOn ℂ h (Metric.ball z s))
    {n : ℕ} (heq : EqOn h (fun w ↦ (w - z) ^ n • f w) (Metric.ball z s \ {z}))
    (φ : StrongDual ℂ E) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q z ∧ q z = φ (a 0) ∧ q =ᶠ[𝓝[≠] z] φ ∘ f := by
  let b := φ ∘ h
  have hb : DifferentiableOn ℂ b (Metric.ball z s) := fun w hw ↦
    (vectorHolomorphic_hasDerivAt_comp hh Metric.isOpen_ball φ ⟨w, hw⟩).differentiableAt.differentiableWithinAt
  have hbe : EqOn b (fun w ↦ (w - z) ^ n * φ (f w)) (Metric.ball z s \ {z}) := by
    intro w hw
    simp [b, heq hw, smul_eq_mul]
  have hbz := hb.analyticAt (Metric.ball_mem_nhds z hs)
  have hord : (n : ENat) ≤ analyticOrderAt b z := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hbz).mpr
    intro j hj
    have hj' : (j : ℤ) - n < 0 := by omega
    have hcoeff := ha.coeff_eq_derivative_of_cleared φ n j hs hb hbe
    rw [ha.eq_zero_of_not_pole hz hj', map_zero] at hcoeff
    exact (div_eq_zero_iff.mp hcoeff.symm).resolve_right (by exact_mod_cast Nat.factorial_ne_zero j)
  obtain ⟨q, hq, hqeq⟩ := (natCast_le_analyticOrderAt hbz).mp hord
  obtain ⟨t, ht, hball⟩ := Metric.mem_nhds_iff.mp
    (hq.eventually_analyticAt.and (hqeq.and (Metric.ball_mem_nhds z hs)))
  have hdiff : DifferentiableOn ℂ q (Metric.ball z t) :=
    fun w hw ↦ (hball hw).1.differentiableAt.differentiableWithinAt
  have hqf : EqOn q (φ ∘ f) (Metric.ball z t \ {z}) := by
    intro w hw
    apply mul_left_cancel₀ (pow_ne_zero n (sub_ne_zero.mpr (show w ≠ z from hw.2)))
    exact ((hball hw.1).2.1.symm).trans (hbe ⟨(hball hw.1).2.2, hw.2⟩)
  refine ⟨q, hq, ?_, ?_⟩
  · symm
    simpa using ha.coeff_eq_derivative_of_cleared φ 0 0 ht hdiff (by
      intro w hw
      simpa using hqf hw)
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z ht),
      self_mem_nhdsWithin] with w hw hwz
    exact hqf ⟨hw, hwz⟩

/-- Every point in the domain has a pole-clearing power on a disc whose puncture
lies in the original domain of holomorphy. -/
theorem IsVectorMeromorphicOn.exists_cleared (hf : IsVectorMeromorphicOn f Ω D)
    (hz : z ∈ Ω) :
    ∃ (n : ℕ) (r : ℝ) (h : ℂ → E),
      0 < r ∧ Metric.ball z r \ {z} ⊆ Ω \ D ∧ DifferentiableOn ℂ h (Metric.ball z r) ∧
      EqOn h (fun w ↦ (w - z) ^ n • f w) (Metric.ball z r \ {z}) := by
  obtain ⟨_, _, hopen, hhol, hclear⟩ := hf
  by_cases hzD : z ∈ D
  · exact hclear z hzD
  · obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ⟨hz, hzD⟩)
    exact ⟨0, r, f, hr, sdiff_subset.trans hball, hhol.mono hball, fun w _ ↦ by simp⟩

/-- Filling each removable exceptional point with the constant Laurent coefficient
gives a holomorphic representative on the open complement of the exceptional poles. -/
theorem IsVectorMeromorphicOn.exists_holomorphic_representative (hΩ : IsOpen Ω)
    (hf : IsVectorMeromorphicOn f Ω D) :
    let U := Ω \ (D ∩ {w | IsVectorPoleAt f w})
    IsOpen U ∧ ∃ g : ℂ → E, EqOn g f (Ω \ D) ∧ DifferentiableOn ℂ g U := by
  classical
  intro U
  obtain ⟨hDΩ, _, hopen, hhol, hclear⟩ := (show IsVectorMeromorphicOn f Ω D from hf)
  have hsub : Ω \ D ⊆ U := fun _ hw ↦ ⟨hw.1, fun hp ↦ hw.2 hp.1⟩
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun w hw ↦ by
    by_cases hwD : w ∈ D
    · obtain ⟨_, r, _, hr, hball, _, _⟩ := hclear w hwD
      apply mem_of_superset (Metric.ball_mem_nhds w hr)
      intro u hu
      rcases eq_or_ne u w with rfl | huw
      · exact hw
      · exact hsub (hball ⟨hu, huw⟩)
    · exact mem_of_superset (hopen.mem_nhds ⟨hw.1, hwD⟩) hsub
  let a (w : ℂ) (hw : w ∈ D) : ℤ → E := (hf.existsUnique_laurentSeries hΩ (hDΩ hw)).exists.choose
  let g (w : ℂ) := if hw : w ∈ D then a w hw 0 else f w
  have hgf : EqOn g f (Ω \ D) := fun w hw ↦ dite_eq_right hw.2
  refine ⟨hU, g, hgf, differentiableOn_of_weaklyHolomorphicOn hU ?_⟩
  intro φ w hw
  apply DifferentiableAt.differentiableWithinAt
  by_cases hwD : w ∈ D
  · obtain ⟨n, r, h, hr, hball, hh, heq⟩ := hclear w hwD
    have ha : HasVectorLaurentSeriesAt f w (a w hwD) := Classical.choose_spec (ExistsUnique.exists
      (hf.existsUnique_laurentSeries hΩ (hDΩ hwD)))
    obtain ⟨q, hq, hqval, hqf⟩ := ha.exists_analyticAt_of_not_pole
      (fun hp ↦ hw.2 ⟨hwD, hp⟩) hr hh heq φ
    apply hq.differentiableAt.congr_of_eventuallyEq
    filter_upwards [eventually_nhdsWithin_iff.mp hqf, Metric.ball_mem_nhds w hr] with u hu hub
    rcases eq_or_ne u w with rfl | huw
    · simpa [g, hwD] using hqval.symm
    · rw [Function.comp_apply, hgf (hball ⟨hub, huw⟩)]
      exact (hu huw).symm
  · have hw' : w ∈ Ω \ D := ⟨hw.1, hwD⟩
    apply (vectorHolomorphic_hasDerivAt_comp hhol hopen φ ⟨w, hw'⟩).differentiableAt.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hw'] with u hu
    exact congrArg φ (hgf hu)

/-- Paper: Lemma C.5.3.2, p. 740. The Laurent coefficient is the normalized
Pettis contour integral against the reciprocal power of the local coordinate.
Deviation: Restores interior containment from the cited Theorem C.5.2.4.
An extension across removable exceptional points supplies the contour values. -/
theorem hasPettisIntegral_laurentCoeff (hΩ : IsOpen Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (γ : PositiveSimpleContour)
    (htrace : γ.val.trace ⊆ Ω) (hinterior : γ.interior ⊆ Ω) (hz : z ∈ γ.interior)
    (havoid : ∀ w ∈ γ.val.trace, ¬ IsVectorPoleAt f w)
    (honly : ∀ w ∈ γ.interior, IsVectorPoleAt f w → w = z) (k : ℤ) :
    ∃ g : ℂ → E, EqOn g f (Ω \ D) ∧
      DifferentiableOn ℂ g (Ω \ {w | IsVectorPoleAt f w}) ∧
      HasPettisIntegral γ.val.measure (fun w ↦ ((w - z) ^ (k + 1))⁻¹ • g w)
        ((2 * (Real.pi : ℂ) * Complex.I) •
          vectorLaurentCoeff (hf.existsUnique_laurentSeries hΩ (hinterior hz)).exists k) := by
  classical
  let U := Ω \ (D ∩ {w | IsVectorPoleAt f w})
  obtain ⟨hU, g, hgf, hg⟩ : IsOpen U ∧ ∃ g, EqOn g f (Ω \ D) ∧ DifferentiableOn ℂ g U :=
    hf.exists_holomorphic_representative hΩ
  refine ⟨g, hgf, hg.mono (fun w hw ↦ ⟨hw.1, fun hp ↦ hw.2 hp.2⟩), ?_⟩
  have htraceU : γ.val.trace ⊆ U := fun w hw ↦ ⟨htrace hw, fun hp ↦ havoid w hw hp.2⟩
  obtain ⟨n, r, h, hr, hpunct, hh, hclear⟩ := hf.exists_cleared (hinterior hz)
  let V := U ∪ Metric.ball z r
  have hV : IsOpen V := hU.union Metric.isOpen_ball
  have htr : γ.val.trace ⊆ V := htraceU.trans subset_union_left
  have hint : γ.interior ⊆ V := by
    intro w hw
    rcases eq_or_ne w z with rfl | hwz
    · exact Or.inr (Metric.mem_ball_self hr)
    · exact Or.inl ⟨hinterior hw, fun hp ↦ hwz (honly w hw hp.2)⟩
  let a := (hf.existsUnique_laurentSeries hΩ (hinterior hz)).exists.choose
  have ha : HasVectorLaurentSeriesAt f z a := Classical.choose_spec
    (hf.existsUnique_laurentSeries hΩ (hinterior hz)).exists
  let m := n + k.natAbs
  let j := (k + (m : ℤ)).toNat
  have hj : (j : ℤ) - (m : ℤ) = k := by dsimp [j, m]; omega
  let μ := γ.val.measure
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hscalar (φ : StrongDual ℂ E) :
      Integrable (fun w ↦ ((w - z) ^ (k + 1))⁻¹ * φ (g w)) μ.variation ∧
      complexMeasureIntegral μ (fun w ↦ ((w - z) ^ (k + 1))⁻¹ * φ (g w)) = c * φ (a k) := by
    -- The extra power ensures the shifted exponent is a natural number for every `k`.
    let q (w : ℂ) := (w - z) ^ k.natAbs * φ (h w)
    let p (w : ℂ) := (w - z) ^ m * φ (g w)
    let Q := update p z (q z)
    have hQq : EqOn Q q (Metric.ball z r) := by
      intro w hw
      rcases eq_or_ne w z with rfl | hwz
      · exact update_self _ _ _
      · have hw' : w ∈ Metric.ball z r \ {z} := ⟨hw, hwz⟩
        rw [show Q w = p w from update_of_ne hwz _ _]
        simp [p, q, m, pow_add, hclear hw', hgf (hpunct hw'), smul_eq_mul, mul_assoc, mul_left_comm]
    have hdiff (f₀ : ℂ → E) {S : Set ℂ} (hS : IsOpen S) (hf₀ : DifferentiableOn ℂ f₀ S)
        (l : ℕ) : DifferentiableOn ℂ (fun w ↦ (w - z) ^ l * φ (f₀ w)) S := by
      apply ((differentiableOn_id.sub_const z).pow l).mul
      intro w hw
      exact (vectorHolomorphic_hasDerivAt_comp hf₀ hS φ ⟨w, hw⟩).differentiableAt.differentiableWithinAt
    have hQball : DifferentiableOn ℂ Q (Metric.ball z r) :=
      (hdiff h Metric.isOpen_ball hh _).congr hQq
    have hQV : DifferentiableOn ℂ Q V := by
      intro w hw
      by_cases hwball : w ∈ Metric.ball z r
      · exact (hQball.differentiableAt (Metric.isOpen_ball.mem_nhds hwball)).differentiableWithinAt
      · have hwU : w ∈ U := hw.resolve_right hwball
        have hwz : w ≠ z := fun he ↦ hwball (he ▸ Metric.mem_ball_self hr)
        apply DifferentiableAt.differentiableWithinAt
        apply ((hdiff g hU hg m).differentiableAt (hU.mem_nhds hwU)).congr_of_eventuallyEq
        filter_upwards [isOpen_ne.mem_nhds hwz] with u hu
        exact update_of_ne hu _ _
    have hcoeff := ha.coeff_eq_derivative_of_cleared φ m j hr hQball (by
      intro w hw
      simp only [Q, update_of_ne (show w ≠ z from hw.2), p, hgf (hpunct hw)])
    rw [hj] at hcoeff
    have hker : (fun w ↦ ((w - z) ^ (j + 1))⁻¹ * Q w) =ᵐ[γ.val.measure.variation]
        fun w ↦ ((w - z) ^ (k + 1))⁻¹ * φ (g w) := by
      filter_upwards [γ.val.ae_mem_trace] with w hw
      have hwz := ne_of_mem_of_not_mem hw hz.1
      rw [show Q w = p w from update_of_ne hwz _ _]
      dsimp only [p]
      rw [← mul_assoc, laurentKernel_mul_pow (sub_ne_zero.mpr hwz), hj, ← zpow_neg]
      congr 2
      omega
    obtain ⟨hi, heq⟩ := γ.scalarIntegral_cauchy_derivative hV htr hint hQV hz j
    refine ⟨hi.congr hker, ?_⟩
    have hcongr : complexMeasureIntegral μ (fun w ↦ ((w - z) ^ (j + 1))⁻¹ * Q w) =
        complexMeasureIntegral μ (fun w ↦ ((w - z) ^ (k + 1))⁻¹ * φ (g w)) :=
      VectorMeasure.integral_congr_ae hker
    rw [← hcongr, heq, hcoeff]
    simp only [c, div_eq_mul_inv]
    ring
  intro φ
  refine ⟨?_, ?_⟩
  · change Integrable (fun w ↦ φ (((w - z) ^ (k + 1))⁻¹ • g w)) μ.variation
    simpa only [map_smul, smul_eq_mul, Function.comp_apply] using (hscalar φ).1
  · change φ (c • a k) = complexMeasureIntegral μ (fun w ↦ φ (((w - z) ^ (k + 1))⁻¹ • g w))
    simpa only [map_smul, smul_eq_mul] using (hscalar φ).2.symm

/-- Paper: (C.5.3.5), p. 740. The residue is the coefficient of exponent minus one. -/
def vectorResidue (h : ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a) : E :=
  vectorLaurentCoeff h (-1)

/-- A regular germ contributes zero to the residue sum, even when its
center belongs to the declared exceptional set. -/
theorem vectorResidue_eq_zero_of_not_pole
    (h : ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a)
    (hz : ¬ IsVectorPoleAt f z) : vectorResidue h = 0 :=
  h.choose_spec.eq_zero_of_not_pole hz (by norm_num)

/-- Adding the pole-clearing exponents gives a common power which clears both germs. -/
theorem IsVectorMeromorphicOn.linearCombination {g : ℂ → E} {D' : Set ℂ}
    (hf : IsVectorMeromorphicOn f Ω D) (hg : IsVectorMeromorphicOn g Ω D') (a b : ℂ) :
    IsVectorMeromorphicOn (a • f + b • g) Ω (D ∪ D') := by
  have hsub := union_subset hf.1 hg.1
  have hdom : Ω \ (D ∪ D') = (Ω \ D) ∩ (Ω \ D') := by ext; simp; tauto
  have hopen : IsOpen (Ω \ (D ∪ D')) := hdom ▸ hf.2.2.1.inter hg.2.2.1
  have hpunct {D₀ : Set ℂ} {F : ℂ → E} (hF : IsVectorMeromorphicOn F Ω D₀)
      (x : ℂ) (hx : x ∈ Ω) : ∀ᶠ y in 𝓝[≠] x, y ∉ D₀ := by
    obtain ⟨_, r, _, hr, hs, _, _⟩ := hF.exists_cleared hx
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hr), self_mem_nhdsWithin]
      with y hy hyx using (hs ⟨hy, hyx⟩).2
  refine ⟨hsub, isDiscrete_iff_nhdsNE.mpr (fun x hx ↦ ?_), hopen, ?_, fun x hx ↦ ?_⟩
  · rw [← disjoint_iff, disjoint_principal_right]
    filter_upwards [hpunct hf x (hsub hx), hpunct hg x (hsub hx)] with y hy hy' using
      fun h ↦ h.elim hy hy'
  · apply differentiableOn_of_weaklyHolomorphicOn hopen
    intro φ
    have h₁ := (vectorHolomorphicOn_weaklyHolomorphic hf.2.2.1 hf.2.2.2.1 φ).mono
      (hdom ▸ inter_subset_left)
    have h₂ := (vectorHolomorphicOn_weaklyHolomorphic hg.2.2.1 hg.2.2.2.1 φ).mono
      (hdom ▸ inter_subset_right)
    simpa [Function.comp_def] using (h₁.const_mul a).fun_add (h₂.const_mul b)
  · obtain ⟨n, r, F, hr, hs, hF, heF⟩ := hf.exists_cleared (hsub hx)
    obtain ⟨m, t, G, ht, htS, hG, heG⟩ := hg.exists_cleared (hsub hx)
    let B := Metric.ball x (min r t)
    have h₁ : B ⊆ Metric.ball x r := Metric.ball_subset_ball (min_le_left _ _)
    have h₂ : B ⊆ Metric.ball x t := Metric.ball_subset_ball (min_le_right _ _)
    refine ⟨n + m, min r t, fun y ↦ (a * (y - x) ^ m) • F y + (b * (y - x) ^ n) • G y,
      lt_min hr ht, fun y hy ↦ hdom ▸ ⟨hs ⟨h₁ hy.1, hy.2⟩, htS ⟨h₂ hy.1, hy.2⟩⟩, ?_, ?_⟩
    · apply differentiableOn_of_weaklyHolomorphicOn Metric.isOpen_ball
      intro φ
      have hp (j : ℕ) (c : ℂ) : DifferentiableOn ℂ (fun y ↦ c * (y - x) ^ j) B :=
        ((differentiableOn_id.sub_const x).pow j).const_mul c
      simpa [Function.comp_def] using
        ((hp m a).fun_mul ((vectorHolomorphicOn_weaklyHolomorphic Metric.isOpen_ball hF φ).mono h₁)).fun_add
          ((hp n b).fun_mul ((vectorHolomorphicOn_weaklyHolomorphic Metric.isOpen_ball hG φ).mono h₂))
    · intro y hy
      simp [heF ⟨h₁ hy.1, hy.2⟩, heG ⟨h₂ hy.1, hy.2⟩, pow_add, smul_add, smul_smul,
        mul_assoc, mul_comm, mul_left_comm]

/-- All sufficiently small circles recover the residue and lie in the regular domain. -/
private theorem IsVectorMeromorphicOn.eventually_circleIntegral_residue (hf : IsVectorMeromorphicOn f Ω D)
    (hΩ : IsOpen Ω) (hz : z ∈ Ω) (φ : StrongDual ℂ E) :
    ∀ᶠ R in 𝓝[>] (0 : ℝ), CircleIntegrable (φ ∘ f) z R ∧
      circleIntegral (φ ∘ f) z R = (2 * (Real.pi : ℂ) * Complex.I) *
        φ (vectorResidue (hf.existsUnique_laurentSeries hΩ hz).exists) := by
  let h := (hf.existsUnique_laurentSeries hΩ hz).exists
  obtain ⟨r, hr, hcoef⟩ := h.choose_spec.eventually_circleIntegral_coeff
  obtain ⟨_, t, _, ht, hpunct, _, _⟩ := hf.exists_cleared hz
  filter_upwards [Ioo_mem_nhdsGT (lt_min hr ht)] with R hR
  refine ⟨ContinuousOn.circleIntegrable hR.1.le
    ((φ.continuous.comp_continuousOn hf.2.2.2.1.continuousOn).mono fun y hy ↦
      hpunct ⟨Metric.mem_ball.mpr ((Metric.mem_sphere.mp hy).trans_lt (lt_min_iff.mp hR.2).2),
        Metric.ne_of_mem_sphere hy hR.1.ne'⟩), ?_⟩
  simpa [vectorResidue, vectorLaurentCoeff, h, Function.comp_def] using
    hcoef R hR.1 (lt_min_iff.mp hR.2).1 φ (-1)

/-- Paper: Lemma C.5.3.3(1), p. 740. The residue preserves complex linear
combinations.
Deviation: The linear combination uses the common domain of both representatives. -/
theorem vectorResidue_linear (hΩ : IsOpen Ω) (hz : z ∈ Ω)
    {g : ℂ → E} {D' : Set ℂ} (hf : IsVectorMeromorphicOn f Ω D)
    (hg : IsVectorMeromorphicOn g Ω D') (a b : ℂ) :
    ∃ h : IsVectorMeromorphicOn (a • f + b • g) Ω (D ∪ D'),
      vectorResidue (h.existsUnique_laurentSeries hΩ hz).exists =
        a • vectorResidue (hf.existsUnique_laurentSeries hΩ hz).exists +
          b • vectorResidue (hg.existsUnique_laurentSeries hΩ hz).exists := by
  have h := hf.linearCombination hg a b
  refine ⟨h, ?_⟩
  apply (weakBidualEval_isEmbedding E).injective
  apply LinearMap.ext
  intro φ
  change φ _ = φ _
  obtain ⟨R, ⟨hfi, hfr⟩, ⟨hgi, hgr⟩, _, hlin⟩ :=
    ((hf.eventually_circleIntegral_residue hΩ hz φ).and
      ((hg.eventually_circleIntegral_residue hΩ hz φ).and
        (h.eventually_circleIntegral_residue hΩ hz φ))).exists
  have he : φ ∘ (a • f + b • g) = fun y ↦ a • (φ ∘ f) y + b • (φ ∘ g) y := by
    ext y
    simp
  have hadd := circleIntegral.integral_add (hfi.const_smul (a := a)) (hgi.const_smul (a := b))
  simp only [Pi.smul_apply] at hadd
  rw [he, hadd,
    circleIntegral.integral_smul, circleIntegral.integral_smul, hfr, hgr] at hlin
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  apply mul_left_cancel₀ hc
  rw [← hlin, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

-- TODO(paper-gap): The unrestricted wording of C.5.3.3(2) allows an annular hole
-- inside the contour and never explicitly requires z to be inside it.

/-- Paper: Lemma C.5.3.3(2), p. 740. The normalized contour integral around an
enclosed point gives its residue when the only possible interior pole is that point.
Deviation: The point is explicitly enclosed, and the contour and interior
satisfy the conditions of the Laurent coefficient formula above. -/
theorem hasPettisIntegral_vectorResidue (hΩ : IsOpen Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (γ : PositiveSimpleContour)
    (htrace : γ.val.trace ⊆ Ω) (hinterior : γ.interior ⊆ Ω) (hz : z ∈ γ.interior)
    (havoid : ∀ w ∈ γ.val.trace, ¬ IsVectorPoleAt f w)
    (honly : ∀ w ∈ γ.interior, IsVectorPoleAt f w → w = z) :
    ∃ g : ℂ → E, EqOn g f (Ω \ D) ∧
      DifferentiableOn ℂ g (Ω \ {w | IsVectorPoleAt f w}) ∧
      HasPettisIntegral γ.val.measure g
        ((2 * (Real.pi : ℂ) * Complex.I) •
          vectorResidue (hf.existsUnique_laurentSeries hΩ (hinterior hz)).exists) := by
  simpa [vectorResidue] using
    hasPettisIntegral_laurentCoeff hΩ hf γ htrace hinterior hz havoid honly (-1)

/-- Continuous complex-linear maps preserve the meromorphic representative and
carry every Laurent coefficient, in particular the residue, to its image. -/
theorem vectorLaurentCoeff_comp_continuousLinearMap
    {F : Type*} [AddCommGroup F] [Module ℂ F] [UniformSpace F]
    [IsUniformAddGroup F] [ContinuousSMul ℂ F] [T2Space F] [PolynormableSpace ℂ F]
    [QuasiCompleteSpace ℂ F] (hΩ : IsOpen Ω) (hz : z ∈ Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (T : E →L[ℂ] F) :
    ∃ h : IsVectorMeromorphicOn (T ∘ f) Ω D, ∀ k : ℤ,
      vectorLaurentCoeff (h.existsUnique_laurentSeries hΩ hz).exists k =
        T (vectorLaurentCoeff (hf.existsUnique_laurentSeries hΩ hz).exists k) := by
  have hcomp {U : Set ℂ} {g : ℂ → E} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) :
      DifferentiableOn ℂ (T ∘ g) U := by
    intro x hx
    have h := hg.hasFDerivAt (hU.mem_nhds hx)
    have hT : HasFDerivAt (T ∘ g) (T.comp (fderiv ℂ g x)) x := by
      apply HasFDerivAt.of_isLittleOTVS
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
        using T.isBigOTVS_comp.trans_isLittleOTVS h.isLittleOTVS
    exact ⟨_, hT.hasFDerivWithinAt⟩
  have hmer : IsVectorMeromorphicOn (T ∘ f) Ω D := by
    obtain ⟨hDΩ, hDd, hopen, hhol, hclear⟩ := hf
    refine ⟨hDΩ, hDd, hopen, hcomp hopen hhol, fun w hw ↦ ?_⟩
    obtain ⟨n, r, g, hr, hsub, hg, heq⟩ := hclear w hw
    refine ⟨n, r, T ∘ g, hr, hsub, hcomp Metric.isOpen_ball hg, fun x hx ↦ ?_⟩
    simp only [Function.comp_apply, heq hx, map_smul]
  refine ⟨hmer, fun k ↦ ?_⟩
  let a := (hf.existsUnique_laurentSeries hΩ hz).exists
  let b := (hmer.existsUnique_laurentSeries hΩ hz).exists
  have hab := b.choose_spec.coeff_unique (a.choose_spec.continuousLinearMap_comp T)
  exact congrFun hab k

/-- At a pole of order (n), the power (n) clears the pole. The resulting
holomorphic germ has residue equal to its factorial-normalized derivative
at index (n-1). -/
theorem IsVectorMeromorphicOn.exists_residue_derivative_of_order
    (hΩ : IsOpen Ω) (hf : IsVectorMeromorphicOn f Ω D) (hz : z ∈ Ω)
    {n : ℕ} (hn : 0 < n) (ho : HasVectorMeromorphicOrderAt f z (-(n : ℤ))) :
    ∃ (r : ℝ) (G : ℂ → E), 0 < r ∧ DifferentiableOn ℂ G (Metric.ball z r) ∧
      EqOn G (fun w ↦ (w - z) ^ n • f w) (Metric.ball z r \ {z}) ∧
      vectorResidue (hf.existsUnique_laurentSeries hΩ hz).exists =
        ((n - 1).factorial : ℂ)⁻¹ • (deriv^[n - 1] G) z := by
  classical
  obtain ⟨a, ha, hane, hzero⟩ := ho
  obtain ⟨m, r, g, hr, hpunct, hg, heq⟩ := hf.exists_cleared hz
  let B := Metric.ball z r
  have hB : IsOpen B := Metric.isOpen_ball
  have hzB : z ∈ B := Metric.mem_ball_self hr
  have hgw := vectorHolomorphicOn_weaklyHolomorphic hB hg
  obtain ⟨b, hb⟩ := (weaklyHolomorphicOn_iff_taylor hB).mp hgw z hzB
  have hseries := hasVectorLaurentSeriesAt_of_taylor hr hb heq
  have hnm : n ≤ m := by
    by_contra! h
    apply hane
    rw [ha.coeff_unique hseries]
    exact ite_eq_right (by omega : ¬ -(m : ℤ) ≤ -(n : ℤ))
  let G := update (fun w ↦ (w - z) ^ n • f w) z (a (-(n : ℤ)))
  have hGclear : EqOn G (fun w ↦ (w - z) ^ n • f w) (B \ {z}) :=
    fun w hw ↦ update_of_ne (show w ≠ z from hw.2) _ _
  have hGweak : WeaklyHolomorphicOn G B := by
    intro ℓ w hw
    by_cases hwz : w = z
    · subst w
      let u := ℓ ∘ g
      have hu := hgw ℓ
      have huz := hu.analyticAt (hB.mem_nhds hzB)
      have heu : EqOn u (fun y ↦ (y - z) ^ m * ℓ (f y)) (B \ {z}) := by
        intro y hy
        simp only [u, comp_apply, heq hy, map_smul, smul_eq_mul]
      have hord : ((m - n : ℕ) : ENat) ≤ analyticOrderAt u z := by
        apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero huz).mpr
        intro j hj
        have hj' : (j : ℤ) - m < -(n : ℤ) := by omega
        have hcoeff := ha.coeff_eq_derivative_of_cleared ℓ m j hr hu heu
        rw [hzero _ hj', map_zero] at hcoeff
        exact (div_eq_zero_iff.mp hcoeff.symm).resolve_right (by exact_mod_cast Nat.factorial_ne_zero j)
      obtain ⟨q, hq, hqu⟩ := (natCast_le_analyticOrderAt huz).mp hord
      obtain ⟨t, ht, hball⟩ := Metric.mem_nhds_iff.mp
        (hq.eventually_analyticAt.and (hqu.and (Metric.ball_mem_nhds z hr)))
      have hqhol : DifferentiableOn ℂ q (Metric.ball z t) := fun y hy ↦
        (hball hy).1.differentiableAt.differentiableWithinAt
      have hqf : EqOn q (fun y ↦ (y - z) ^ n * ℓ (f y)) (Metric.ball z t \ {z}) := by
        intro y hy
        apply mul_left_cancel₀ (pow_ne_zero (m - n) (sub_ne_zero.mpr (show y ≠ z from hy.2)))
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnm]
        exact ((hball hy.1).2.1.symm).trans (heu ⟨(hball hy.1).2.2, hy.2⟩)
      have hval : ℓ (a (-(n : ℤ))) = q z := by
        simpa using ha.coeff_eq_derivative_of_cleared ℓ n 0 ht hqhol hqf
      apply DifferentiableAt.differentiableWithinAt
      apply hq.differentiableAt.congr_of_eventuallyEq
      filter_upwards [Metric.ball_mem_nhds z ht] with y hy
      rcases eq_or_ne y z with rfl | hyz
      · simpa [G] using hval
      · rw [comp_apply, hGclear ⟨(hball hy).2.2, hyz⟩, map_smul, smul_eq_mul]
        exact (hqf ⟨hy, hyz⟩).symm
    · have hregular := vectorHolomorphicOn_weaklyHolomorphic hf.2.2.1 hf.2.2.2.1 ℓ
      have h₁ : DifferentiableAt ℂ (fun y ↦ (y - z) ^ n * ℓ (f y)) w :=
        (((differentiableOn_id.sub_const z).pow n).mul hregular).differentiableAt
          (hf.2.2.1.mem_nhds (hpunct ⟨hw, hwz⟩))
      apply DifferentiableAt.differentiableWithinAt
      apply h₁.congr_of_eventuallyEq
      filter_upwards [hB.mem_nhds hw, isOpen_ne.mem_nhds hwz] with y hy hyz
      simp only [comp_apply, hGclear ⟨hy, hyz⟩, map_smul, smul_eq_mul]
  refine ⟨r, G, hr, differentiableOn_of_weaklyHolomorphicOn hB hGweak, hGclear, ?_⟩
  have hcoeff := (hf.existsUnique_laurentSeries hΩ hz).exists.choose_spec.coeff_unique ha
  change (hf.existsUnique_laurentSeries hΩ hz).exists.choose (-1) =
    ((n - 1).factorial : ℂ)⁻¹ • (deriv^[n - 1] G) z
  rw [hcoeff]
  exact ha.residue_eq_cleared_derivative hn hr hGweak hGclear

/-- On a relatively closed discrete exceptional set, the weak pole-clearing
presentation and strong vector meromorphy describe the same functions. -/
theorem isVectorMeromorphicOn_iff_weak (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω)
    (hD : IsDiscrete D) :
    IsVectorMeromorphicOn f Ω D ↔ WeakVectorMeromorphic f Ω D := by
  constructor
  · rintro ⟨_, _, hopen, hhol, hclear⟩
    refine ⟨hopen, vectorHolomorphicOn_weaklyHolomorphic hopen hhol, ?_⟩
    intro x hx
    obtain ⟨n, r, g, hr, _, hg, heq⟩ := hclear x hx.2
    refine ⟨n, g, fun ℓ ↦ ?_, ?_⟩
    · exact (vectorHolomorphicOn_weaklyHolomorphic Metric.isOpen_ball hg ℓ).analyticAt
        (Metric.ball_mem_nhds x hr)
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hr),
        self_mem_nhdsWithin] with w hw hwx
      exact (heq ⟨hw, hwx⟩).symm
  · rintro ⟨hopen, hhol, hclear⟩
    refine ⟨hDΩ, hD, hopen, differentiableOn_of_weaklyHolomorphicOn hopen hhol, ?_⟩
    intro x hx
    have hxΩ := hDΩ hx
    obtain ⟨V, hV, hVD⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hD x hx
    have hxV : x ∈ V := (show x ∈ V ∩ D by rw [hVD]; exact mem_singleton _).1
    obtain ⟨n, g, hg, heq⟩ := hclear x ⟨hxΩ, hx⟩
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
      (inter_mem (hΩ.mem_nhds hxΩ) (inter_mem (hV.mem_nhds hxV) (eventually_nhdsWithin_iff.mp heq)))
    have hregular : Metric.ball x r \ {x} ⊆ Ω \ D := by
      intro y hy
      exact ⟨(hsub hy.1).1, fun hyD ↦ hy.2 (hVD ▸ ⟨(hsub hy.1).2.1, hyD⟩)⟩
    have hEq : EqOn g (fun w ↦ (w - x) ^ n • f w) (Metric.ball x r \ {x}) :=
      fun y hy ↦ ((hsub hy.1).2.2 hy.2).symm
    refine ⟨n, r, g, hr, hregular, differentiableOn_of_weaklyHolomorphicOn Metric.isOpen_ball ?_, hEq⟩
    intro ℓ y hy
    by_cases hyx : y = x
    · exact hyx ▸ (hg ℓ).differentiableAt.differentiableWithinAt
    · have hd : DifferentiableOn ℂ (fun w ↦ (w - x) ^ n * ℓ (f w)) (Ω \ D) :=
        ((differentiableOn_id.sub_const x).pow n).mul (hhol ℓ)
      apply DifferentiableAt.differentiableWithinAt
      apply (hd.differentiableAt (hopen.mem_nhds (hregular ⟨hy, hyx⟩))).congr_of_eventuallyEq
      filter_upwards [Metric.isOpen_ball.mem_nhds hy, isOpen_ne.mem_nhds hyx] with w hw hwx
      simp only [comp_apply, hEq ⟨hw, hwx⟩, map_smul, smul_eq_mul]


end

end Masullo
