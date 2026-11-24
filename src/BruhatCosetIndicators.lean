import LocallyConstantTests
import HeckeEulerProducts
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.Basic

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical ContDiff NumberField SchwartzMap RestrictedProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev FinAdeles := FiniteAdeleRing (𝓞 F) F

/-- Every finite tensor of indicators of additive subgroups is invariant under
simultaneous negation of its finite coordinates. -/
theorem adelic_subgroupIndicatorTensor_even
    (K : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (x : FinAdeles F) :
    (if ∀ v, (-x) v ∈ K v then (1 : ℂ) else 0) =
      (if ∀ v, x v ∈ K v then (1 : ℂ) else 0) := by
  classical
  have he : (∀ v, (-x) v ∈ K v) ↔ ∀ v, x v ∈ K v := by
    apply forall_congr'
    intro v
    change -x v ∈ K v ↔ x v ∈ K v
    exact (K v).neg_mem_iff
  rw [he]

private abbrev subgroupIndicatorTensors : Set (Adeles F → ℂ) :=
  {f | ∃ (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
      (K : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    f = fun a => φ (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1) *
      (if ∀ v, a.2 v ∈ K v then 1 else 0)}

private theorem subgroupIndicatorTensors_span_even {f : Adeles F → ℂ}
    (hf : f ∈ Submodule.span ℂ (subgroupIndicatorTensors F)) (a : Adeles F) :
    f (a.1, -a.2) = f a := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨φ, K, rfl⟩ := hg
    change _ * (if ∀ v, (-a.2) v ∈ K v then (1 : ℂ) else 0) =
      _ * (if ∀ v, a.2 v ∈ K v then (1 : ℂ) else 0)
    rw [adelic_subgroupIndicatorTensor_even F K a.2]
  | zero => rfl
  | add g h hg hh ihg ihh =>
    change g (a.1, -a.2) + h (a.1, -a.2) = g a + h a
    rw [ihg, ihh]
  | smul c g hg ih =>
    change c • g (a.1, -a.2) = c • g a
    rw [ih]

/-- Lemma 2.1.3.2(3) as printed fails at every finite place. Compact-open
subgroup indicators cannot produce a test supported near a finite adele
and vanishing at its additive inverse. -/
theorem bruhat_subgroupIndicators_counterexample (v : HeightOneSpectrum (𝓞 F)) :
    ∃ f ∈ bruhatSubmodule F, f ∉ Submodule.span ℂ (subgroupIndicatorTensors F) := by
  classical
  let L := v.adicCompletion F
  letI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  letI : T2Space (FinAdeles F) :=
    inferInstanceAs (T2Space (Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]))
  obtain ⟨K, hK, hKo, hK1⟩ := finiteAdeles_exists_compactClopen_one (F := F)
  let r := dist (-(1 : L)) 1
  have hr : 0 < r := dist_pos.mpr (by
    intro e
    have he := congrArg (fun t : L => t + 1) e
    simp only [neg_add_cancel, ← two_mul, mul_one] at he
    have htwo : (2 : v.adicCompletion F) ≠ 0 := two_ne_zero
    exact htwo he.symm)
  let U := K ∩ (fun x : FinAdeles F => x v) ⁻¹' Metric.ball (1 : L) r
  have hUopen : IsOpen U :=
    hKo.2.inter (Metric.isOpen_ball.preimage (RestrictedProduct.continuous_eval v))
  have hUc : IsCompact U :=
    hK.inter_right ((IsUltrametricDist.isClosed_ball (1 : L) r).preimage
      (RestrictedProduct.continuous_eval v))
  have h1 : (1 : FinAdeles F) ∈ U := ⟨hK1, Metric.mem_ball_self hr⟩
  have hn1 : -(1 : FinAdeles F) ∉ U := fun h => (lt_irrefl r) h.2
  let χ := compactOpenIndicator (FinAdeles F) ⟨U, hUc, hUopen⟩
  let ψ : FiniteBruhat F := ⟨⟨χ.val, χ.property.1⟩, χ.property.2⟩
  obtain ⟨u, _, huc, hu, _, hu0⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (s := univ)
      (x := (0 : mixedEmbedding.mixedSpace F)) univ_mem
  let z (x : mixedEmbedding.mixedSpace F) : ℂ := (u x : ℂ)
  let φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ) :=
    (huc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hu)
  let g := bruhatTensor F φ ψ
  refine ⟨g, bruhatTensor_mem F φ ψ, fun hg => ?_⟩
  have he := subgroupIndicatorTensors_span_even F hg (0, 1)
  change φ ((InfiniteAdeleRing.ringEquiv_mixedSpace F) 0) * ψ.toLocallyConstant (-1) =
    φ ((InfiniteAdeleRing.ringEquiv_mixedSpace F) 0) * ψ.toLocallyConstant 1 at he
  have hψ0 : ψ.toLocallyConstant (-1) = 0 := by
    change U.indicator (fun _ => (1 : ℂ)) (-1) = 0
    exact Set.indicator_of_notMem hn1 _
  have hψ1 : ψ.toLocallyConstant 1 = 1 := by
    change U.indicator (fun _ => (1 : ℂ)) 1 = 1
    exact Set.indicator_of_mem h1 _
  have hφ : φ 0 = 1 := by
    change (u 0 : ℂ) = 1
    exact_mod_cast hu0
  rw [map_zero, hψ0, hψ1, hφ, mul_zero, mul_one] at he
  exact zero_ne_one he

/-- The whole finite completion is an open noncompact set, so it cannot
be a finite union of compact opens as claimed in Example 2.1.2.6. -/
theorem finitePlace_univ_not_isCompact (w : HeightOneSpectrum (𝓞 F)) :
    ¬ IsCompact (univ : Set (w.adicCompletion F)) := by
  let K := w.adicCompletion F
  let π : K := chosenFiniteUniformizer F w
  letI : NontriviallyNormedField K :=
    { toNormedField := inferInstance
      non_trivial := ⟨π⁻¹, by
        rw [norm_inv, norm_finiteUniformizer F w π (chosenFiniteUniformizer_spec F w), inv_inv]
        exact_mod_cast HeightOneSpectrum.one_lt_absNorm w⟩ }
  intro h
  obtain ⟨x, _, hmax⟩ := h.exists_isMaxOn (univ_nonempty (α := w.adicCompletion F))
    (continuous_norm.continuousOn : ContinuousOn (fun x : w.adicCompletion F => ‖x‖) univ)
  obtain ⟨y, hy⟩ := NormedField.exists_lt_norm (w.adicCompletion F) ‖x‖
  exact hy.not_ge (hmax (mem_univ y))

open scoped WithZero in
/-- Example 2.1.2.6. Every finite-place Schwartz–Bruhat test is a finite
linear combination of indicators of translates of positive powers of the maximal
ideal. Adapted from original commit de89e10 (Apache-2.0). -/
theorem finitePlaceSchwartz_sum_indicators (w : HeightOneSpectrum (𝓞 F))
    (f : locallyConstantTests (w.adicCompletion F))
    (π : w.adicCompletion F)
    (hπ : Valued.v.IsUniformizer π) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (a : Fin n → w.adicCompletion F) (N : ℤ),
      0 < N ∧ ∀ x : w.adicCompletion F,
        f.val x = ∑ i, c i * Set.indicator
            {y | ∃ z : w.adicCompletionIntegers F, y = a i + π ^ N * z.val} (fun _ => 1) x := by
  classical
  let K := w.adicCompletion F
  let g : K → ℂ := f.val
  obtain ⟨hg, hc⟩ := f.property
  -- Compactness gives one neighborhood of translations fixing all values on the support.
  have hopen : IsOpen {p : K × K | g (p.1 + p.2) = g p.1} := by
    have hloc : IsLocallyConstant (fun p : K × K ↦ g (p.1 + p.2) = g p.1) :=
      (hg.comp_continuous continuous_add).comp₂ (hg.comp_continuous continuous_fst) Eq
    simpa only [eq_iff_iff, iff_true] using hloc.isOpen_fiber True
  obtain ⟨U, V, _, hV, hU, hzero, hUV⟩ :=
    generalized_tube_lemma hc (isCompact_singleton (x := (0 : K))) hopen (by
      rintro ⟨x, y⟩ ⟨_, hy⟩
      obtain rfl := mem_singleton_iff.mp hy
      change g (x + 0) = g x
      rw [add_zero])
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp (hV.mem_nhds (hzero (mem_singleton 0)))
  let ν : Valuation K ℤᵐ⁰ := Valued.v
  let r : ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding γ.val
  have hr : r ≠ 0 := by simp [r]
  let N : ℤ := max 1 (1 - WithZero.log r)
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hπvalue : ν π = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (HeightOneSpectrum.valuedAdicCompletion_surjective F w)))
  have hpow : ν (π ^ N) = WithZero.exp (-N) := by
    rw [map_zpow₀ ν, hπvalue, ← WithZero.exp_zsmul]
    simp
  have hv : ν (π ^ N) ≠ 0 := by simp [hpow]
  have hlt : ν (π ^ N) < r := by
    rw [hpow, ← WithZero.exp_log hr, WithZero.exp_lt_exp]
    have h := le_max_right 1 (1 - WithZero.log r)
    omega
  let L := ν.leAddSubgroup (ν (π ^ N))
  have hL : (L : Set K) ⊆ V := fun x hx ↦
    hγ ((ν.restrict_lt_iff_lt_embedding).mpr (lt_of_le_of_lt hx hlt))
  have hLopen : IsOpen (L : Set K) := by
    change IsOpen {x : K | ν x ≤ ν (π ^ N)}
    have hball : IsOpen {x : K | ν.restrict x ≤ ν.restrict (π ^ N)} :=
      Valued.isOpen_closedBall K (fun h ↦ hv (ν.restrict_eq_zero_iff.mp h))
    simpa only [Valuation.restrict_le_iff] using hball
  let q : K → K ⧸ L := QuotientAddGroup.mk
  let : DiscreteTopology (K ⧸ L) := QuotientAddGroup.discreteTopology hLopen
  let A := q '' tsupport g
  have hfinite : A.Finite := (hc.image QuotientAddGroup.continuous_mk).finite_of_discrete
  let : Fintype A := hfinite.fintype
  let e := (Fintype.equivFin A).symm
  let a (i : Fin (Fintype.card A)) : K := (e i).property.choose
  have ha (i : Fin (Fintype.card A)) : a i ∈ tsupport g ∧ q (a i) = (e i).val :=
    (e i).property.choose_spec
  -- Each quotient fiber is a translate of the scaled integer ring.
  have hfiber (x y : K) :
      (∃ z : w.adicCompletionIntegers F, x = y + π ^ N * z.val) ↔ q x = q y := by
    have hp : π ^ N ≠ 0 := fun h ↦ hv (by rw [h, map_zero])
    rw [QuotientAddGroup.eq_iff_sub_mem]
    constructor
    · rintro ⟨z, rfl⟩
      change ν (y + π ^ N * z.val - y) ≤ ν (π ^ N)
      rw [add_sub_cancel_left, map_mul]
      exact mul_le_of_le_one_right' z.property
    · intro hx
      have hz : (x - y) / π ^ N ∈ w.adicCompletionIntegers F := by
        change ν ((x - y) / π ^ N) ≤ 1
        rw [ν.map_div, div_le_one₀ (pos_of_ne_zero hv)]
        exact hx
      exact ⟨⟨_, hz⟩, by
        change x = y + π ^ N * ((x - y) / π ^ N)
        rw [mul_comm (π ^ N), div_mul_cancel₀ _ hp, add_sub_cancel]⟩
  refine ⟨_, fun i ↦ g (a i), a, N, hN, fun x ↦ ?_⟩
  change g x = _
  simp only [Set.indicator, Set.mem_ofPred_eq, hfiber, fun i ↦ (ha i).2]
  by_cases hx : q x ∈ A
  · let i := e.symm ⟨q x, hx⟩
    have hi : (e i).val = q x := congrArg Subtype.val (e.apply_symm_apply ⟨q x, hx⟩)
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
    · rw [ite_eq_left hi.symm, mul_one]
      have hmem : x - a i ∈ L :=
        QuotientAddGroup.eq_iff_sub_mem.mp (show q x = q (a i) from hi.symm.trans (ha i).2.symm)
      have heq : g (a i + (x - a i)) = g (a i) :=
        hUV (mk_mem_prod (hU (ha i).1) (hL hmem))
      simpa only [add_sub_cancel] using heq
    · intro j _ hj
      have hne : q x ≠ (e j).val := fun h ↦ hj (e.injective (Subtype.ext (h.symm.trans hi.symm)))
      rw [ite_eq_right hne, mul_zero]
  · have hgx : g x = 0 := notMem_support.mp fun hs ↦ hx ⟨x, subset_tsupport g hs, rfl⟩
    rw [hgx]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hne : q x ≠ (e i).val := fun h ↦ hx (h.symm ▸ (e i).property)
    rw [ite_eq_right hne, mul_zero]

end
end Masullo
