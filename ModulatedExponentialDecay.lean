import ModulatedBruhatCompactCore
import BruhatCompactTestTopology
import FrechetFactorization

open Filter Function Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ) (I : Set ℝ)

/-- Real abscissa multiplication on functions on the group. -/
def modulatedExponentialWeight (a : ℝ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
  LinearMap.mulLeft ℂ (fun g => (Real.exp (a * (m g).toAdd) : ℂ))

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
theorem modulatedExponentialWeight_apply (a : ℝ) (f : G → ℂ) (g : G) :
    modulatedExponentialWeight m a f g = Real.exp (a * (m g).toAdd) • f g := rfl

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
theorem modulatedExponentialWeight_add (a b : ℝ) (f : G → ℂ) :
    modulatedExponentialWeight m a (modulatedExponentialWeight m b f) =
      modulatedExponentialWeight m (a + b) f := by
  funext g
  simp only [modulatedExponentialWeight_apply, smul_smul, add_mul, Real.exp_add]

set_option maxHeartbeats 1200000 in
/-- Lemma D.3.3.2. Two Schwartz–Bruhat endpoint twists imply Schwartz–Bruhat
regularity at every intermediate abscissa. The endpoint profiles are
compared on a common elementary quotient. -/
theorem modulatedExponentialWeight_mem_between {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    {f : G → ℂ} (ha : modulatedExponentialWeight m a f ∈ bruhatSchwartzSubmodule (G := G))
    (hb : modulatedExponentialWeight m b f ∈ bruhatSchwartzSubmodule (G := G)) :
    modulatedExponentialWeight m c f ∈ bruhatSchwartzSubmodule (G := G) := by
  obtain ⟨P, x, hx⟩ := ha
  obtain ⟨Q, y, hy⟩ := hb
  obtain ⟨R, u, v, hu, hv⟩ := bruhatSchwartzStages_common x y
  have hua := hu.trans hx
  have hvb := hv.trans hy
  let A := ElementaryLCAModel R.2.realDim R.2.torusDim R.2.latticeRank R.2.finiteFactor
  let M := (R.1.descendHom m (R.1.modulation_eq_one_on_kernel m)).comp
    (R.2.equiv.symm : Multiplicative A →ₜ* R.1.StageQuotient)
  let l : A →+ ℝ := M.toMonoidHom.toAdditive
  have hl : Continuous l := continuous_toAdd.comp (M.continuous.comp continuous_ofAdd)
  have hlog (g : R.1.upper.val) : l (R.1.stageCoordinates R.2 g).toAdd = (m g.val).toAdd := by
    change ((R.1.descendHom m (R.1.modulation_eq_one_on_kernel m))
      (R.2.equiv.symm (R.2.equiv (QuotientGroup.mk g)))).toAdd = _
    rw [R.2.equiv.symm_apply_apply, LCAStructuralPair.descendHom_mk]
  have htwist (d : ℝ) : modulatedExponentialWeight m (d - a) (modulatedExponentialWeight m a f) =
      modulatedExponentialWeight m d f := by
    rw [modulatedExponentialWeight_add, sub_add_cancel]
  have hG (d : ℝ) (g : R.1.upper.val) :
      Real.exp ((d - a) * l (R.1.stageCoordinates R.2 g).toAdd) •
          u (R.1.stageCoordinates R.2 g).toAdd = modulatedExponentialWeight m d f g.val := by
    rw [hlog, ← R.1.realizeSchwartz_apply_of_mem R.2 u g, hua]
    exact congrFun (htwist d) g.val
  have hmatch (z : A) : v z = Real.exp ((b - a) * l z) • u z := by
    have hs : Surjective (R.1.stageCoordinates R.2) :=
      R.2.equiv.surjective.comp QuotientGroup.mk_surjective
    obtain ⟨g, hg⟩ := hs (Multiplicative.ofAdd z)
    rw [← show (R.1.stageCoordinates R.2 g).toAdd = z from congrArg Multiplicative.toAdd hg,
      hG b g, ← hvb]
    exact (R.1.realizeSchwartz_apply_of_mem R.2 v g).symm
  let w : R.Space := ⟨_, @elementarySchwartz_exponential_between R.2.realDim R.2.torusDim R.2.latticeRank
    R.2.finiteFactor R.2.finiteGroup R.2.finiteTopology R.2.finiteDiscrete (Finite.of_fintype _)
    l hl a c b hac hcb u v hmatch⟩
  refine ⟨R, w, funext fun g => ?_⟩
  by_cases hg : g ∈ R.1.upper.val
  · exact (R.1.realizeSchwartz_apply_of_mem R.2 w ⟨g, hg⟩).trans (hG c ⟨g, hg⟩)
  · rw [R.1.realizeSchwartz_apply_of_not_mem R.2 w g hg, ← htwist c,
      modulatedExponentialWeight_apply, ← hua,
      R.1.realizeSchwartz_apply_of_not_mem R.2 u g hg, smul_zero]

/-- The decay space consists of functions whose twists at all abscissae
belong to the Schwartz–Bruhat space. -/
def modulatedExponentialDecaySubmodule : Submodule ℂ (G → ℂ) :=
  ⨅ a : I, bruhatSchwartzSubmodule.comap (modulatedExponentialWeight m a)

abbrev ModulatedExponentialDecay := modulatedExponentialDecaySubmodule m I

def modulatedExponentialDecay_twist (a : I) :
    ModulatedExponentialDecay m I →ₗ[ℂ] BruhatSchwartz G :=
  ((modulatedExponentialWeight m a).comp (modulatedExponentialDecaySubmodule m I).subtype).codRestrict
    _ fun f => (Submodule.mem_iInf _).mp f.property a

theorem modulatedExponentialDecay_twist_apply (a : I) (f : ModulatedExponentialDecay m I) (g : G) :
    (modulatedExponentialDecay_twist m I a f).val g =
      Real.exp ((a : ℝ) * (m g).toAdd) • f.val g := rfl

/-- The projective topology of all the Schwartz–Bruhat twists. -/
instance : TopologicalSpace (ModulatedExponentialDecay m I) :=
  ⨅ a : I, TopologicalSpace.induced (modulatedExponentialDecay_twist m I a) inferInstance

theorem modulatedExponentialDecay_mem_of_smooth_compactSupport {f : G → ℂ}
    (hf : f ∈ bruhatSmoothSubmodule (G := G)) (hc : HasCompactSupport f) :
    f ∈ modulatedExponentialDecaySubmodule m I := by
  apply (Submodule.mem_iInf _).mpr
  intro a
  exact twist_mem_bruhatSchwartz_of_smooth_compactSupport m a hf hc

private theorem tendsto_modulatedExponentialDecay_iff {α : Type*}
    {F : Filter α} {u : α → ModulatedExponentialDecay m I} {f : ModulatedExponentialDecay m I} :
    Tendsto u F (𝓝 f) ↔
      ∀ a : I, Tendsto (fun n => modulatedExponentialDecay_twist m I a (u n)) F
        (𝓝 (modulatedExponentialDecay_twist m I a f)) := by
  change Tendsto u F (@nhds _ (⨅ a : I,
      TopologicalSpace.induced (modulatedExponentialDecay_twist m I a) inferInstance) f) ↔ _
  rw [nhds_iInf, tendsto_iInf]
  simp only [nhds_induced, tendsto_comap_iff, Function.comp_def]

set_option maxHeartbeats 800000 in
/-- The same compactly supported cutoff sequence converges simultaneously
at every real abscissa, in the projective Schwartz–Bruhat topology. -/
theorem dense_modulatedExponentialDecay_smooth_compactSupport (hm : IsProperMap m) (hI : I.Nonempty) :
    Dense {f : ModulatedExponentialDecay m I |
      f.val ∈ bruhatSmoothSubmodule (G := G) ∧ HasCompactSupport f.val} := by
  intro f
  let fₙ (n : ℕ) (g : G) := truncationMultiplier n (modulatedLog m g) * f.val g
  choose u hu huv huc using fun a : I =>
    exists_bruhatSchwartz_logCutoff_sequence m hm (modulatedExponentialDecay_twist m I a f)
  have he (a : I) (n : ℕ) (g : G) :
      (u a n).val g = Real.exp ((a : ℝ) * (m g).toAdd) • fₙ n g := by
    rw [huv, modulatedExponentialDecay_twist_apply]
    exact mul_smul_comm _ _ _
  have hmem (n : ℕ) : fₙ n ∈ modulatedExponentialDecaySubmodule m I := by
    apply (Submodule.mem_iInf _).mpr
    intro a
    change modulatedExponentialWeight m a (fₙ n) ∈ bruhatSchwartzSubmodule
    rw [show modulatedExponentialWeight m a (fₙ n) = (u a n).val from funext (fun g => (he a n g).symm)]
    exact (u a n).property
  let v (n : ℕ) : ModulatedExponentialDecay m I := ⟨fₙ n, hmem n⟩
  have hv (a : I) (n : ℕ) : modulatedExponentialDecay_twist m I a (v n) = u a n :=
    Subtype.ext (funext fun g => (he a n g).symm)
  apply mem_closure_of_tendsto (f := v)
    ((tendsto_modulatedExponentialDecay_iff m I (u := v)).mpr (fun a => by
      simpa only [hv] using hu a))
  apply Eventually.of_forall
  intro n
  obtain ⟨a, ha⟩ := hI
  let a₀ : I := ⟨a, ha⟩
  have hInv : fₙ n = fun g => Real.exp (-a * (m g).toAdd) • (u a₀ n).val g := by
    funext g
    rw [he, smul_smul, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, one_smul]
  change fₙ n ∈ bruhatSmoothSubmodule (G := G) ∧ HasCompactSupport (fₙ n)
  refine ⟨hInv.symm ▸ bruhatSmooth_realModulation_smul m (-a) (bruhatSchwartz_le_smooth (u a₀ n).property), ?_⟩
  apply (huc a₀ n).mono
  intro g hg
  change (u a₀ n).val g ≠ 0
  exact fun h => hg ((congrFun hInv g).trans (by rw [h, smul_zero]))

set_option maxHeartbeats 1000000 in
private theorem compactTestStage_weight_mem_range (a : ℝ) (i : BruhatCompactTestIndex G) (u : i.Space) :
    modulatedExponentialWeight m a (i.1.realize u.val) ∈ i.1.realize.range := by
  let p := i.1
  let A := ElementaryLCAModel p.2.realDim p.2.torusDim p.2.latticeRank p.2.finiteFactor
  let M := (p.1.descendHom m (p.1.modulation_eq_one_on_kernel m)).comp
    (p.2.equiv.symm : Multiplicative A →ₜ* p.1.StageQuotient)
  let l : A →+ ℝ := M.toMonoidHom.toAdditive
  let φ (y : A) := Real.exp (a * l y) • u.val y
  let f := modulatedExponentialWeight m a (p.realize u.val)
  have hf : f ∈ bruhatSmoothSubmodule (G := G) :=
    bruhatSmooth_realModulation_smul m a (p.realize_smooth u.val)
  have hc : HasCompactSupport f := by
    refine HasCompactSupport.intro' i.2.property i.2.property.isClosed (fun g hg => ?_)
    change Real.exp (a * (m g).toAdd) • p.realize u.val g = 0
    rw [u.property g hg, smul_zero]
  have hφ (x : p.1.upper.val) : φ (p.1.stageCoordinates p.2 x).toAdd = f x.val := by
    have he : l (p.1.stageCoordinates p.2 x).toAdd = (m x.val).toAdd := by
      change ((p.1.descendHom m (p.1.modulation_eq_one_on_kernel m))
        (p.2.equiv.symm (p.2.equiv (QuotientGroup.mk x)))).toAdd = _
      rw [p.2.equiv.symm_apply_apply, LCAStructuralPair.descendHom_mk]
    change Real.exp (a * l (p.1.stageCoordinates p.2 x).toAdd) • u.val (p.1.stageCoordinates p.2 x).toAdd =
      Real.exp (a * (m x.val).toAdd) • p.realize u.val x.val
    rw [he, p.1.realizeSchwartz_apply_of_mem]
  exact exists_bruhatSchwartzStage_realization_of_compactSupport hf hc p φ hφ (fun x hx => by
    change Real.exp (a * (m x).toAdd) • p.realize u.val x = 0
    rw [p.1.realizeSchwartz_apply_of_not_mem p.2 u.val x hx, smul_zero])

/-- On a compact support stage exponential multiplication is represented in
the same elementary quotient. -/
def compactTestStage_weight (a : ℝ) (i : BruhatCompactTestIndex G) : i.Space →ₗ[ℂ] i.1.Space :=
  (LinearEquiv.ofInjective i.1.realize (i.1.1.realizeSchwartz_injective i.1.2)).symm.toLinearMap.comp
    (((modulatedExponentialWeight m a).comp
      (i.1.realize.comp (i.1.compactTests i.2.val).subtype)).codRestrict _
        (compactTestStage_weight_mem_range m a i))

theorem compactTestStage_realize_weight (a : ℝ) (i : BruhatCompactTestIndex G)
    (u : i.Space) (g : G) :
    i.1.realize (compactTestStage_weight m a i u) g =
      Real.exp (a * (m g).toAdd) • i.1.realize u.val g :=
  congrFun (LinearEquiv.ofInjective_symm_apply i.1.realize
    (h := i.1.1.realizeSchwartz_injective i.1.2)
    ⟨_, compactTestStage_weight_mem_range m a i u⟩) g

set_option maxHeartbeats 1500000 in
theorem compactTestStage_weight_continuous (a : ℝ) (i : BruhatCompactTestIndex G) :
    Continuous (compactTestStage_weight m a i) := by
  obtain ⟨hT, _, hmetric, hcomplete⟩ := @elementarySchwartz_isFrechet
    i.1.2.realDim i.1.2.torusDim i.1.2.latticeRank i.1.2.finiteFactor
    i.1.2.finiteGroup i.1.2.finiteTopology i.1.2.finiteDiscrete (Finite.of_fintype _)
  letI : T2Space i.1.Space := hT
  letI : TopologicalSpace.MetrizableSpace i.1.Space := hmetric
  letI : FirstCountableTopology i.1.Space := inferInstance
  letI : FirstCountableTopology i.Space := IsInducing.subtypeVal.firstCountableTopology
  letI : CompleteSpace i.1.Space := hcomplete
  letI : ContinuousSMul ℂ i.1.Space := (PolynormableSpace.withSeminorms ℂ i.1.Space).continuousSMul
  letI : IsClosed (i.Space : Set i.1.Space) := i.1.isClosed_compactTests i.2.val
  letI : IsUniformAddGroup i.Space := (i.1.compactTests i.2.val).toAddSubgroup.isUniformAddGroup
  let L := compactTestStage_weight m a i
  apply frechet_continuous_of_closed_graph L
  let S (g : G) : Set (i.Space × i.1.Space) :=
    {q | i.1.realize q.2 g = Real.exp (a * (m g).toAdd) • i.1.realize q.1.val g}
  have he : (L.graph : Set (i.Space × i.1.Space)) = ⋂ g : G, S g := by
    apply Set.ext
    intro q
    change q.2 = L q.1 ↔ q ∈ ⋂ g : G, S g
    constructor
    · intro h
      exact mem_iInter.mpr fun g => (congrArg (fun u : i.1.Space => i.1.realize u g) h).trans
        (compactTestStage_realize_weight m a i q.1 g)
    · intro h
      apply i.1.1.realizeSchwartz_injective i.1.2
      funext g
      exact (mem_iInter.mp h g).trans (compactTestStage_realize_weight m a i q.1 g).symm
  have hc (g : G) : IsClosed (S g) := by
    have h₁ : Continuous (fun q : i.Space × i.1.Space => i.1.realize q.2 g) :=
      (i.1.continuous_realize_eval g).comp continuous_snd
    have h₂ : Continuous (fun q : i.Space × i.1.Space => i.1.realize q.1.val g) :=
      (i.1.continuous_realize_eval g).comp (continuous_subtype_val.comp continuous_fst)
    exact isClosed_eq h₁ (h₂.const_smul (Real.exp (a * (m g).toAdd)))
  exact (congrArg IsClosed he).mpr (isClosed_iInter hc)

/-- The inclusion of compact Bruhat tests into the projective decay space. -/
def bruhatCompactTest_toModulatedExponentialDecay :
    BruhatCompactTest G →ₗ[ℂ] ModulatedExponentialDecay m I :=
  (bruhatSchwartzSubmodule.subtype.comp bruhatCompactTest_toSchwartz.toLinearMap).codRestrict _
    (fun u => modulatedExponentialDecay_mem_of_smooth_compactSupport m I
      (bruhatSchwartz_le_smooth u.val.property) u.property)

set_option maxHeartbeats 1500000 in
/-- Lemma D.3.6.1. The inclusion of compact Bruhat tests in the projective
decay space is continuous and has dense range. For second-countable groups their topology
is the strict countable limit verified by `bruhatCompactTest_strict`. -/
theorem bruhatCompactTest_continuous_injective_dense_decay (hm : IsProperMap m) (hI : I.Nonempty) :
    let j := bruhatCompactTest_toModulatedExponentialDecay m I
    Continuous j ∧ Injective j ∧ DenseRange j := by
  let j := bruhatCompactTest_toModulatedExponentialDecay m I
  refine ⟨?_, ?_, ?_⟩
  · change Continuous[inferInstance, ⨅ a : I,
      TopologicalSpace.induced (modulatedExponentialDecay_twist m I a) inferInstance] j
    apply continuous_iInf_rng.mpr
    intro a
    apply continuous_induced_rng.mpr
    let L := (modulatedExponentialDecay_twist m I a).comp j
    change Continuous L
    apply (locallyConvexFinal_continuous_iff (fun i : BruhatCompactTestIndex G => i.inclusion) L).mpr
    intro i
    have he : (L.comp i.inclusion : i.Space → BruhatSchwartz G) =
        i.1.inclusionCLM ∘ compactTestStage_weight m a i := by
      funext u
      apply Subtype.ext
      funext g
      exact (compactTestStage_realize_weight m a i u g).symm
    rw [he]
    exact i.1.inclusionCLM.continuous.comp (compactTestStage_weight_continuous m a i)
  · intro u v h
    apply BruhatCompactTest.val_injective
    apply Subtype.ext
    exact congrArg (fun z : ModulatedExponentialDecay m I => z.val) h
  · intro f
    apply closure_mono _ (dense_modulatedExponentialDecay_smooth_compactSupport m I hm hI f)
    rintro u ⟨hu, hc⟩
    obtain ⟨v, hv⟩ := (exists_bruhatCompactTest_iff u.val).mpr ⟨hu, hc⟩
    exact ⟨v, Subtype.ext hv⟩

end

end Masullo
