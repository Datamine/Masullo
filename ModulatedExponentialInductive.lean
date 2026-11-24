import ModulatedExponentialDecay

open Filter Function Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 1100000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ) (I : Set ℝ)

/-- For a modulated group the whole group is an admissible upper subgroup.
These stages are the quotients by the compact kernels of Definition D.3.3.3. -/
abbrev WholeBruhatStage (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  {p : BruhatSchwartzStage G // p.1.upper.val = ⊤}

set_option maxHeartbeats 900000 in
/-- Every structural stage refines to one with the whole group as its upper subgroup. -/
theorem exists_wholeBruhatStage_refinement (hm : IsProperMap m) (hms : Surjective m)
    (p : BruhatSchwartzStage G) :
    ∃ q : WholeBruhatStage G, p.1 ≤ q.val.1 := by
  obtain ⟨J, hJ⟩ := exists_modulatedBruhat_upper_eq_top m hm hms
  let Q : LCAStructuralPair G :=
    ⟨J, p.1.kernel, p.1.kernel_closed, p.1.annihilator_open, p.1.annihilator_compactlyGenerated,
      by rw [hJ]; exact le_top⟩
  obtain ⟨q⟩ := Q.quotient_elementary
  refine ⟨⟨⟨Q, q⟩, hJ⟩, ?_⟩
  show p.1.upper.val ≤ J.val ∧ Q.kernel ≤ p.1.kernel
  exact ⟨by rw [hJ]; exact le_top, le_rfl⟩

set_option maxHeartbeats 1600000 in
/-- Once one twist is represented on a whole-group quotient, every other
Schwartz twist descends to that same quotient. -/
theorem wholeBruhatStage_exponential_twist_mem_range (p : WholeBruhatStage G)
    {f : G → ℂ} {a b : ℝ} (ha : modulatedExponentialWeight m a f ∈ p.val.realize.range)
    (hb : modulatedExponentialWeight m b f ∈ bruhatSchwartzSubmodule (G := G)) :
    modulatedExponentialWeight m b f ∈ p.val.realize.range := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨q, v, hv⟩ := hb
  let P := p.val
  letI := (lcaStructuralPairs_filtered (G := G)).2
  obtain ⟨R, hPR, hQR⟩ := exists_ge_ge P.1 q.1
  obtain ⟨r⟩ := R.quotient_elementary
  let Rr : BruhatSchwartzStage G := ⟨R, r⟩
  let w := q.transition Rr hQR v
  have hw : Rr.realize w = modulatedExponentialWeight m b f :=
    (congrArg Subtype.val (q.inclusion_transition Rr hQR v)).trans hv
  have hup : R.upper.val = P.1.upper.val := by
    refine le_antisymm ?_ hPR.1
    rw [show P.1.upper.val = ⊤ from p.property]
    exact le_top
  have hru : R.upper.val ≤ P.1.upper.val := hup.le
  have hrk : R.kernel ≤ P.1.kernel := hPR.2
  let φ := R.stageCoordinateMap P.1 hru hrk r P.2
  let φ₀ := φ.toMonoidHom.toAdditive
  have ho : IsOpenMap φ := P.2.equiv.toHomeomorph.isOpenMap.comp
    ((R.stageMap_isOpenMap P.1 hru hrk).comp r.equiv.symm.toHomeomorph.isOpenMap)
  have hs : Surjective φ := P.2.equiv.surjective.comp
    ((R.stageMap_surjective_of_upper_eq P.1 hru hrk hup).comp r.equiv.symm.surjective)
  let A := ElementaryLCAModel P.2.realDim P.2.torusDim P.2.latticeRank P.2.finiteFactor
  let M := (P.1.descendHom m (P.1.modulation_eq_one_on_kernel m)).comp
    (P.2.equiv.symm : Multiplicative A →ₜ* P.1.StageQuotient)
  let l : A →+ ℝ := M.toMonoidHom.toAdditive
  let g (z : A) := Real.exp ((b - a) * l z) • u z
  have hwp (x : P.1.upper.val) :
      g (P.1.stageCoordinates P.2 x).toAdd = modulatedExponentialWeight m b f x.val := by
    have hlog : l (P.1.stageCoordinates P.2 x).toAdd = (m x.val).toAdd := by
      change ((P.1.descendHom m (P.1.modulation_eq_one_on_kernel m))
        (P.2.equiv.symm (P.2.equiv (QuotientGroup.mk x)))).toAdd = _
      rw [P.2.equiv.symm_apply_apply, LCAStructuralPair.descendHom_mk]
    change Real.exp ((b - a) * l (P.1.stageCoordinates P.2 x).toAdd) •
      u (P.1.stageCoordinates P.2 x).toAdd = _
    rw [hlog, ← P.1.realizeSchwartz_apply_of_mem P.2 u x, hu,
      ← modulatedExponentialWeight_apply, modulatedExponentialWeight_add, sub_add_cancel]
  have hEq : g ∘ φ₀ = w.val := by
    funext z
    obtain ⟨x, hx⟩ := (r.equiv.surjective.comp QuotientGroup.mk_surjective) (Multiplicative.ofAdd z)
    have hφ : φ (Multiplicative.ofAdd z) =
        P.1.stageCoordinates P.2 (Subgroup.inclusion hru x) :=
      (congrArg φ hx.symm).trans (R.stageCoordinateMap_stageCoordinates P.1 hru hrk r P.2 x)
    change g (φ (Multiplicative.ofAdd z)).toAdd = w z
    rw [hφ, hwp]
    have hreal : Rr.realize w x.val = w z := by
      have he := R.realizeSchwartz_apply_of_mem r w x
      rw [show R.stageCoordinates r x = Multiplicative.ofAdd z from hx] at he
      exact he
    exact (congrFun hw.symm x.val).trans hreal
  have hmem := @elementarySchwartz_mem_of_openPullback
    Rr.2.realDim Rr.2.torusDim Rr.2.latticeRank P.2.realDim P.2.torusDim P.2.latticeRank
    Rr.2.finiteFactor P.2.finiteFactor
    Rr.2.finiteGroup Rr.2.finiteTopology Rr.2.finiteDiscrete (Finite.of_fintype _)
    P.2.finiteGroup P.2.finiteTopology P.2.finiteDiscrete (Finite.of_fintype _)
    φ₀ φ.continuous ho (fun y => hs (Multiplicative.ofAdd y)) w g hEq
  let z : P.Space := ⟨g, hmem⟩
  refine ⟨z, funext fun x => ?_⟩
  let x₀ : P.1.upper.val := ⟨x, p.property.symm ▸ Subgroup.mem_top x⟩
  exact (P.1.realizeSchwartz_apply_of_mem P.2 z x₀).trans (hwp x₀)

set_option maxHeartbeats 1000000 in
/-- All abscissa twists of a decay function are simultaneously realized
on one whole-group structural quotient. -/
theorem exists_wholeBruhatStage_decay (hm : IsProperMap m) (hms : Surjective m) (hI : I.Nonempty)
    (f : ModulatedExponentialDecay m I) :
    ∃ p : WholeBruhatStage G, ∀ a : I, modulatedExponentialWeight m a f.val ∈ p.val.realize.range := by
  obtain ⟨a, ha⟩ := hI
  let a₀ : I := ⟨a, ha⟩
  obtain ⟨P, u, hu⟩ := (modulatedExponentialDecay_twist m I a₀ f).property
  obtain ⟨Q, hpq⟩ := exists_wholeBruhatStage_refinement m hm hms P
  let w := P.transition Q.val hpq u
  have hw : Q.val.realize w = modulatedExponentialWeight m a f.val :=
    (congrArg Subtype.val (P.inclusion_transition Q.val hpq u)).trans hu
  exact ⟨Q, fun b => wholeBruhatStage_exponential_twist_mem_range m Q ⟨w, hw⟩
    (modulatedExponentialDecay_twist m I b f).property⟩

/-- All weighted functions are represented in the same structural quotient. -/
def wholeBruhatDecayStageSubmodule (p : WholeBruhatStage G) : Submodule ℂ (G → ℂ) :=
  ⨅ a : I, p.val.realize.range.comap (modulatedExponentialWeight m a)

def WholeBruhatDecayStage (p : WholeBruhatStage G) :=
  ↥(wholeBruhatDecayStageSubmodule m I p)

variable {m I}

namespace WholeBruhatDecayStage

variable {p : WholeBruhatStage G}

instance : AddCommGroup (WholeBruhatDecayStage m I p) :=
  inferInstanceAs (AddCommGroup (wholeBruhatDecayStageSubmodule m I p))

instance : Module ℂ (WholeBruhatDecayStage m I p) :=
  inferInstanceAs (Module ℂ (wholeBruhatDecayStageSubmodule m I p))

def algebraicEquiv : WholeBruhatDecayStage m I p ≃ₗ[ℂ] wholeBruhatDecayStageSubmodule m I p :=
  LinearEquiv.refl ℂ _

def val (f : WholeBruhatDecayStage m I p) : G → ℂ := (algebraicEquiv f).val

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
theorem property (f : WholeBruhatDecayStage m I p) (a : I) :
    modulatedExponentialWeight m a f.val ∈ p.val.realize.range :=
  (Submodule.mem_iInf _).mp (algebraicEquiv f).property a

def twist (p : WholeBruhatStage G) (a : I) :
    WholeBruhatDecayStage m I p →ₗ[ℂ] p.val.Space :=
  (LinearEquiv.ofInjective p.val.realize (p.val.1.realizeSchwartz_injective p.val.2)).symm.toLinearMap.comp
    (((modulatedExponentialWeight m a).comp
      ((wholeBruhatDecayStageSubmodule m I p).subtype.comp algebraicEquiv.toLinearMap)).codRestrict _
        (fun f => f.property a))

theorem realize_twist (p : WholeBruhatStage G) (a : I) (f : WholeBruhatDecayStage m I p) :
    p.val.realize (twist p a f) = modulatedExponentialWeight m a f.val :=
  LinearEquiv.ofInjective_symm_apply p.val.realize (h := p.val.1.realizeSchwartz_injective p.val.2)
    ⟨_, f.property a⟩

instance : TopologicalSpace (WholeBruhatDecayStage m I p) :=
  ⨅ a : I, TopologicalSpace.induced (twist p a) inferInstance

instance : PolynormableSpace ℂ (WholeBruhatDecayStage m I p) :=
  PolynormableSpace.iInf fun a => PolynormableSpace.induced (twist p a)

instance : IsTopologicalAddGroup (WholeBruhatDecayStage m I p) :=
  (PolynormableSpace.withSeminorms ℂ (WholeBruhatDecayStage m I p)).topologicalAddGroup

theorem continuous_iff {X : Type*} [TopologicalSpace X] (f : X → WholeBruhatDecayStage m I p) :
    Continuous f ↔ ∀ a : I, Continuous (twist p a ∘ f) := by
  change Continuous[inferInstance, ⨅ a : I, TopologicalSpace.induced (twist p a) inferInstance] f ↔ _
  exact continuous_iInf_rng.trans (forall_congr' fun _ => continuous_induced_rng)

theorem tendsto_iff {X : Type*} {F : Filter X} {f : X → WholeBruhatDecayStage m I p}
    {u : WholeBruhatDecayStage m I p} :
    Tendsto f F (𝓝 u) ↔ ∀ a : I, Tendsto (twist p a ∘ f) F (𝓝 (twist p a u)) := by
  change Tendsto f F (@nhds _ (⨅ a : I, TopologicalSpace.induced (twist p a) inferInstance) u) ↔ _
  rw [nhds_iInf, tendsto_iInf]
  simp only [nhds_induced, tendsto_comap_iff]

end WholeBruhatDecayStage

/-- The decay space with the inductive topology of Definition D.3.3.3. -/
def ModulatedExponentialInductive (m : G →ₜ* Multiplicative ℝ) (I : Set ℝ) :=
  ModulatedExponentialDecay m I

namespace ModulatedExponentialInductive

instance : AddCommGroup (ModulatedExponentialInductive m I) :=
  inferInstanceAs (AddCommGroup (ModulatedExponentialDecay m I))

instance : Module ℂ (ModulatedExponentialInductive m I) :=
  inferInstanceAs (Module ℂ (ModulatedExponentialDecay m I))

def algebraicEquiv : ModulatedExponentialInductive m I ≃ₗ[ℂ] ModulatedExponentialDecay m I :=
  LinearEquiv.refl ℂ _

def val (f : ModulatedExponentialInductive m I) : G → ℂ := (algebraicEquiv f).val

/-- The algebraic inclusion of a whole-group decay stage. -/
def stageMap (p : WholeBruhatStage G) :
    WholeBruhatDecayStage m I p →ₗ[ℂ] ModulatedExponentialInductive m I := by
  let L : WholeBruhatDecayStage m I p →ₗ[ℂ] (G → ℂ) :=
    (wholeBruhatDecayStageSubmodule m I p).subtype.comp WholeBruhatDecayStage.algebraicEquiv.toLinearMap
  refine algebraicEquiv.symm.toLinearMap.comp (L.codRestrict _ (fun f => ?_))
  apply (Submodule.mem_iInf _).mpr
  intro a
  obtain ⟨u, hu⟩ := f.property a
  exact ⟨p.val, u, hu⟩

instance : TopologicalSpace (ModulatedExponentialInductive m I) :=
  locallyConvexFinalTopology (fun p : WholeBruhatStage G => stageMap (m := m) (I := I) p)

instance : PolynormableSpace ℂ (ModulatedExponentialInductive m I) :=
  (locallyConvexFinal_withSeminorms
    (fun p : WholeBruhatStage G => stageMap (m := m) (I := I) p)).toPolynormableSpace

theorem stageMap_continuous (p : WholeBruhatStage G) :
    Continuous (stageMap (m := m) (I := I) p) :=
  locallyConvexFinal_stage_continuous (fun p : WholeBruhatStage G => stageMap (m := m) (I := I) p) p

end ModulatedExponentialInductive

variable (m I)

/-- The compact-test inclusion into the decay space with its inductive topology. -/
def bruhatCompactTest_toModulatedExponentialInductive :
    BruhatCompactTest G →ₗ[ℂ] ModulatedExponentialInductive m I :=
  ModulatedExponentialInductive.algebraicEquiv.symm.toLinearMap.comp
    (bruhatCompactTest_toModulatedExponentialDecay m I)

set_option maxHeartbeats 2200000 in
theorem bruhatCompactTest_continuous_inductiveDecay (hm : IsProperMap m) (hms : Surjective m) :
    Continuous (bruhatCompactTest_toModulatedExponentialInductive m I) := by
  let L := bruhatCompactTest_toModulatedExponentialInductive m I
  refine (locallyConvexFinal_continuous_iff (fun i : BruhatCompactTestIndex G => i.inclusion) L).mpr fun i => ?_
  obtain ⟨q, hq⟩ := exists_wholeBruhatStage_refinement m hm hms i.1
  let T := i.1.transition q.val hq
  have hT (a : I) (u : i.Space) :
      q.val.realize (T (compactTestStage_weight m a i u)) =
        modulatedExponentialWeight m a (i.1.realize u.val) := by
    have h := congrArg Subtype.val (i.1.inclusion_transition q.val hq (compactTestStage_weight m a i u))
    exact h.trans (funext fun x => compactTestStage_realize_weight m a i u x)
  let U (u : i.Space) : WholeBruhatDecayStage m I q :=
    WholeBruhatDecayStage.algebraicEquiv.symm ⟨i.1.realize u.val,
      (Submodule.mem_iInf _).mpr fun a => ⟨T (compactTestStage_weight m a i u), hT a u⟩⟩
  have hU : Continuous U := by
    apply (WholeBruhatDecayStage.continuous_iff U).mpr
    intro a
    have he : WholeBruhatDecayStage.twist q a ∘ U = T ∘ compactTestStage_weight m a i := by
      funext u
      apply q.val.1.realizeSchwartz_injective q.val.2
      exact (WholeBruhatDecayStage.realize_twist q a (U u)).trans (hT a u).symm
    rw [he]
    exact T.continuous.comp (compactTestStage_weight_continuous m a i)
  have he : (L.comp i.inclusion : i.Space → ModulatedExponentialInductive m I) =
      ModulatedExponentialInductive.stageMap q ∘ U := by
    funext u
    apply ModulatedExponentialInductive.algebraicEquiv.injective
    exact Subtype.ext rfl
  rw [he]
  exact (ModulatedExponentialInductive.stageMap_continuous q).comp hU

set_option maxHeartbeats 2200000 in
/-- A common logarithmic cutoff sequence converges inside one fixed decay
stage for all abscissae. -/
private theorem wholeBruhatDecayStage_compact_cutoffs (hm : IsProperMap m) (hI : I.Nonempty)
    (p : WholeBruhatStage G) (f : WholeBruhatDecayStage m I p) :
    ∃ U : ℕ → WholeBruhatDecayStage m I p, Tendsto U atTop (𝓝 f) ∧
      ∀ n, (U n).val ∈ bruhatSmoothSubmodule (G := G) ∧ HasCompactSupport (U n).val := by
  let P := p.val
  let A := ElementaryLCAModel P.2.realDim P.2.torusDim P.2.latticeRank P.2.finiteFactor
  let M := (P.1.descendHom m (P.1.modulation_eq_one_on_kernel m)).comp
    (P.2.equiv.symm : Multiplicative A →ₜ* P.1.StageQuotient)
  let l : A →+ ℝ := M.toMonoidHom.toAdditive
  have hl : Continuous l := continuous_toAdd.comp (M.continuous.comp continuous_ofAdd)
  choose u hu hu_eq using fun a : I =>
    @exists_elementarySchwartz_logCutoff_sequence P.2.realDim P.2.torusDim P.2.latticeRank
      P.2.finiteFactor P.2.finiteGroup P.2.finiteTopology P.2.finiteDiscrete (Finite.of_fintype _)
      l hl (WholeBruhatDecayStage.twist p a f)
  let w (n : ℕ) (g : G) := truncationMultiplier n (modulatedLog m g) * f.val g
  have he (a : I) (n : ℕ) : P.realize (u a n) = modulatedExponentialWeight m a (w n) := by
    funext g
    let x : P.1.upper.val := ⟨g, p.property.symm ▸ Subgroup.mem_top g⟩
    let y := (P.1.stageCoordinates P.2 x).toAdd
    have hy : l y = modulatedLog m g := by
      change ((P.1.descendHom m (P.1.modulation_eq_one_on_kernel m))
        (P.2.equiv.symm (P.2.equiv (QuotientGroup.mk x)))).toAdd = _
      rw [P.2.equiv.symm_apply_apply, LCAStructuralPair.descendHom_mk]
      rfl
    have hv : WholeBruhatDecayStage.twist p a f y =
        Real.exp ((a : ℝ) * (m g).toAdd) • f.val g :=
      (P.1.realizeSchwartz_apply_of_mem P.2 (WholeBruhatDecayStage.twist p a f) x).symm.trans
        (congrFun (WholeBruhatDecayStage.realize_twist p a f) g)
    calc
      P.realize (u a n) g = u a n y := P.1.realizeSchwartz_apply_of_mem P.2 (u a n) x
      _ = truncationMultiplier n (modulatedLog m g) * (Real.exp ((a : ℝ) * (m g).toAdd) • f.val g) :=
        (hu_eq a n y).trans (congrArg₂ (fun t z => truncationMultiplier n t * z) hy hv)
      _ = modulatedExponentialWeight m a (w n) g := mul_smul_comm _ _ _
  let U (n : ℕ) : WholeBruhatDecayStage m I p :=
    WholeBruhatDecayStage.algebraicEquiv.symm ⟨w n,
      (Submodule.mem_iInf _).mpr fun a => ⟨u a n, he a n⟩⟩
  refine ⟨U, WholeBruhatDecayStage.tendsto_iff.mpr (fun a => ?_), fun n => ?_⟩
  · have h : WholeBruhatDecayStage.twist p a ∘ U = u a := by
      funext n
      apply P.1.realizeSchwartz_injective P.2
      exact (WholeBruhatDecayStage.realize_twist p a (U n)).trans (he a n).symm
    rw [h]
    exact hu a
  · change w n ∈ bruhatSmoothSubmodule (G := G) ∧ HasCompactSupport (w n)
    constructor
    · obtain ⟨a, ha⟩ := hI
      let a₀ : I := ⟨a, ha⟩
      have hs := bruhatSmooth_realModulation_smul m (-a) (P.realize_smooth (u a₀ n))
      have hInv : (fun g => Real.exp (-a * (m g).toAdd) • P.realize (u a₀ n) g) = w n := by
        funext g
        rw [he a₀ n, modulatedExponentialWeight_apply, smul_smul, ← Real.exp_add]
        change Real.exp (-a * (m g).toAdd + a * (m g).toAdd) • w n g = w n g
        rw [neg_mul, neg_add_cancel, Real.exp_zero, one_smul]
      exact hInv ▸ hs
    · let R := 2 * ((n : ℝ) + 1)
      have hc : Continuous (modulatedLog m) := continuous_toAdd.comp m.continuous
      have hp : IsProperMap (modulatedLog m) := hm
      refine HasCompactSupport.intro' (hp.isCompact_preimage (isCompact_Icc (a := -R) (b := R)))
        (isClosed_Icc.preimage hc) fun g hg => ?_
      have hR : R < |modulatedLog m g| := lt_of_not_ge fun ht => hg (abs_le.mp ht)
      change truncationMultiplier n (modulatedLog m g) * f.val g = 0
      rw [truncationMultiplier_zero n hR, zero_mul]

set_option maxHeartbeats 1400000 in
/-- Lemma D.3.6.1 in the manuscript's inductive topology. -/
theorem bruhatCompactTest_inductiveDecay_continuous_injective_dense
    (hm : IsProperMap m) (hms : Surjective m) (hI : I.Nonempty) :
    let j := bruhatCompactTest_toModulatedExponentialInductive m I
    Continuous j ∧ Injective j ∧ DenseRange j := by
  let j := bruhatCompactTest_toModulatedExponentialInductive m I
  refine ⟨bruhatCompactTest_continuous_inductiveDecay m I hm hms, ?_, ?_⟩
  · intro u v h
    apply BruhatCompactTest.val_injective
    apply Subtype.ext
    exact congrArg (fun z : ModulatedExponentialInductive m I => z.val) h
  · intro f
    obtain ⟨p, hp⟩ := exists_wholeBruhatStage_decay m I hm hms hI
      (ModulatedExponentialInductive.algebraicEquiv f)
    let f₀ : WholeBruhatDecayStage m I p :=
      WholeBruhatDecayStage.algebraicEquiv.symm ⟨f.val, (Submodule.mem_iInf _).mpr hp⟩
    have hf : ModulatedExponentialInductive.stageMap p f₀ = f :=
      ModulatedExponentialInductive.algebraicEquiv.injective (Subtype.ext rfl)
    obtain ⟨U, hU, hCompact⟩ := wholeBruhatDecayStage_compact_cutoffs m I hm hI p f₀
    have ht : Tendsto (fun n => ModulatedExponentialInductive.stageMap p (U n)) atTop (𝓝 f) :=
      hf ▸ ((ModulatedExponentialInductive.stageMap_continuous p).tendsto f₀).comp hU
    apply mem_closure_of_tendsto ht
    apply Eventually.of_forall
    intro n
    obtain ⟨v, hv⟩ := (exists_bruhatCompactTest_iff (U n).val).mpr (hCompact n)
    exact ⟨v, ModulatedExponentialInductive.algebraicEquiv.injective (Subtype.ext hv)⟩

end

end Masullo
