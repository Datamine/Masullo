import ModulatedExponentialInductive
import BruhatSchwartzTranslation
import ElementarySchwartzTranslationContinuity

open Filter Function Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ) (I : Set ℝ)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
private theorem modulation_weight_translate (a : ℝ) (f : G → ℂ) (g x : G) :
    modulatedExponentialWeight m a (fun y => f (g⁻¹ * y)) x =
      Real.exp (a * (m g).toAdd) • modulatedExponentialWeight m a f (g⁻¹ * x) := by
  simp only [modulatedExponentialWeight_apply, smul_smul, ← Real.exp_add, map_mul, map_inv]
  congr 2
  change a * (m x).toAdd = a * (m g).toAdd + a * (-(m g).toAdd + (m x).toAdd)
  ring

namespace WholeBruhatDecayStage

variable (p : WholeBruhatStage G)

private def lift (g : G) : p.val.1.upper.val := ⟨g, p.property.symm ▸ Subgroup.mem_top g⟩

private def translateTwist (a : I) (g : G) (f : WholeBruhatDecayStage m I p) : p.val.Space :=
  (Real.exp ((a : ℝ) * (m g).toAdd) : ℂ) •
    elementarySchwartz_translate (p.val.1.stageCoordinates p.val.2 (lift p g⁻¹)).toAdd (twist p a f)

set_option maxHeartbeats 1200000 in
private theorem realize_translateTwist (a : I) (g : G) (f : WholeBruhatDecayStage m I p) :
    p.val.realize (translateTwist m I p a g f) =
      modulatedExponentialWeight m a (fun x => f.val (g⁻¹ * x)) := by
  funext x
  unfold translateTwist
  rw [map_smul, p.val.realize_translate, realize_twist]
  change Real.exp ((a : ℝ) * (m g).toAdd) • modulatedExponentialWeight m a f.val (x * g⁻¹) = _
  rw [mul_comm x, modulation_weight_translate]

/-- Translation preserves every fixed-quotient exponential stage. -/
def translate (g : G) (f : WholeBruhatDecayStage m I p) : WholeBruhatDecayStage m I p :=
  algebraicEquiv.symm ⟨fun x => f.val (g⁻¹ * x),
    (Submodule.mem_iInf _).mpr fun a => ⟨translateTwist m I p a g f, realize_translateTwist m I p a g f⟩⟩

set_option maxHeartbeats 1800000 in
/-- The weighted translations are jointly continuous on each whole-group
stage in the projective topology of all its twists. -/
theorem continuous_translate :
    Continuous (fun z : G × WholeBruhatDecayStage m I p => translate m I p z.1 z.2) := by
  refine (continuous_iff _).mpr fun a => ?_
  let T (z : G × WholeBruhatDecayStage m I p) := translateTwist m I p a z.1 z.2
  have he : twist p a ∘ (fun z : G × WholeBruhatDecayStage m I p => translate m I p z.1 z.2) = T := by
    funext z
    apply p.val.1.realizeSchwartz_injective p.val.2
    exact (realize_twist p a (translate m I p z.1 z.2)).trans
      (realize_translateTwist m I p a z.1 z.2).symm
  rw [he]
  have hg : Continuous (fun g : G => (p.val.1.stageCoordinates p.val.2 (lift p g⁻¹)).toAdd) :=
    continuous_toAdd.comp ((p.val.1.stageCoordinates p.val.2).continuous.comp
      (continuous_inv.subtype_mk _))
  have hf : Continuous (twist p a : WholeBruhatDecayStage m I p → p.val.Space) :=
    (continuous_iff (id : WholeBruhatDecayStage m I p → _)).mp continuous_id a
  have ht : Continuous (fun z : G × WholeBruhatDecayStage m I p =>
      elementarySchwartz_translate (p.val.1.stageCoordinates p.val.2 (lift p z.1⁻¹)).toAdd (twist p a z.2)) :=
    (@continuous_elementarySchwartz_translate p.val.2.realDim p.val.2.torusDim p.val.2.latticeRank
      p.val.2.finiteFactor p.val.2.finiteGroup p.val.2.finiteTopology p.val.2.finiteDiscrete
      (Finite.of_fintype _)).comp ((hg.comp continuous_fst).prodMk (hf.comp continuous_snd))
  letI : ContinuousSMul ℂ p.val.Space := (PolynormableSpace.withSeminorms ℂ p.val.Space).continuousSMul
  have hscalar : Continuous (fun g : G => (Real.exp ((a : ℝ) * (m g).toAdd) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul (continuous_toAdd.comp m.continuous)))
  exact (hscalar.comp continuous_fst).smul ht

end WholeBruhatDecayStage

namespace ModulatedExponentialInductive

set_option maxHeartbeats 1300000 in
/-- Left translation, represented by its values as a function. -/
def translate (g : G) : ModulatedExponentialInductive m I →ₗ[ℂ] ModulatedExponentialInductive m I where
  toFun f := algebraicEquiv.symm ⟨fun x => f.val (g⁻¹ * x), by
    apply (Submodule.mem_iInf _).mpr
    intro a
    let u := modulatedExponentialDecay_twist m I a (algebraicEquiv f)
    have he : modulatedExponentialWeight m a (fun x => f.val (g⁻¹ * x)) =
        (Real.exp ((a : ℝ) * (m g).toAdd) : ℂ) • (bruhatSchwartz_translate g u).val := by
      funext x
      rw [modulation_weight_translate, Pi.smul_apply, bruhatSchwartz_translate_apply]
      rfl
    change modulatedExponentialWeight m a (fun x => f.val (g⁻¹ * x)) ∈ bruhatSchwartzSubmodule
    rw [he]
    exact bruhatSchwartzSubmodule.smul_mem _ (bruhatSchwartz_translate g u).property⟩
  map_add' _ _ := algebraicEquiv.injective (Subtype.ext rfl)
  map_smul' _ _ := algebraicEquiv.injective (Subtype.ext rfl)

@[simp] theorem translate_apply (g : G) (f : ModulatedExponentialInductive m I) (x : G) :
    (translate m I g f).val x = f.val (g⁻¹ * x) := rfl

@[simp] theorem translate_one (f : ModulatedExponentialInductive m I) :
    translate m I (1 : G) f = f := by
  apply algebraicEquiv.injective
  apply Subtype.ext
  funext x
  change f.val ((1 : G)⁻¹ * x) = f.val x
  rw [inv_one, one_mul]

theorem translate_mul (g h : G) (f : ModulatedExponentialInductive m I) :
    translate m I (g * h) f = translate m I g (translate m I h f) := by
  apply algebraicEquiv.injective
  apply Subtype.ext
  funext x
  change f.val ((g * h)⁻¹ * x) = f.val (h⁻¹ * (g⁻¹ * x))
  rw [mul_inv_rev, mul_assoc]

set_option maxHeartbeats 1500000 in
/-- The left action is jointly continuous for the manuscript's inductive
decay topology. -/
theorem continuous_translate (hm : IsProperMap m) (hms : Surjective m) (hI : I.Nonempty) :
    Continuous (fun z : G × ModulatedExponentialInductive m I => translate m I z.1 z.2) := by
  apply locallyConvexFinal_continuous_family
    (fun p : WholeBruhatStage G => stageMap (m := m) (I := I) p) (translate m I)
  · intro f
    obtain ⟨p, hp⟩ := exists_wholeBruhatStage_decay m I hm hms hI (algebraicEquiv f)
    let u : WholeBruhatDecayStage m I p :=
      WholeBruhatDecayStage.algebraicEquiv.symm ⟨f.val, (Submodule.mem_iInf _).mpr hp⟩
    exact ⟨p, u, algebraicEquiv.injective (Subtype.ext rfl)⟩
  · intro p
    have he : (fun z : G × WholeBruhatDecayStage m I p => translate m I z.1 (stageMap p z.2)) =
        stageMap p ∘ (fun z : G × WholeBruhatDecayStage m I p =>
          WholeBruhatDecayStage.translate m I p z.1 z.2) := by
      funext z
      exact algebraicEquiv.injective (Subtype.ext rfl)
    rw [he]
    exact (stageMap_continuous p).comp (WholeBruhatDecayStage.continuous_translate m I p)

end ModulatedExponentialInductive

end

end Masullo
