import ModulatedDecayCountable
import BruhatSchwartzStructure

open Bornology Function Set Topology
open scoped Uniformity

namespace Masullo

noncomputable section

universe u

set_option maxHeartbeats 2100000

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ) (I : Set ℝ)

/-- With proper surjective modulation, the whole-group stages admit a
monotone cofinal sequence. -/
theorem exists_wholeBruhatStage_cofinal [SecondCountableTopology G]
    (hm : IsProperMap m) (hms : Surjective m) :
    ∃ p : ℕ → WholeBruhatStage G, Monotone (fun n => (p n).val.1) ∧
      ∀ q : WholeBruhatStage G, ∃ n, q.val.1 ≤ (p n).val.1 := by
  obtain ⟨P,hP,hCov⟩ := lcaStructuralPairs_cofinalSequence (G := G)
  obtain ⟨q,hq,_⟩ := exists_modulatedBruhat_character_stage m hm hms (1 : PontryaginDual G)
  obtain ⟨N,hN⟩ := hCov q
  let p (n : ℕ) : WholeBruhatStage G :=
    ⟨⟨P (n+N),Classical.choice (P (n+N)).quotient_elementary⟩,top_unique
      (hq ▸ hN.1.trans (hP (Nat.le_add_left N n)).1)⟩
  refine ⟨p, fun a b hab => hP (Nat.add_le_add_right hab N),fun q => ?_⟩
  obtain ⟨n,hn⟩ := hCov q.val.1
  exact ⟨n,hn.trans (hP (Nat.le_add_right n N))⟩

/-- The full decay space is barrelled, by the Fréchet property of its stages. -/
theorem modulatedDecay_barrelled (hI : I.Nonempty) :
    BarrelledSpace ℂ (ModulatedExponentialInductive m I) := by
  constructor
  intro q hq
  apply locallyConvexFinal_seminorm_continuous
    (fun p : WholeBruhatStage G => ModulatedExponentialInductive.stageMap (m := m) (I := I) p)
  intro p
  let X := WholeBruhatDecayStage m I p
  letI : TopologicalSpace.MetrizableSpace X :=
    (wholeBruhatDecayStage_metrizable_secondCountable m hI p).1
  letI : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  letI : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace X := WholeBruhatDecayStage.complete m I hI p
  letI : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul
  letI : (𝓤 X).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  letI : BaireSpace X := BaireSpace.of_completelyPseudoMetrizable
  exact (q.comp (ModulatedExponentialInductive.stageMap p)).continuous_of_lowerSemicontinuous
    (hq.comp (ModulatedExponentialInductive.stageMap_continuous p))

/-- A bounded linear map out of the decay space to a locally convex space
is continuous. -/
theorem modulatedDecay_linear_continuous_of_bounded (hI : I.Nonempty)
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y]
    (L : ModulatedExponentialInductive m I →ₗ[ℂ] Y)
    (hL : ∀ B : Set (ModulatedExponentialInductive m I), IsVonNBounded ℂ B →
      IsVonNBounded ℂ (L '' B)) : Continuous L := by
  letI : IsTopologicalAddGroup Y := (PolynormableSpace.withSeminorms ℂ Y).topologicalAddGroup
  apply (locallyConvexFinal_continuous_iff
    (fun p : WholeBruhatStage G => ModulatedExponentialInductive.stageMap (m := m) (I := I) p) L).mpr
  intro p
  let X := WholeBruhatDecayStage m I p
  letI : TopologicalSpace.MetrizableSpace X :=
    (wholeBruhatDecayStage_metrizable_secondCountable m hI p).1
  letI : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul
  apply LinearMap.continuous_of_locally_bounded
  intro C hC
  let j : X →L[ℂ] ModulatedExponentialInductive m I :=
    ⟨ModulatedExponentialInductive.stageMap p, ModulatedExponentialInductive.stageMap_continuous p⟩
  change IsVonNBounded ℂ ((fun x : X => L (j x)) '' C)
  exact Set.image_image (⇑L) (⇑j) C ▸ hL _ (hC.image j)


/-- At abscissa zero the twist is the continuous injective inclusion of
the actual functions into the Schwartz–Bruhat space. -/
theorem modulatedDecay_zero_inclusion (hI : (0 : ℝ) ∈ I) :
    ∃ j : ModulatedExponentialInductive m I →L[ℂ] BruhatSchwartz G,
      Injective j ∧ ∀ f, (j f).val = f.val := by
  let j := modulatedDecayTwistCLM m I ⟨0,hI⟩
  have hj (f : ModulatedExponentialInductive m I) : (j f).val = f.val := by
    funext x
    change Real.exp (0 * (m x).toAdd) • f.val x = f.val x
    rw [zero_mul, Real.exp_zero, one_smul]
  refine ⟨j,fun f g h => ModulatedExponentialInductive.algebraicEquiv.injective
    (Subtype.ext ((hj f).symm.trans ((congrArg Subtype.val h).trans (hj g)))),hj⟩

end

end Masullo
