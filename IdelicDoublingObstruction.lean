import ArchimedeanFundamentalDomain
import DoublingSequences

open Filter Function IsDedekindDomain NumberField NumberField.Units
open NumberField.Units.dirichletUnitTheorem Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

theorem archRegulatorLog_nontrivial_kernel :
    ∃ a : archNormOne F, a ≠ 1 ∧ archRegulatorLog F a = 1 := by
  let u : (𝓞 F)ˣ := -1
  let a := globalUnitArch F u
  have hU : u ∈ NumberField.Units.torsion F := by
    rw [NumberField.Units.mem_torsion]
    intro w
    rw [← InfinitePlace.norm_embedding_eq]
    change ‖w.embedding (-1)‖ = 1
    rw [map_neg, map_one, norm_neg, norm_one]
  have hl : archRegulatorLog F a = 1 := by
    rw [show a = globalUnitArch F u from rfl, archRegulatorLog_globalUnit,
      (logEmbedding_eq_zero_iff (K := F)).mpr hU]
    rfl
  have ha : a ≠ 1 := by
    intro h
    let w : InfinitePlace F := Classical.choice inferInstance
    have he := congrArg (fun x : archNormOne F => x.val.val w) h
    change (algebraMap F w.Completion (-1)) = 1 at he
    have hs := (algebraMap F w.Completion).injective (he.trans (map_one _).symm)
    exact one_ne_zero (CharZero.neg_eq_self_iff.mp hs)
  exact ⟨a, ha, hl⟩

/-- Shrinking boxes in the logarithmic coordinates leave the kernel
in every inverse image, so they cannot give a neighborhood base. -/
theorem printed_archLogBoxes_not_cofinal (P : ℕ → Set (logSpace F)) (hP : ∀ k, 0 ∈ P k) :
    ¬ CofinalAtOne (fun k => (fun a => (archRegulatorLog F a).toAdd) ⁻¹' P k) := by
  intro h
  obtain ⟨a, ha, hₐ⟩ := archRegulatorLog_nontrivial_kernel F
  letI : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  have hV : ({a}ᶜ : Set (archNormOne F)) ∈ 𝓝 (1 : archNormOne F) :=
    compl_singleton_mem_nhds ha.symm
  obtain ⟨k, hk⟩ := h _ hV
  have hx : a ∈ (fun a => (archRegulatorLog F a).toAdd) ⁻¹' P k := by
    change (archRegulatorLog F a).toAdd ∈ P k
    rw [hₐ]
    exact hP k
  exact (hk hx) (mem_singleton a)

/-- The printed radius boxes have the obstruction at every stage. -/
theorem printed_archLogCubes_not_cofinal :
    ¬ CofinalAtOne (fun k => (fun a => (archRegulatorLog F a).toAdd) ⁻¹'
      {x : logSpace F | ∀ i, |(regulatorBasis F).repr x i| < 1 / ((k : ℝ) + 1)}) := by
  apply printed_archLogBoxes_not_cofinal F
  intro k
  change ∀ i, |(regulatorBasis F).repr 0 i| < 1 / ((k : ℝ) + 1)
  intro i
  rw [map_zero, Finsupp.zero_apply, abs_zero]
  positivity

/-- The modulus interval printed in A.5.2.15 and A.5.2.17 fails
inversion symmetry already at index two. -/
theorem printed_modulusInterval_not_inversion_symmetric :
    ∃ t : ℝ, 0 < t ∧ t ∈ Ioo (1 - (1 : ℝ) / 2) (1 + (1 : ℝ) / 2) ∧
      t⁻¹ ∉ Ioo (1 - (1 : ℝ) / 2) (1 + (1 : ℝ) / 2) := by
  refine ⟨3 / 5, by norm_num, by norm_num, ?_⟩
  rintro ⟨_, h⟩
  norm_num at h


end

end Masullo
