import IdelicStageFaithfulness
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

open Function NumberField Module Topology

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff

/-- The split Haar formula integrates over the manuscript's norm-one group. -/
theorem ideleClassLogNorm_ker_eq_normOne :
    (ideleClassLogNorm F).ker = normOneIdeleClass F := by
  ext g
  change Multiplicative.ofAdd (Real.log (ideleClassNorm F g)) =
    Multiplicative.ofAdd (0 : ℝ) ↔ ideleClassNorm F g = 1
  constructor
  · intro hg
    have hlog := Multiplicative.ofAdd.injective hg
    exact (Real.exp_log (ideleClassNorm_pos F g)).symm.trans
      ((congrArg Real.exp hlog).trans Real.exp_zero)
  · intro hg
    rw [hg, Real.log_one]

set_option maxHeartbeats 10000000 in
/-- The common global directions project to a basis on every refinement of
a single whole-group stage. The given radial section is the first vector. -/
theorem exists_ideleClass_cofinal_basis_directions
    (τ : Multiplicative ℝ →ₜ* IdeleClass F)
    (hτ : RightInverse τ (ideleClassLogNorm F)) :
    let d := Module.finrank ℚ F - 1
    ∃ P₀ : WholeBruhatStage (IdeleClass F),
    ∃ γ : Fin (d + 1) → Multiplicative ℝ →ₜ* IdeleClass F,
      γ 0 = τ ∧ (∀ (i : Fin d) t, ideleClassLogNorm F (γ i.succ t) = 1) ∧
      ∀ P : WholeBruhatStage (IdeleClass F), P.val.1.kernel ≤ P₀.val.1.kernel →
        ∃ B : Basis (Fin (d + 1)) ℝ
          (EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)),
          ∀ i, P.coordinates.comp (γ i) = elementaryOneParameter (B i) := by
  obtain ⟨P₀, hP₀⟩ := exists_ideleClassStage_bijective_archimedeanVelocity F
  obtain ⟨γ, hγ₀, hγ₁, hγ⟩ := exists_ideleClass_spanning_directions F τ hτ
  refine ⟨P₀, γ, hγ₀, hγ₁, fun P hP => ?_⟩
  obtain ⟨L, hL, _⟩ := hP₀ P hP
  obtain ⟨v, hv, hvel⟩ := hγ P
  let X := EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)
  have hdim : Module.finrank ℝ (mixedEmbedding.mixedSpace F) = Module.finrank ℝ X :=
    (LinearEquiv.ofBijective L hL).finrank_eq
  have hc : Fintype.card (Fin (Module.finrank ℚ F - 1 + 1)) =
      Module.finrank ℝ X := by
    rw [← hdim, mixedEmbedding.finrank, Fintype.card_fin]
    have hn : 0 < Module.finrank ℚ F := Module.finrank_pos
    omega
  let B := basisOfTopLeSpanOfCardEqFinrank v hv.ge hc
  refine ⟨B, fun i => ?_⟩
  have hBi : B i = v i := by simp [B]
  exact hBi.symm ▸ hvel i


end
end Masullo
