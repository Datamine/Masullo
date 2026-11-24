import EuclideanSchwartzUncurrying
import PeriodicBanachCoordinates

open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {L : AddSubgroup X}

/-- The joint Schwartz tests localized in the first variable of a product. -/
def firstPeriodicSchwartz (b : PeriodicLocalization L) : Submodule ℂ 𝓢(X × Y, ℂ) where
  carrier := {f | ∀ y, IsLocalizedPeriodic b (fun x => f (x, y))}
  zero_mem' := by
    intro y x k
    change b.weight (x + k.val) • (0 : ℂ) = b.weight x • 0
    simp
  add_mem' := by
    intro f g hf hg y x k
    change b.weight (x + k.val) • (f (x, y) + g (x, y)) =
      b.weight x • (f (x + k.val, y) + g (x + k.val, y))
    rw [smul_add, smul_add, hf y x k, hg y x k]
  smul_mem' := by
    intro c f hf y x k
    change b.weight (x + k.val) • (c • f (x, y)) =
      b.weight x • (c • f (x + k.val, y))
    rw [smul_comm (b.weight (x + k.val)) c, smul_comm (b.weight x) c, hf y x k]

set_option maxHeartbeats 800000 in
/-- The canonical Schwartz currying equivalence restricts to the mixed
case with a torus in the first variable. Both sides use the same compact cutoff on its cover. -/
theorem exists_firstPeriodicSchwartz_curryEquiv {a b : ℕ} {I : Type*} [Countable I]
    {L : AddSubgroup (EuclideanSpace ℝ (Fin a))} (w : PeriodicLocalization L)
    {p : SeminormFamily ℂ 𝓢(EuclideanSpace ℝ (Fin b), ℂ) I} (hp : WithSeminorms p) :
    ∃ C : (firstPeriodicSchwartz (Y := EuclideanSpace ℝ (Fin b)) w) ≃L[ℂ]
        (localBanachPeriodic w hp),
      ∀ f x i, (C f).val.val i x = localBanachDenseMap (p i) (schwartzSlice x f.val) := by
  let X := EuclideanSpace ℝ (Fin a)
  let Y := EuclideanSpace ℝ (Fin b)
  let A := 𝓢(X × Y, ℂ)
  let U := firstPeriodicSchwartz (Y := Y) w
  let W := localizedPeriodicSubmodule w (localBanachDiagonal hp).range
  obtain ⟨C, hC⟩ := exists_schwartzCurryEquiv (a := a) (b := b) hp
  have hm (f : A) : f ∈ U ↔ C f ∈ W := by
    constructor
    · intro hf i x k
      have he : w.weight (x + k.val) • schwartzSlice x f =
          w.weight x • schwartzSlice (x + k.val) f := by
        apply SchwartzMap.ext
        intro y
        exact hf y x k
      change w.weight (x + k.val) • (C f).val i x =
        w.weight x • (C f).val i (x + k.val)
      rw [hC f x i, hC f (x + k.val) i]
      simpa only [map_smul] using congrArg (localBanachDenseMap (p i)) he
    · intro hf y x k
      have he : w.weight (x + k.val) • schwartzSlice x f =
          w.weight x • schwartzSlice (x + k.val) f := by
        apply (localBanachDiagonal_isInducing hp).isEmbedding.injective
        funext i
        change localBanachDenseMap (p i) _ = localBanachDenseMap (p i) _
        have hq : w.weight (x + k.val) • (C f).val i x =
            w.weight x • (C f).val i (x + k.val) := hf i x k
        rw [hC f x i, hC f (x + k.val) i] at hq
        simpa only [map_smul] using hq
      exact congrArg (fun g : 𝓢(Y, ℂ) => g y) he
  have hmap : U.map C.toLinearEquiv.toLinearMap = W := by
    ext z
    change (∃ f ∈ U, C f = z) ↔ z ∈ W
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (hm f).mp hf
    · intro hz
      exact ⟨C.symm z, (hm _).mpr (by simpa using hz), C.apply_symm_apply z⟩
  exact ⟨C.ofSubmodules U W hmap, fun f x i => hC f.val x i⟩


end
end Masullo
