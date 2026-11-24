import SchwartzCurryingClosedSubspace
import PeriodicFirstSchwartzCurrying

open Set
open scoped SchwartzMap

namespace Masullo

noncomputable section

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {L : AddSubgroup Y}

/-- The scalar Schwartz model of a torus, with the chosen compact cutoff on its cover. -/
def scalarPeriodicSchwartz (w : PeriodicLocalization L) : Submodule ℂ 𝓢(Y, ℂ) where
  carrier := {f | IsLocalizedPeriodic w f}
  zero_mem' := by
    intro x k
    change w.weight (x + k.val) • (0 : ℂ) = w.weight x • 0
    simp
  add_mem' := by
    intro f g hf hg x k
    change w.weight (x + k.val) • (f x + g x) =
      w.weight x • (f (x + k.val) + g (x + k.val))
    rw [smul_add, smul_add, hf x k, hg x k]
  smul_mem' := by
    intro c f hf x k
    change w.weight (x + k.val) • (c • f x) = w.weight x • (c • f (x + k.val))
    rw [smul_comm (w.weight (x + k.val)) c, smul_comm (w.weight x) c, hf x k]

theorem isClosed_scalarPeriodicSchwartz (w : PeriodicLocalization L) :
    IsClosed (scalarPeriodicSchwartz w : Set 𝓢(Y, ℂ)) := by
  have he : (scalarPeriodicSchwartz w : Set 𝓢(Y, ℂ)) =
      ⋂ x : Y, ⋂ k : L, {f : 𝓢(Y, ℂ) | w.weight (x + k.val) • f x =
        w.weight x • f (x + k.val)} := by
    ext f
    change IsLocalizedPeriodic w f ↔ _
    simp only [IsLocalizedPeriodic, mem_iInter, mem_ofPred_eq]
  rw [he]
  refine isClosed_iInter fun x => isClosed_iInter fun k => ?_
  have h (y : Y) : Continuous (fun f : 𝓢(Y, ℂ) => f y) :=
    ((BoundedContinuousFunction.evalCLM ℂ y).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ Y ℂ)).continuous
  have h₁ : Continuous (fun f : 𝓢(Y, ℂ) => w.weight (x + k.val) * f x) := continuous_const.mul (h x)
  have h₂ : Continuous (fun f : 𝓢(Y, ℂ) => w.weight x * f (x + k.val)) := continuous_const.mul (h (x + k.val))
  simpa only [smul_eq_mul] using isClosed_eq h₁ h₂

/-- Currying on a Euclidean space times a torus, expressed through the
closed localization equations in the second variable. -/
theorem exists_secondPeriodicSchwartz_curryEquiv {a b : ℕ} {I : Type*} [Countable I]
    {L : AddSubgroup (EuclideanSpace ℝ (Fin b))} (w : PeriodicLocalization L)
    {p : SeminormFamily ℂ (scalarPeriodicSchwartz w) I} (hp : WithSeminorms p) :
    ∃ C : (schwartzWithSlicesIn (X := EuclideanSpace ℝ (Fin a)) (scalarPeriodicSchwartz w)) ≃L[ℂ]
        (localBanachSchwartz (X := EuclideanSpace ℝ (Fin a)) hp),
      ∀ f x i, (C f).val i x =
        localBanachDenseMap (p i) (schwartzWithSlicesIn_slice (scalarPeriodicSchwartz w) x f) :=
  exists_schwartzCurry_closedSubspaceEquiv (scalarPeriodicSchwartz w) (isClosed_scalarPeriodicSchwartz w) hp

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The joint Schwartz model with independent cutoff equations in both variables. -/
def bothPeriodicSchwartz {K : AddSubgroup X} (v : PeriodicLocalization K)
    (w : PeriodicLocalization L) :
    Submodule ℂ (schwartzWithSlicesIn (X := X) (scalarPeriodicSchwartz w)) :=
  (firstPeriodicSchwartz (Y := Y) v).comap
    (schwartzWithSlicesIn (X := X) (scalarPeriodicSchwartz w)).subtype

set_option maxHeartbeats 2200000 in
/-- Currying on a product of two tori, with the same cutoffs on the joint and curried sides. -/
theorem exists_bothPeriodicSchwartz_curryEquiv {a b : ℕ} {I : Type*} [Countable I]
    {K : AddSubgroup (EuclideanSpace ℝ (Fin a))} (v : PeriodicLocalization K)
    {L : AddSubgroup (EuclideanSpace ℝ (Fin b))} (w : PeriodicLocalization L)
    {p : SeminormFamily ℂ (scalarPeriodicSchwartz w) I} (hp : WithSeminorms p) :
    ∃ C : (bothPeriodicSchwartz v w) ≃L[ℂ] (localBanachPeriodic v hp),
      ∀ f x i, (C f).val.val i x =
        localBanachDenseMap (p i) (schwartzWithSlicesIn_slice (scalarPeriodicSchwartz w) x f.val) := by
  let X := EuclideanSpace ℝ (Fin a)
  let S := scalarPeriodicSchwartz w
  let A := schwartzWithSlicesIn (X := X) S
  let F (x : X) := schwartzWithSlicesIn_slice S x
  let U : Submodule ℂ A := bothPeriodicSchwartz v w
  let W : Submodule ℂ (localBanachSchwartz (X := X) hp) :=
    localizedPeriodicSubmodule v (localBanachDiagonal hp).range
  obtain ⟨C, hC⟩ := exists_secondPeriodicSchwartz_curryEquiv (a := a) w hp
  have hm (f : A) : f ∈ U ↔ C f ∈ W := by
    change (∀ y, IsLocalizedPeriodic v (fun x => f.val (x, y))) ↔
      (∀ i, IsLocalizedPeriodic v ((C f).val i))
    constructor
    · intro hf i x k
      have he : v.weight (x + k.val) • F x f = v.weight x • F (x + k.val) f := by
        apply Subtype.ext
        apply SchwartzMap.ext
        intro y
        exact hf y x k
      change v.weight (x + k.val) • (C f).val i x = v.weight x • (C f).val i (x + k.val)
      rw [hC f x i, hC f (x + k.val) i]
      simpa only [map_smul] using congrArg (localBanachDenseMap (p i)) he
    · intro hf y x k
      have he : v.weight (x + k.val) • F x f = v.weight x • F (x + k.val) f := by
        apply (localBanachDiagonal_isInducing hp).isEmbedding.injective
        funext i
        change localBanachDenseMap (p i) _ = localBanachDenseMap (p i) _
        have hq : v.weight (x + k.val) • (C f).val i x =
            v.weight x • (C f).val i (x + k.val) := hf i x k
        rw [hC f x i, hC f (x + k.val) i] at hq
        simpa only [map_smul] using hq
      exact congrArg (fun g : S => g.val y) he
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
