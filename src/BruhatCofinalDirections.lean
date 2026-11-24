import BruhatStageSeparation
import ElementaryVelocity

open Function Module Set Topology

namespace Masullo.WholeBruhatStage

noncomputable section

variable {G V : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V] [TopologicalSpace V] [ContinuousSMul ℝ V]

omit [Module.Finite ℝ V] in
private theorem exists_stage_linear_velocity (P : WholeBruhatStage G)
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (e : Multiplicative V →ₜ* G)
    (he : ∀ c : Multiplicative ℝ →ₜ* G, ∃ x : V, ∀ t : ℝ,
      c (Multiplicative.ofAdd t) = e (Multiplicative.ofAdd (t • x))) :
    ∃ L : V →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)),
      Surjective L ∧ ∀ x t, P.coordinates (e (Multiplicative.ofAdd (t • x))) =
        elementaryOneParameter (L x) (Multiplicative.ofAdd t) := by
  let q := P.coordinates.comp e
  obtain ⟨L, hL⟩ := exists_linear_elementaryVelocity q
  refine ⟨L, ?_, hL⟩
  intro v
  letI : T2Space P.val.2.finiteFactor := DiscreteTopology.toT2Space
  letI : T2Space P.ElementaryCoordinates := Prod.t2Space
  letI : T2Space (Multiplicative P.ElementaryCoordinates) :=
    inferInstanceAs (T2Space P.ElementaryCoordinates)
  obtain ⟨c, hc⟩ := exists_oneParameter_lift_proper P.coordinates
    (P.coordinates_proper m hm) P.coordinates_surjective (elementaryOneParameter v)
  obtain ⟨x, hx⟩ := he c
  refine ⟨x, elementaryOneParameter_injective (r := P.val.2.latticeRank)
    (F := P.val.2.finiteFactor) ?_⟩
  apply ContinuousMonoidHom.ext
  intro t
  have hc' : P.coordinates (c t) = elementaryOneParameter v t := DFunLike.congr_fun hc t
  rw [show c t = e (Multiplicative.ofAdd (t.toAdd • x)) from hx t.toAdd] at hc'
  exact (hL x t.toAdd).symm.trans hc'

set_option maxHeartbeats 4000000 in
/-- A faithful finite-dimensional parametrization of all real one-parameter
subgroups is preserved by the elementary projections on all sufficiently fine stages. -/
theorem exists_cofinal_bijective_velocity
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hs : Surjective m)
    (e : Multiplicative V →ₜ* G)
    (he : ∀ c : Multiplicative ℝ →ₜ* G, ∃ x : V, ∀ t : ℝ,
      c (Multiplicative.ofAdd t) = e (Multiplicative.ofAdd (t • x)))
    (hf : ∀ x : V, (∀ t : ℝ, e (Multiplicative.ofAdd (t • x)) = 1) → x = 0) :
    ∃ P : WholeBruhatStage G, ∀ Q : WholeBruhatStage G, Q.val.1.kernel ≤ P.val.1.kernel →
      ∃ L : V →ₗ[ℝ]
          (EuclideanSpace ℝ (Fin Q.val.2.realDim) × EuclideanSpace ℝ (Fin Q.val.2.torusDim)),
        Bijective L ∧ ∀ x t, Q.coordinates (e (Multiplicative.ofAdd (t • x))) =
          elementaryOneParameter (L x) (Multiplicative.ofAdd t) := by
  classical
  choose L hL hline using fun P : WholeBruhatStage G => exists_stage_linear_velocity P m hm e he
  let K (Q : WholeBruhatStage G) : Submodule ℝ V := (L Q).ker
  have hK (Q : WholeBruhatStage G) (x : V) :
      x ∈ K Q ↔ ∀ t : ℝ, Q.coordinates (e (Multiplicative.ofAdd (t • x))) = 1 := by
    change L Q x = 0 ↔ _
    rw [← elementaryOneParameter_eq_one_iff (r := Q.val.2.latticeRank)
      (F := Q.val.2.finiteFactor) (L Q x)]
    simp only [hline]
  have hmono (P Q : WholeBruhatStage G)
      (hpq : P.val.1.kernel ≤ Q.val.1.kernel) : K P ≤ K Q := by
    intro x hx
    apply (hK Q x).mpr
    intro t
    let y := e (Multiplicative.ofAdd (t • x))
    have hy : y ∈ P.coordinates.toMonoidHom.ker := (hK P x).mp hx t
    rw [P.coordinates_ker] at hy
    have hy' : y ∈ Q.coordinates.toMonoidHom.ker := Q.coordinates_ker.symm ▸ hpq hy
    exact hy'
  obtain ⟨S, hS, _⟩ := exists_modulatedBruhat_character_stage m hm hs 1
  obtain ⟨A⟩ := S.quotient_elementary
  letI : Nonempty (WholeBruhatStage G) := ⟨⟨⟨S, A⟩, hS⟩⟩
  have hdir : Directed (· ≥ ·) K := by
    intro P Q
    obtain ⟨R, hRP, hRQ⟩ := P.exists_common_kernel_refinement Q
    exact ⟨R, hmono R P hRP, hmono R Q hRQ⟩
  have hsep (x : V) (hx : ∀ Q, x ∈ K Q) : x = 0 := by
    apply hf x
    intro t
    exact eq_one_of_coordinates_eq_one m hm hs _ fun Q => (hK Q x).mp (hx Q) t
  obtain ⟨P, hP⟩ := exists_trivial_velocity_kernel K hdir hsep
  refine ⟨P, fun Q hQP => ?_⟩
  have hker : (L Q).ker = ⊥ := le_antisymm ((hmono Q P hQP).trans hP.le) bot_le
  exact ⟨L Q, ⟨LinearMap.ker_eq_bot.mp hker, hL Q⟩, hline Q⟩

set_option maxHeartbeats 2500000 in
/-- With the radial direction prescribed, a common angular family projects
to a basis on every refinement of a single whole-group stage. -/
theorem exists_cofinal_radial_basis_directions
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (e : Multiplicative V →ₜ* G)
    (he : ∀ c : Multiplicative ℝ →ₜ* G, ∃ x : V, ∀ t : ℝ,
      c (Multiplicative.ofAdd t) = e (Multiplicative.ofAdd (t • x)))
    (hf : ∀ x : V, (∀ t : ℝ, e (Multiplicative.ofAdd (t • x)) = 1) → x = 0)
    {d : ℕ} (hd : Module.finrank ℝ V = d + 1) :
    ∃ P₀ : WholeBruhatStage G, ∃ γ : Fin (d + 1) → Multiplicative ℝ →ₜ* G,
      γ 0 = τ ∧ (∀ (i : Fin d) t, m (γ i.succ t) = 1) ∧
      ∀ P : WholeBruhatStage G, P.val.1.kernel ≤ P₀.val.1.kernel →
        ∃ B : Basis (Fin (d + 1)) ℝ
          (EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)),
          ∀ i, P.coordinates.comp (γ i) = elementaryOneParameter (B i) := by
  let N₀ : V →+ ℝ := (m.comp e).toMonoidHom.toAdditive
  let N := (N₀.toRealLinearMap (continuous_toAdd.comp
    (m.continuous.comp (e.continuous.comp continuous_ofAdd)))).toLinearMap
  obtain ⟨x, hx⟩ := he τ
  have hxN : N x = 1 := by
    have h := congrArg (fun g : G => (m g).toAdd) (hx 1)
    rw [one_smul] at h
    exact h.symm.trans (congrArg Multiplicative.toAdd (hτ (Multiplicative.ofAdd 1)))
  obtain ⟨C, hC, hCker⟩ := exists_radial_basis N x hxN hd
  let line (v : V) : Multiplicative ℝ →ₜ* Multiplicative V :=
    ⟨((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight v).toAddMonoidHom.toMultiplicative,
      (show Continuous (fun t : Multiplicative ℝ => Multiplicative.ofAdd (t.toAdd • v)) from
        continuous_ofAdd.comp (continuous_toAdd.smul continuous_const))⟩
  let γ (i : Fin (d + 1)) := e.comp (line (C i))
  obtain ⟨P₀, hstage⟩ := exists_cofinal_bijective_velocity m hm hτ.surjective e he hf
  refine ⟨P₀, γ, ?_, ?_, fun P hP => ?_⟩
  · apply ContinuousMonoidHom.ext
    intro t
    change e (Multiplicative.ofAdd (t.toAdd • C 0)) = τ t
    rw [hC]
    exact (hx t.toAdd).symm
  · intro i t
    apply Multiplicative.toAdd.injective
    change N (t.toAdd • C i.succ) = 0
    rw [map_smul, hCker i, smul_zero]
  · obtain ⟨L, hL, h⟩ := hstage P hP
    let B := C.map (LinearEquiv.ofBijective L hL)
    refine ⟨B, fun i => ?_⟩
    apply ContinuousMonoidHom.ext
    intro t
    exact h (C i) t.toAdd

end
end Masullo.WholeBruhatStage
