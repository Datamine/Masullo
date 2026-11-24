import SLocalPaleyWiener
import FiniteRadialTests

open Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev P := HeightOneSpectrum (𝓞 F)
variable (S : Finset (P F))

theorem isCompact_sLocalPaleyWienerBox (X : ℝ) : IsCompact (sLocalPaleyWienerBox F S X) := by
  let A (v : InfinitePlace F) := {x : v.Completion | ‖x‖ ^ v.mult ≤ X}
  let B (v : S) := Metric.closedBall (0 : v.val.adicCompletion F) X
  have hA (v : InfinitePlace F) : IsCompact (A v) := by
    let e := InfinitePlace.Completion.extensionEmbedding v
    have he := InfinitePlace.Completion.isometry_extensionEmbedding v
    have hK := he.isClosedEmbedding.isCompact_preimage
      (isCompact_closedBall (0 : ℂ) (max 1 X))
    apply hK.of_isClosed_subset (isClosed_le (continuous_norm.pow v.mult) continuous_const)
    intro x hx
    change dist (e x) 0 ≤ max 1 X
    rw [← map_zero e, he.dist_eq, dist_zero_right]
    by_cases h : ‖x‖ ≤ 1
    · exact h.trans (le_max_left _ _)
    · exact ((le_self_pow₀ (le_of_not_ge h) v.mult_ne_zero).trans hx).trans (le_max_right _ _)
  have hB (v : S) : IsCompact (B v) := by
    letI := finitePlace_properSpace F v.val
    exact isCompact_closedBall _ _
  have he : sLocalPaleyWienerBox F S X = (univ.pi A) ×ˢ (univ.pi B) := by
    ext x
    change ((∀ v : InfinitePlace F, ‖x.1 v‖ ^ v.mult ≤ X) ∧ ∀ v : S, ‖x.2 v‖ ≤ X) ↔
      ((∀ v : InfinitePlace F, v ∈ univ → ‖x.1 v‖ ^ v.mult ≤ X) ∧
       (∀ v : S, v ∈ univ → x.2 v ∈ Metric.closedBall 0 X))
    simp only [mem_univ, forall_const, Metric.mem_closedBall, dist_zero_right]
  rw [he]
  exact (isCompact_univ_pi hA).prod (isCompact_univ_pi hB)

/-- At an added place the enlarged Fourier support is bounded by the
radius of the local codifferent. -/
def sLocalFourierTailRadius (S T : Finset (P F)) : ℝ :=
  ∑ v ∈ T \ S, (v.asIdeal.absNorm : ℝ) ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))

private theorem le_sLocalFourierTailRadius {T : Finset (P F)} (v : T) (hv : v.val ∉ S) :
    (v.val.asIdeal.absNorm : ℝ) ^ multiplicity v.val.asIdeal (differentIdeal ℤ (𝓞 F)) ≤
      sLocalFourierTailRadius F S T := by
  unfold sLocalFourierTailRadius
  exact Finset.single_le_sum
    (f := fun w : P F ↦ (w.asIdeal.absNorm : ℝ) ^ multiplicity w.asIdeal (differentIdeal ℤ (𝓞 F)))
    (fun w _ ↦ pow_nonneg (Nat.cast_nonneg _) _)
    (Finset.mem_sdiff.mpr ⟨v.property,hv⟩)

/-- An inserted base-stage test in the absolute box of radius X is in
the full enlarged-stage absolute box, with the added radii accounted for. -/
theorem sLocalAbsolutePaleyWienerStageTests_le_enlargedBox
    {T : Finset (P F)} (hST : S ⊆ T) {X Y : ℝ} (hXY : X ≤ Y) :
    sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerBox F S X) ≤
      sLocalPaleyWienerTests F T (sLocalPaleyWienerBox F T (max Y (sLocalFourierTailRadius F S T))) := by
  intro f hf
  obtain ⟨g,hg,rfl⟩ := Submodule.mem_map.mp hf
  have hbox := ((mem_sLocalPaleyWienerTests_iff F S _ g).mp hg).2
  let R := max Y (sLocalFourierTailRadius F S T)
  let B := sLocalPaleyWienerBox F T R
  let φ := sLocalBruhatRestriction F T
    (sLocalFourierCompression F T (sLocalBruhatTransition F hST g)).val
  letI : T2Space (InfiniteAdeleRing F) := (infiniteAdeleMixedHomeomorph F).isEmbedding.t2Space
  letI : T2Space (SAdeles F T) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing F × ((v : T) → v.val.adicCompletion F)))
  have hc : IsCompact B := isCompact_sLocalPaleyWienerBox F T R
  have hs : tsupport φ ⊆ B := by
    apply closure_minimal _ hc.isClosed
    intro x hx
    change GlobalBruhat.evaluation F (sLocalBruhatPad F T x)
      (sLocalBruhatCorestrict F T (GlobalBruhat.fourier F g.val)).val ≠ 0 at hx
    change sLocalBruhatRestriction F T
      (sLocalBruhatCorestrict F T (GlobalBruhat.fourier F g.val)).val x ≠ 0 at hx
    rw [sLocalBruhatCorestrict_restrict] at hx
    change GlobalBruhat.evaluation F (sLocalBruhatPad F T x) (GlobalBruhat.fourier F g.val) ≠ 0 at hx
    rw [sLocalFourier_codifferent_reconstruct F S g] at hx
    have he (v : T) :
        (sLocalBruhatPad F T x).2 v.val = x.2 v := sLocalBruhatPad_finite F T x v
    have hbase : sAdelesProjection F S (sLocalBruhatPad F T x) =
        (x.1, fun v : S ↦ x.2 ⟨v.val,hST v.property⟩) := by
      refine Prod.ext rfl (funext fun v ↦ ?_)
      exact he ⟨v.val,hST v.property⟩
    have hd (v : T) (hv : v.val ∉ S) : x.2 v ∈ finitePlaceIntegerAnnihilator F v.val := by
      by_contra hn
      have hn' : ¬ ∀ w ∉ S, (sLocalBruhatPad F T x).2 w ∈ finitePlaceIntegerAnnihilator F w :=
        fun h ↦ hn (he v ▸ h v.val hv)
      rw [ite_eq_right hn', mul_zero] at hx
      exact hx rfl
    have hn := left_ne_zero_of_mul hx
    rw [hbase, ← sLocalBruhatCorestrict_restrict F S] at hn
    have hx' := hbox (subset_tsupport _ hn)
    refine ⟨fun v ↦ (hx'.1 v).trans (hXY.trans (le_max_left _ _)), fun v ↦ ?_⟩
    by_cases hv : v.val ∈ S
    · have h := hx'.2 ⟨v.val,hv⟩
      exact h.trans (hXY.trans (le_max_left _ _))
    · have h := hd v hv
      rw [finitePlaceIntegerAnnihilator_eq_differentBall] at h
      exact h.trans ((le_sLocalFourierTailRadius F S v hv).trans (le_max_right _ _))
  exact (mem_sLocalPaleyWienerTests_iff F T B _).mpr
    ⟨hc.of_isClosed_subset isClosed_closure hs,hs⟩

end

end Masullo
