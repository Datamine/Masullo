import BruhatCyclicPeriodizationStages
import BruhatStageEvaluation
import BruhatCyclicFactorization

open Function Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 700000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
  (γ : G) (hγ : 0 < (m γ).toAdd)

local notation "Γ" => Subgroup.zpowers γ
local notation "H" => G ⧸ Γ

variable [hT : T2Space (G ⧸ Subgroup.zpowers γ)]
  [hLC : LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]

variable (hms : Surjective m)

include hm hms in
private theorem exists_bruhatCyclicPeriodization :
    ∃ P : BruhatSchwartz G →L[ℂ] BruhatSchwartz H,
      ∀ f x, (P f).val (QuotientGroup.mk x) = bruhatSchwartz_cyclicOrbitSum m γ hγ x f := by
  let r : G → H := QuotientGroup.mk
  have hr : Surjective r := QuotientGroup.mk_surjective
  let c : Set (BruhatSchwartzStage G) := {p | p.1.upper.val = ⊤}
  let A : G → BruhatSchwartz G →L[ℂ] ℂ := bruhatSchwartz_cyclicOrbitSum m γ hγ
  have hv (p : c) : ∃ q : BruhatSchwartzStage H, ∀ f : p.val.Space,
      ∃ u : q.Space, ∀ x, q.realize u (r x) = A x (p.val.inclusion f) := by
    have ht : ∃ Q : WholeBruhatStage H, ∀ f : p.val.Space, ∃ u : Q.val.Space,
        ∀ x : G, Q.val.realize u (r x) = A x (p.val.inclusion f) :=
      exists_bruhatCyclicPeriodization_stage m hm γ hγ p
    exact ⟨ht.choose.val, ht.choose_spec⟩
  have hcof : ∀ p : BruhatSchwartzStage G, ∃ q : c, p.1 ≤ q.val.1 :=
    exists_wholeBruhatStage_refinement m hm hms
  have hGlue : ∃ L : BruhatSchwartz G →L[ℂ] BruhatSchwartz H,
      ∀ (f : BruhatSchwartz G) (x : G), (L f).val (r x) = A x f :=
    @bruhatSchwartz_exists_clm_of_cofinal_stage_values G H
      _ _ _ _ _ _ _ _ hT hLC G r hr A c hcof hv
  exact hGlue


/-- Ordinary Schwartz–Bruhat periodization into the compact quotient's
actual Schwartz–Bruhat topology. -/
def bruhatCyclicPeriodization : BruhatSchwartz G →L[ℂ] BruhatSchwartz H :=
  (exists_bruhatCyclicPeriodization m hm γ hγ hms).choose

/-- Evaluation at any representative is the absolutely convergent orbit sum. -/
theorem bruhatCyclicPeriodization_apply (f : BruhatSchwartz G) (x : G) :
    (bruhatCyclicPeriodization m hm γ hγ hms f).val (QuotientGroup.mk x) =
      bruhatSchwartz_cyclicOrbitSum m γ hγ x f :=
  (exists_bruhatCyclicPeriodization m hm γ hγ hms).choose_spec f x

include hm hms hT hLC in
/-- The ordinary periodization has a continuous right inverse defined by
multiplying the pullback by a fixed normalized logarithmic cutoff. -/
theorem exists_bruhatCyclicPeriodization_section :
    ∃ S : BruhatSchwartz H →L[ℂ] BruhatSchwartz G,
      RightInverse S (bruhatCyclicPeriodization m hm γ hγ hms) := by
  let P := bruhatCyclicPeriodization m hm γ hγ hms
  obtain ⟨S, hS⟩ := exists_weightedCyclicPeriodization_section m hm hms γ hγ P
    (bruhatCyclicPeriodization_apply m hm γ hγ hms) univ (mem_univ 0)
  exact ⟨(modulatedDecay_zeroInclusion m univ (mem_univ 0)).comp S, hS⟩

include hm hms hT hLC in
theorem bruhatCyclicPeriodization_isOpenMap :
    IsOpenMap (bruhatCyclicPeriodization m hm γ hγ hms) := by
  let P := bruhatCyclicPeriodization m hm γ hγ hms
  letI : IsTopologicalAddGroup (BruhatSchwartz G) :=
    (PolynormableSpace.withSeminorms ℂ (BruhatSchwartz G)).topologicalAddGroup
  letI : IsTopologicalAddGroup (BruhatSchwartz H) :=
    (PolynormableSpace.withSeminorms ℂ (BruhatSchwartz H)).topologicalAddGroup
  obtain ⟨S, hS⟩ := exists_bruhatCyclicPeriodization_section m hm γ hγ hms
  intro U hU
  apply isOpen_iff_mem_nhds.2
  rintro y ⟨x, hx, rfl⟩
  let T (z : BruhatSchwartz H) := x + S (z - P x)
  have hCont : Continuous T := continuous_const.add (S.continuous.comp (continuous_id.sub continuous_const))
  have hxT : T (P x) = x := by simp [T]
  have hPT (z : BruhatSchwartz H) : P (T z) = z := by
    change P (x + S (z - P x)) = z
    rw [map_add]
    rw [show P (S (z - P x)) = z - P x from hS (z - P x)]
    abel
  have hN : U ∈ 𝓝 (T (P x)) := by
    rw [hxT]
    exact hU.mem_nhds hx
  filter_upwards [hCont.continuousAt.preimage_mem_nhds hN] with z hz
  exact ⟨T z, hz, hPT z⟩

end

end Masullo
