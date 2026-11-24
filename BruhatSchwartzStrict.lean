import BruhatSchwartz
import StructuralCofinality
import StrictStageTopology

open Bornology Function Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

set_option maxHeartbeats 1500000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

namespace BruhatSchwartzStage

/-- Each stage map into the full Schwartz–Bruhat space is continuous in the
final locally convex topology. -/
def inclusionCLM (p : BruhatSchwartzStage G) : p.Space →L[ℂ] BruhatSchwartz G :=
  ⟨p.inclusion, locallyConvexFinal_stage_continuous
    (fun p : BruhatSchwartzStage G ↦ p.inclusion) p⟩

theorem inclusion_injective (p : BruhatSchwartzStage G) : Injective p.inclusionCLM :=
  fun _ _ hab ↦ p.1.realizeSchwartz_injective p.2 (congrArg Subtype.val hab)

private theorem transition_exists (p q : BruhatSchwartzStage G) (h : p.1 ≤ q.1) :
    ∃ L : p.Space →L[ℂ] q.Space, IsClosedEmbedding L ∧ ∀ f, q.realize (L f) = p.realize f := by
  have hu : p.1.upper.val ≤ q.1.upper.val := h.1
  have hk : q.1.kernel ≤ p.1.kernel := h.2
  exact p.1.schwartz_refinement_closedEmbedding q.1 hu hk p.2 q.2

/-- The unique refinement map preserving the realized function. -/
def transition (p q : BruhatSchwartzStage G) (h : p.1 ≤ q.1) : p.Space →L[ℂ] q.Space :=
  (transition_exists p q h).choose

theorem transition_isClosedEmbedding (p q : BruhatSchwartzStage G) (h : p.1 ≤ q.1) :
    IsClosedEmbedding (transition p q h) := (transition_exists p q h).choose_spec.1

theorem inclusion_transition (p q : BruhatSchwartzStage G) (h : p.1 ≤ q.1) (f : p.Space) :
    q.inclusionCLM (transition p q h f) = p.inclusionCLM f :=
  Subtype.ext ((transition_exists p q h).choose_spec.2 f)

end BruhatSchwartzStage

variable (b : ℕ → BruhatSchwartzStage G)

/-- The final topology can be tested on any cofinal family of stages. -/
theorem bruhatSchwartz_continuous_of_cofinal
    (hCov : ∀ p : LCAStructuralPair G, ∃ n, p ≤ (b n).1)
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y]
    (L : BruhatSchwartz G →ₗ[ℂ] Y)
    (hL : ∀ n, Continuous (L.comp (b n).inclusion)) : Continuous L := by
  apply (locallyConvexFinal_continuous_iff (fun p : BruhatSchwartzStage G ↦ p.inclusion) L).mpr
  intro p
  obtain ⟨n, h⟩ := hCov p.1
  have heq : (L.comp p.inclusion : p.Space → Y) =
      (L.comp (b n).inclusion) ∘ (BruhatSchwartzStage.transition p (b n) h) := by
    funext f
    exact congrArg L (BruhatSchwartzStage.inclusion_transition p (b n) h f).symm
  rw [heq]
  exact (hL n).comp (BruhatSchwartzStage.transition p (b n) h).continuous

/-- Continuity of a seminorm on the full limit can be tested on any cofinal
family of structural stages. -/
theorem bruhatSchwartz_seminorm_continuous_of_cofinal
    (hCov : ∀ p : LCAStructuralPair G, ∃ n, p ≤ (b n).1)
    (q : Seminorm ℂ (BruhatSchwartz G)) (hq : ∀ n, Continuous (q.comp (b n).inclusion)) :
    Continuous q := by
  apply locallyConvexFinal_seminorm_continuous (fun p : BruhatSchwartzStage G ↦ p.inclusion) q
  intro p
  obtain ⟨n, h⟩ := hCov p.1
  have heq : (q.comp p.inclusion : p.Space → ℝ) =
      (q.comp (b n).inclusion) ∘ (BruhatSchwartzStage.transition p (b n) h) := by
    funext f
    exact congrArg q (BruhatSchwartzStage.inclusion_transition p (b n) h f).symm
  rw [heq]
  exact (hq n).comp (BruhatSchwartzStage.transition p (b n) h).continuous

/-- The realized cofinal stages give an actual countable inductive
presentation of the same full Schwartz–Bruhat space. -/
def bruhatSchwartz_countablePresentation
    (hb : Monotone (fun n ↦ (b n).1))
    (hCov : ∀ p : LCAStructuralPair G, ∃ n, p ≤ (b n).1) :
    LinearInductivePresentation (BruhatSchwartz G) (fun n ↦ (b n).Space) where
  incl n := (b n).inclusionCLM
  transition {m n} h := BruhatSchwartzStage.transition (b m) (b n) (hb h)
  injective_incl n := (b n).inclusion_injective
  incl_transition {m n} h f := BruhatSchwartzStage.inclusion_transition (b m) (b n) (hb h) f
  exhaust x := by
    obtain ⟨p, f, hf⟩ := x.property
    obtain ⟨n, h⟩ := hCov p.1
    refine ⟨n, BruhatSchwartzStage.transition p (b n) h f, ?_⟩
    exact (BruhatSchwartzStage.inclusion_transition p (b n) h f).trans (Subtype.ext hf)
  continuous_limit l :=
    ⟨fun h n ↦ h.comp (b n).inclusionCLM.continuous,
      bruhatSchwartz_continuous_of_cofinal b hCov l⟩

variable [SecondCountableTopology G]

/-- Lemma D.1.5.6. The full Schwartz–Bruhat limit is Hausdorff, each
structural stage has its intrinsic topology, and each bounded set comes
from one stage and is bounded there. -/
theorem bruhatSchwartz_strict :
    T2Space (BruhatSchwartz G) ∧
      (∀ p : BruhatSchwartzStage G, IsEmbedding p.inclusionCLM) ∧
      ∀ B : Set (BruhatSchwartz G), IsVonNBounded ℂ B →
        ∃ (p : BruhatSchwartzStage G) (C : Set p.Space),
          IsVonNBounded ℂ C ∧ p.inclusionCLM '' C = B := by
  obtain ⟨P, hP, hCov⟩ := lcaStructuralPairs_cofinalSequence (G := G)
  let b (n : ℕ) : BruhatSchwartzStage G := ⟨P n, Classical.choice (P n).quotient_elementary⟩
  letI (n : ℕ) : ContinuousSMul ℂ (b n).Space :=
    (PolynormableSpace.withSeminorms ℂ (b n).Space).continuousSMul
  let D := bruhatSchwartz_countablePresentation b hP hCov
  have hclosed (n : ℕ) : IsClosedEmbedding (D.transition (Nat.le_succ n)) :=
    BruhatSchwartzStage.transition_isClosedEmbedding (b n) (b (n + 1)) (hP (Nat.le_succ n))
  have hEmb (n : ℕ) : IsEmbedding (D.incl n) :=
    D.strict_incl_isEmbedding (bruhatSchwartz_seminorm_continuous_of_cofinal b hCov)
      (fun k ↦ (hclosed k).isEmbedding) n
  refine ⟨bruhatSchwartz_t2, fun p ↦ ?_, fun B hB ↦ ?_⟩
  · obtain ⟨n, h⟩ := hCov p.1
    have he : (p.inclusionCLM : p.Space → BruhatSchwartz G) =
        (D.incl n) ∘ (BruhatSchwartzStage.transition p (b n) h) :=
      funext fun f ↦ (BruhatSchwartzStage.inclusion_transition p (b n) h f).symm
    rw [he]
    exact (hEmb n).comp (BruhatSchwartzStage.transition_isClosedEmbedding p (b n) h).isEmbedding
  · have hlim (L : BruhatSchwartz G →ₗ[ℂ] lp (fun _ : ℕ ↦ ℂ) ∞) :
        (∀ n, Continuous (L.comp (D.incl n).toLinearMap)) → Continuous L :=
      bruhatSchwartz_continuous_of_cofinal b hCov L
    obtain ⟨n, C, hC, he⟩ := (D.strict_bounded_iff hclosed hEmb hlim B).mp hB
    exact ⟨b n, C, hC, he⟩

end

end Masullo
