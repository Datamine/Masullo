import ClassicalSchwartzNuclear
import SLocalThetaStrictFrechet

open IsDedekindDomain NumberField UniformSpace
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

universe u

variable (F : Type u) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- The mixed archimedean Schwartz space used in the adelic constructions
is nuclear. -/
theorem archimedeanSchwartz_nuclear :
    NuclearLocallyConvex.{u, u} 𝓢(mixedEmbedding.mixedSpace F, ℂ) :=
  classicalSchwartz_nuclear _

theorem archimedeanSchwartz_strongDual_nuclear :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :=
  classicalSchwartz_strongDual_nuclear _

/-- The actual S-local test space is nuclear via its finite Schwartz-product stages. -/
theorem sLocalBruhat_nuclear :
    NuclearLocallyConvex.{u, u} (sLocalBruhatImage F S) := by
  obtain ⟨I, P, D, _, _, _, hFinal⟩ := sLocalBruhat_exists_frechetPresentation F S
  refine D.nuclear_of_stages (fun n ↦ ?_) hFinal
  change NuclearLocallyConvex.{u, u} (P n → 𝓢(mixedEmbedding.mixedSpace F, ℂ))
  exact nuclearLocallyConvex_pi (fun _ ↦ archimedeanSchwartz_nuclear F)

/-- Closed bounded sets in the S-local test space are compact. -/
theorem sLocalBruhat_montel : MontelSpace ℂ (sLocalBruhatImage F S) := by
  letI : UniformSpace (sLocalBruhatImage F S) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (sLocalBruhatImage F S) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (sLocalBruhatImage F S) := sLocalBruhat_complete F S
  exact ⟨fun _ hs hb ↦
    (nuclearLocallyConvex_totallyBounded (sLocalBruhat_nuclear F S) hb).isCompact_of_isClosed hs⟩

/-- The strong dual of the actual S-local test space is nuclear. -/
theorem sLocalBruhat_strongDual_nuclear :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ (sLocalBruhatImage F S)) := by
  obtain ⟨I, P, D, hFr, hEmb, hTrans, hFinal⟩ := sLocalBruhat_exists_frechetPresentation F S
  apply strongDual_nuclear_of_strictFrechet D hFr hEmb hTrans hFinal
  intro n
  change NuclearLocallyConvex.{u, u} (StrongDual ℂ (P n → 𝓢(mixedEmbedding.mixedSpace F, ℂ)))
  exact strongDual_nuclear_pi_finite (fun _ ↦ archimedeanSchwartz_strongDual_nuclear F)

/-- The strong S-local test dual is complete in the topology of bounded convergence. -/
theorem sLocalBruhat_strongDual_complete : CompleteSpace (StrongDual ℂ (sLocalBruhatImage F S)) := by
  obtain ⟨I, P, D, hFr, _, _, _⟩ := sLocalBruhat_exists_frechetPresentation F S
  let X (n : ℕ) := P n → 𝓢(mixedEmbedding.mixedSpace F, ℂ)
  letI : ∀ n, IsTopologicalAddGroup (X n) := fun n ↦ (hFr n).choose
  letI : ∀ n, PolynormableSpace ℂ (X n) := fun n ↦ (hFr n).choose_spec.1
  letI : ∀ n, ContinuousSMul ℂ (X n) :=
    fun n ↦ (PolynormableSpace.withSeminorms ℂ (X n)).continuousSMul
  letI : ∀ n, TopologicalSpace.MetrizableSpace (X n) := fun n ↦ (hFr n).choose_spec.2.1
  letI : ∀ n, SequentialSpace (X n) := fun n ↦ inferInstance
  exact strongDual_complete_of_sequentialSlices D.incl fun l ↦ (D.continuous_limit l).mpr

theorem sLocalBruhat_strongDual_montel :
    MontelSpace ℂ (StrongDual ℂ (sLocalBruhatImage F S)) := by
  letI := sLocalBruhat_strongDual_complete F S
  exact ⟨fun _ hs hb ↦ (nuclearLocallyConvex_totallyBounded
    (E := StrongDual ℂ (sLocalBruhatImage F S))
    (sLocalBruhat_strongDual_nuclear F S) hb).isCompact_of_isClosed hs⟩

/-- The S-local ordinary theta quotient is nuclear. -/
theorem sLocalThetaQuotient_nuclear : NuclearLocallyConvex.{u, u} (SLocalThetaQuotient F S) :=
  sLocalThetaQuotient_nuclear_of_arch F S (archimedeanSchwartz_nuclear F)

/-- The global ordinary theta quotient is nuclear. -/
theorem globalThetaQuotient_nuclear : NuclearLocallyConvex.{u, u} (GlobalThetaQuotient F) :=
  globalThetaQuotient_nuclear_of_arch F (archimedeanSchwartz_nuclear F)

theorem sLocalThetaQuotient_montel : MontelSpace ℂ (SLocalThetaQuotient F S) :=
  sLocalThetaQuotient_montel_of_arch F S (archimedeanSchwartz_nuclear F)

theorem globalThetaQuotient_montel : MontelSpace ℂ (GlobalThetaQuotient F) :=
  globalThetaQuotient_montel_of_arch F (archimedeanSchwartz_nuclear F)

theorem sLocalThetaQuotient_strongDual_nuclear :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ (SLocalThetaQuotient F S)) :=
  sLocalThetaQuotient_strongDual_nuclear_of_arch F S
    (archimedeanSchwartz_nuclear F) (archimedeanSchwartz_strongDual_nuclear F)

theorem globalThetaQuotient_strongDual_nuclear :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ (GlobalThetaQuotient F)) :=
  globalThetaQuotient_strongDual_nuclear_of_arch F
    (archimedeanSchwartz_nuclear F) (archimedeanSchwartz_strongDual_nuclear F)

theorem sLocalThetaQuotient_strongDual_montel :
    MontelSpace ℂ (StrongDual ℂ (SLocalThetaQuotient F S)) :=
  sLocalThetaQuotient_strongDual_montel_of_arch F S
    (archimedeanSchwartz_nuclear F) (archimedeanSchwartz_strongDual_nuclear F)

theorem globalThetaQuotient_strongDual_montel :
    MontelSpace ℂ (StrongDual ℂ (GlobalThetaQuotient F)) :=
  globalThetaQuotient_strongDual_montel_of_arch F
    (archimedeanSchwartz_nuclear F) (archimedeanSchwartz_strongDual_nuclear F)

end

end Masullo
