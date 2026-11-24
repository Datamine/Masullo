import PuncturedTestMultipliers
import CoordinatePlaneExpansion

open Filter Function Set TopologicalSpace Topology
open scoped ContDiff Distributions SchwartzMap

namespace Masullo

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A compact test supported off the distributional support has zero
pairing. A finite cover by open zero sets localizes the test. -/
theorem compactTestDistribution_isVanishingOn_compl_dsupport (Ω : Opens E)
    (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ) :
    Distribution.IsVanishingOn (⇑T) (Distribution.dsupport (⇑T))ᶜ := by
  classical
  intro f hf
  let I := tsupport f
  have hl (x : I) := (Distribution.notMem_dsupport_iff x.val).mp (hf x.property)
  choose U hUvan hUopen hxU using hl
  choose r hr hball using fun x : I ↦ Metric.isOpen_iff.mp (hUopen x) x.val (hxU x)
  let b (x : I) : ContDiffBump x.val := ⟨r x / 3, r x / 2, by linarith [hr x], by linarith [hr x]⟩
  let χ (x : I) (y : E) : ℂ := (b x y : ℂ)
  have hχ (x : I) : ContDiff ℝ ∞ (χ x) :=
    Complex.ofRealCLM.contDiff.comp (b x).contDiff
  have hχU (x : I) : tsupport (χ x) ⊆ U x := by
    apply (tsupport_comp_subset Complex.ofReal_zero (b x)).trans
    rw [(b x).tsupport_eq]
    exact (Metric.closedBall_subset_ball (by
      change r x / 2 < r x
      linarith [hr x])).trans (hball x)
  let V (x : I) := Metric.ball x.val (r x / 3)
  have hfV : tsupport f ⊆ ⋃ x : I, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (by linarith [hr ⟨x,hx⟩])⟩
  obtain ⟨J, hJ⟩ := f.hasCompactSupport.elim_finite_subcover V
    (fun _ ↦ Metric.isOpen_ball) hfV
  have hk (J : Finset I) (g : 𝓓(Ω, ℂ)) (hg : tsupport g ⊆ ⋃ x ∈ J, V x) :
      T g = 0 := by
    induction J using Finset.induction_on generalizing g with
    | empty =>
      have hz : g = 0 := by
        ext x
        exact image_eq_zero_of_notMem_tsupport (fun hx ↦ by simpa using hg hx)
      rw [hz, map_zero]
    | insert x J hx ih =>
      let m := openTestMultiplier Ω (χ x) (hχ x).contDiffOn g
      have hm : (m : E → ℂ) = fun y ↦ χ x y * g y := rfl
      have hTm : T m = 0 := by
        apply hUvan x
        rw [hm]
        exact tsupport_mul_subset_left.trans (hχU x)
      let d := g - m
      have hds : tsupport d ⊆ tsupport g :=
        (tsupport_sub _ _).trans (union_subset Subset.rfl
          (show tsupport m ⊆ tsupport g by rw [hm]; exact tsupport_mul_subset_right))
      have hdV : tsupport d ⊆ ⋃ y ∈ J, V y := by
        intro y hy
        have hu : y ∈ V x ∪ ⋃ z ∈ J, V z := by
          simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left] using hg (hds hy)
        refine hu.resolve_left (fun hxy ↦ ?_)
        have hloc : (d : E → ℂ) =ᶠ[𝓝 y] 0 := by
          filter_upwards [Metric.isOpen_ball.mem_nhds hxy] with z hz
          change g z - m z = 0
          rw [congrFun hm z]
          have hχ1 : χ x z = 1 := by
            change ((b x z : ℝ) : ℂ) = 1
            rw [(b x).one_of_mem_closedBall (Metric.ball_subset_closedBall hz), Complex.ofReal_one]
          rw [hχ1, one_mul, sub_self]
        exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hy
      have hz := ih d hdV
      change T (g - m) = 0 at hz
      rw [map_sub, hTm, sub_zero] at hz
      exact hz
  exact hk J f hJ

theorem compactTestDistribution_isVanishingOn_compl_of_dsupport_subset (Ω : Opens E)
    (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ) {K : Set E}
    (hK : Distribution.dsupport (⇑T) ⊆ K) :
    Distribution.IsVanishingOn (⇑T) Kᶜ :=
  fun f hf ↦ compactTestDistribution_isVanishingOn_compl_dsupport Ω T f
    (hf.trans (compl_subset_compl.mpr hK))

/-- Compactness of the actual distributional support suffices for an
extension from all smooth compact tests to the Schwartz space. -/
theorem exists_temperedExtension_of_isCompact_dsupport
    (T : 𝓓((⊤ : Opens E), ℂ) →L[ℂ] ℂ) (hT : IsCompact (Distribution.dsupport (⇑T))) :
    ∃ U : 𝓢(E, ℂ) →L[ℂ] ℂ, ∀ f : 𝓓((⊤ : Opens E), ℂ), U (smoothTestToSchwartz f) = T f :=
  exists_temperedExtension_of_compactSupport T ⟨_, hT⟩
    (compactTestDistribution_isVanishingOn_compl_dsupport ⊤ T)

/-- The one-normal-coordinate decomposition with the manuscript's actual
compact distributional support hypothesis. -/
theorem realNormal_plane_expansion_of_dsupport
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : 𝓓((⊤ : Opens (ℝ × V)), ℂ) →L[ℂ] ℂ)
    (N : ℕ) (hN : testDistributionOrderLE T N)
    (hK : IsCompact (Distribution.dsupport (⇑T)))
    (hplane : Distribution.dsupport (⇑T) ⊆ {x : ℝ × V | x.1 = 0}) :
    ∃ A : Fin (N+1) → (𝓓((⊤ : Opens V), ℂ) →L[ℂ] ℂ),
      (∀ k, testDistributionOrderLE (A k) N ∧
        Distribution.IsVanishingOn (⇑(A k)) (Prod.snd '' Distribution.dsupport (⇑T))ᶜ) ∧
      (∀ f : 𝓓((⊤ : Opens (ℝ × V)), ℂ),
        T f = ∑ k, A k (testPlaneNormalJet k.val (fun _ ↦ (1 : ℝ)) f)) :=
  realNormal_plane_expansion T N hN
    (compactTestDistribution_isVanishingOn_compl_of_dsupport_subset ⊤ T hplane)
    ⟨_, hK⟩ (compactTestDistribution_isVanishingOn_compl_dsupport ⊤ T)

/-- The arbitrary-codimension expansion for compact distributional support,
including the signed tensor identity and the extension to Schwartz tests. -/
theorem finiteNormal_plane_expansion_of_dsupport
    {D V ι : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι] (b : Module.Basis ι ℝ D)
    (T : 𝓓((⊤ : Opens (D × V)), ℂ) →L[ℂ] ℂ)
    (N : ℕ) (hN : testDistributionOrderLE T N)
    (hK : IsCompact (Distribution.dsupport (⇑T)))
    (hplane : Distribution.dsupport (⇑T) ⊆ {x : D × V | x.1 = 0}) :
    ∃ (A : PlaneJetIndex ι N → (𝓓((⊤ : Opens V), ℂ) →L[ℂ] ℂ))
      (U : 𝓢(D × V, ℂ) →L[ℂ] ℂ) (B : PlaneJetIndex ι N → (𝓢(V, ℂ) →L[ℂ] ℂ)),
      (∀ k, testDistributionOrderLE (A k) N ∧ IsCompact (Distribution.dsupport (⇑(A k)))) ∧
      (∀ f : 𝓓((⊤ : Opens (D × V)), ℂ), T f = ∑ k, A k (testPlaneNormalJet k.1.val (b ∘ k.2) f)) ∧
      T = (∑ k, (-1 : ℂ) ^ k.1.val • testPlaneDiracTensor k.1.val (b ∘ k.2) (A k)) ∧
      (∀ f : 𝓓((⊤ : Opens (D × V)), ℂ), U (smoothTestToSchwartz f) = T f) ∧
      (∀ k (g : 𝓓((⊤ : Opens V), ℂ)), B k (smoothTestToSchwartz g) = A k g) ∧
      U = ∑ k, (B k).comp (schwartzPlaneNormalJet k.1.val (b ∘ k.2)) := by
  let K : Compacts (D × V) := ⟨_, hK⟩
  have hvan := compactTestDistribution_isVanishingOn_compl_dsupport ⊤ T
  obtain ⟨A, hA, he⟩ := finiteNormal_plane_expansion b T N hN
    (compactTestDistribution_isVanishingOn_compl_of_dsupport_subset ⊤ T hplane) K hvan
  let P := Prod.snd '' (K : Set (D × V))
  have hP : IsCompact P := K.isCompact.image continuous_snd
  have hAc (k : PlaneJetIndex ι N) : IsCompact (Distribution.dsupport (⇑(A k))) := by
    apply hP.of_isClosed_subset Distribution.isClosed_dsupport
    intro x hx
    exact (Distribution.mem_dsupport_iff x).mp hx P (hA k).2 hP.isClosed
  obtain ⟨U, B, hU, hB, hUeq⟩ := plane_expansion_tempered (fun k : PlaneJetIndex ι N ↦ k.1.val)
    (fun k ↦ b ∘ k.2) T K hvan A (fun k ↦ (hA k).2) he
  exact ⟨A, U, B, fun k ↦ ⟨(hA k).1, hAc k⟩, he,
    plane_expansion_eq_sum _ _ T A he, hU, hB, hUeq⟩

end
end Masullo
