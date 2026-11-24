import CompactPeriodizationSection
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

open Filter Function Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

/-- Smooth periodic functions represented on the covering line. -/
def smoothPeriodic (d : ℝ) : Submodule ℂ (ℝ → ℂ) where
  carrier := { f | ContDiff ℝ ∞ f ∧ Periodic f d }
  zero_mem' := ⟨contDiff_const, fun _ => rfl⟩
  add_mem' := fun ⟨hf, hp⟩ ⟨hg, hq⟩ => ⟨hf.add hg, fun x => by simp [hp x, hq x]⟩
  smul_mem' := fun c f ⟨hf, hp⟩ => ⟨hf.const_smul c, fun x => by simp [hp x]⟩

/-- Schwartz representatives supported in a fixed compact set. -/
def fixedSupportSchwartz (K : Set ℝ) : Submodule ℂ 𝓢(ℝ, ℂ) where
  carrier := { f | support f ⊆ K }
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x hx
    by_contra h
    have h₁ : f x = 0 := by by_contra e; exact h (hf e)
    have h₂ : g x = 0 := by by_contra e; exact h (hg e)
    exact hx (by simp [h₁, h₂])
  smul_mem' := by
    intro c f hf x hx
    apply hf
    exact fun h => hx (by simp [h])

abbrev LogFixedTest (K : Set ℝ) := ↥(fixedSupportSchwartz K)
abbrev SmoothPeriodic (d : ℝ) := ↥(smoothPeriodic d)

private theorem smoothCompact_hasTemperateGrowth {f : ℝ → ℂ} {K : Set ℝ}
    (hC : ContDiff ℝ ∞ f) (hK : IsCompact K) (hf : support f ⊆ K) :
    f.HasTemperateGrowth :=
  (HasCompactSupport.intro hK (fun _ hx => notMem_support.mp (fun h => hx (hf h)))
    |>.toSchwartzMap hC).hasTemperateGrowth

def localizePeriodic (d : ℝ) {b : ℝ → ℂ} {K : Set ℝ} (hK : IsCompact K)
    (hbC : ContDiff ℝ ∞ b) (hb : support b ⊆ K) :
    SmoothPeriodic d →ₗ[ℂ] 𝓢(ℝ, ℂ) where
  toFun f :=
    (HasCompactSupport.intro hK fun x hx => by
      change b x * (f : ℝ → ℂ) x = 0
      have hz : b x = 0 := notMem_support.mp (fun h => hx (hb h))
      rw [hz, zero_mul]).toSchwartzMap (hbC.mul f.property.1)
  map_add' f g := by ext x; exact mul_add _ _ _
  map_smul' c f := by ext x; change _ * (c * _) = c * (_ * _); ring

@[simp] theorem localizePeriodic_apply (d : ℝ) {b : ℝ → ℂ} {K : Set ℝ}
    (hK : IsCompact K) (hbC : ContDiff ℝ ∞ b) (hb : support b ⊆ K)
    (f : SmoothPeriodic d) (x : ℝ) :
    localizePeriodic d hK hbC hb f x = b x * (f : ℝ → ℂ) x := rfl

/-- Multiplying a periodization by a smooth compactly supported function is
a finite sum of continuous translations and multiplications in Schwartz space. -/
def localizedPeriodization (d : ℝ) {b : ℝ → ℂ} {K I : Set ℝ}
    (hK : IsCompact K) (hI : IsCompact I) (hd : d ≠ 0)
    (hbC : ContDiff ℝ ∞ b) (hb : support b ⊆ I) :
    LogFixedTest K →L[ℂ] 𝓢(ℝ, ℂ) :=
  ∑ n ∈ (exists_uniform_translate_finset hK hI hd).choose,
    (SchwartzMap.smulLeftCLM ℂ b).comp
      ((SchwartzMap.compSubConstCLM ℂ (-(d * (n : ℝ)))).comp
        (fixedSupportSchwartz K).subtypeL)

theorem localizedPeriodization_apply (d : ℝ) {b : ℝ → ℂ} {K I : Set ℝ}
    (hK : IsCompact K) (hI : IsCompact I) (hd : d ≠ 0)
    (hbC : ContDiff ℝ ∞ b) (hb : support b ⊆ I) (f : LogFixedTest K) (x : ℝ) :
    localizedPeriodization d hK hI hd hbC hb f x =
      b x * integerPeriodization d (f : 𝓢(ℝ, ℂ)) x := by
  have htemp := smoothCompact_hasTemperateGrowth hbC hI hb
  have heq :
      localizedPeriodization d hK hI hd hbC hb f x =
        ∑ n ∈ (exists_uniform_translate_finset hK hI hd).choose,
          b x * (f : 𝓢(ℝ, ℂ)) (x + d * (n : ℝ)) := by
    simp [localizedPeriodization, SchwartzMap.smulLeftCLM_apply_apply htemp, smul_eq_mul]
  rw [heq, ← Finset.mul_sum]
  by_cases hx : x ∈ I
  · congr 1
    exact (integerPeriodization_finset_eq f.property
      ((exists_uniform_translate_finset hK hI hd).choose_spec x hx)).symm
  · have hz : b x = 0 := notMem_support.mp (fun h => hx (hb h))
    simp [hz]

def periodizationLM (d : ℝ) {K : Set ℝ} (hK : IsCompact K) (hd : d ≠ 0) :
    LogFixedTest K →ₗ[ℂ] SmoothPeriodic d where
  toFun f := ⟨integerPeriodization d (f : 𝓢(ℝ, ℂ)),
    integerPeriodization_contDiff hK f.property ((f : 𝓢(ℝ, ℂ)).smooth ⊤) hd,
    integerPeriodization_periodic d _⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact (compact_integerTranslate_summable hK f.property hd x).tsum_add
      (compact_integerTranslate_summable hK g.property hd x)
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact tsum_mul_left

theorem b_periodic_one {d : ℝ} {b : ℝ → ℂ}
    (h : ∀ f : ℝ → ℂ, Periodic f d → integerPeriodization d (fun x => b x * f x) = f) :
    integerPeriodization d b = (fun _ => 1) := by
  simpa only [mul_one] using h (fun _ => 1) (fun _ => rfl)

theorem exists_canonical_periodic_cutoff (d : ℝ) (hd : 0 < d) :
    ∃ b : ℝ → ℂ, ContDiff ℝ ∞ b ∧ support b ⊆ Icc (-d) d ∧
      ∀ f : ℝ → ℂ, Periodic f d → integerPeriodization d (fun x => b x * f x) = f := by
  apply integerPeriodization_extends_periodic isCompact_Icc hd
  rw [interior_Icc]
  exact openInterval_covers_integerTranslations hd (by linarith)

def periodicCutoff (d : ℝ) (hd : 0 < d) : ℝ → ℂ :=
  (exists_canonical_periodic_cutoff d hd).choose

theorem periodicCutoff_spec (d : ℝ) (hd : 0 < d) :
    ContDiff ℝ ∞ (periodicCutoff d hd) ∧ support (periodicCutoff d hd) ⊆ Icc (-d) d ∧
      ∀ f : ℝ → ℂ, Periodic f d →
        integerPeriodization d (fun x => periodicCutoff d hd x * f x) = f :=
  (exists_canonical_periodic_cutoff d hd).choose_spec

def periodicChart (d : ℝ) (hd : 0 < d) : SmoothPeriodic d →ₗ[ℂ] 𝓢(ℝ, ℂ) :=
  localizePeriodic d isCompact_Icc (periodicCutoff_spec d hd).1 (periodicCutoff_spec d hd).2.1

/-- Smooth periodic topology via smooth compact localization. -/
instance smoothPeriodic_topology (d : ℝ) [Fact (0 < d)] :
    TopologicalSpace (SmoothPeriodic d) :=
  TopologicalSpace.induced (periodicChart d Fact.out) inferInstance

theorem continuous_periodicChart (d : ℝ) [Fact (0 < d)] :
    Continuous (periodicChart d Fact.out) := continuous_induced_dom

theorem periodicChart_injective (d : ℝ) (hd : 0 < d) :
    Injective (periodicChart d hd) := by
  intro f g h
  apply Subtype.ext
  have hh := congrArg (fun F : 𝓢(ℝ, ℂ) => integerPeriodization d F) h
  change integerPeriodization d (fun x => periodicCutoff d hd x * (f : ℝ → ℂ) x) =
    integerPeriodization d (fun x => periodicCutoff d hd x * (g : ℝ → ℂ) x) at hh
  simpa only [(periodicCutoff_spec d hd).2.2 _ f.property.2,
    (periodicCutoff_spec d hd).2.2 _ g.property.2] using hh

def periodizationCLM (d : ℝ) [Fact (0 < d)] {K : Set ℝ} (hK : IsCompact K) :
    LogFixedTest K →L[ℂ] SmoothPeriodic d where
  toLinearMap := periodizationLM d hK (Fact.out : 0 < d).ne'
  cont := by
    apply continuous_induced_rng.mpr
    have hspec := periodicCutoff_spec d Fact.out
    let h := localizedPeriodization d hK isCompact_Icc (Fact.out : 0 < d).ne'
      hspec.1 hspec.2.1
    convert h.continuous using 1
    funext f
    ext x
    change periodicCutoff d Fact.out x * integerPeriodization d (f : 𝓢(ℝ, ℂ)) x = h f x
    exact (localizedPeriodization_apply d hK isCompact_Icc (Fact.out : 0 < d).ne'
      hspec.1 hspec.2.1 f x).symm

def compactPeriodicSection (d : ℝ) [Fact (0 < d)] {K : Set ℝ}
    (hK : IsCompact K) {b : ℝ → ℂ} (hbC : ContDiff ℝ ∞ b) (hb : support b ⊆ K) :
    SmoothPeriodic d →L[ℂ] LogFixedTest K where
  toLinearMap := (localizePeriodic d hK hbC hb).codRestrict _ fun f x hx =>
    hb fun h => hx (by simp [h])
  cont := by
    apply Continuous.subtype_mk
    let spec := periodicCutoff_spec d Fact.out
    let u : SmoothPeriodic d → LogFixedTest (Icc (-d) d) := fun f =>
      ⟨periodicChart d Fact.out f, fun x hx => spec.2.1 fun hz => hx (by
        change periodicCutoff d Fact.out x * (f : ℝ → ℂ) x = 0
        simp [hz])⟩
    have hu : Continuous u := (continuous_periodicChart d).subtype_mk _
    let h := localizedPeriodization d (isCompact_Icc (a := -d) (b := d)) hK (Fact.out : 0 < d).ne' hbC hb
    convert h.continuous.comp hu using 1
    funext f
    ext x
    dsimp only [Function.comp_apply, h]
    rw [localizedPeriodization_apply]
    change b x * (f : ℝ → ℂ) x =
      b x * integerPeriodization d (fun y => periodicCutoff d Fact.out y * (f : ℝ → ℂ) y) x
    rw [spec.2.2 _ f.property.2]

theorem exists_compactPeriodicSection (d : ℝ) [Fact (0 < d)] {K : Set ℝ}
    (hK : IsCompact K) (hcov : ∀ x : ℝ, ∃ n : ℤ, x + d * (n : ℝ) ∈ interior K) :
    ∃ S : SmoothPeriodic d →L[ℂ] LogFixedTest K,
      RightInverse S (periodizationCLM d hK) := by
  obtain ⟨b, hbC, hb, hbP⟩ := integerPeriodization_extends_periodic hK Fact.out hcov
  refine ⟨compactPeriodicSection d hK hbC hb, fun f => Subtype.ext ?_⟩
  exact hbP _ f.property.2

theorem periodization_surjective_iff_interior_coverage (d : ℝ) [Fact (0 < d)] {K : Set ℝ}
    (hK : IsCompact K) :
    Surjective (periodizationCLM d hK) ↔
      ∀ x : ℝ, ∃ n : ℤ, x + d * (n : ℝ) ∈ interior K := by
  constructor
  · intro h x
    let one : SmoothPeriodic d := ⟨fun _ => 1, contDiff_const, fun _ => rfl⟩
    obtain ⟨f, hf⟩ := h one
    have hval : integerPeriodization d (f : 𝓢(ℝ, ℂ)) x = 1 :=
      congrArg (fun p : SmoothPeriodic d => (p : ℝ → ℂ) x) hf
    by_contra! hn
    have hopen : IsOpen (support (f : 𝓢(ℝ, ℂ))) :=
      (isClosed_eq (f : 𝓢(ℝ, ℂ)).continuous continuous_const).isOpen_compl
    have hp : support (f : 𝓢(ℝ, ℂ)) ⊆ interior K :=
      hopen.subset_interior_iff.mpr f.property
    have hz (n : ℤ) : (f : 𝓢(ℝ, ℂ)) (x + d * (n : ℝ)) = 0 := by
      by_contra hx
      exact hn n (hp hx)
    simp [integerPeriodization, hz] at hval
  · intro h
    obtain ⟨S, hS⟩ := exists_compactPeriodicSection d hK h
    exact hS.surjective

/-- The split periodization induces a topological linear isomorphism from
the actual quotient by its kernel. -/
def compactPeriodizationQuotient (d : ℝ) [Fact (0 < d)] {K : Set ℝ}
    (hK : IsCompact K) (hcov : ∀ x : ℝ, ∃ n : ℤ, x + d * (n : ℝ) ∈ interior K) :
    (LogFixedTest K ⧸ (periodizationCLM d hK).ker) ≃L[ℂ] SmoothPeriodic d := by
  let S := (exists_compactPeriodicSection d hK hcov).choose
  have hS := (exists_compactPeriodicSection d hK hcov).choose_spec
  let P := periodizationCLM d hK
  let F := P.ker.liftQL P le_rfl
  let R := P.ker.mkQL.comp S
  have hright (f : SmoothPeriodic d) : F (R f) = f := by
    change P (S f) = f
    exact hS f
  have hleft (q : LogFixedTest K ⧸ P.ker) : R (F q) = q := by
    obtain ⟨f, rfl⟩ := P.ker.mkQ_surjective q
    change Submodule.Quotient.mk (S (P f)) = Submodule.Quotient.mk f
    rw [Submodule.Quotient.eq]
    change P (S (P f) - f) = 0
    rw [map_sub, hS (P f), sub_self]
  exact { toLinearEquiv := LinearEquiv.ofLinear F.toLinearMap R.toLinearMap
            (LinearMap.ext hright) (LinearMap.ext hleft)
          continuous_toFun := F.continuous
          continuous_invFun := R.continuous }

@[simp] theorem compactPeriodizationQuotient_mk (d : ℝ) [Fact (0 < d)] {K : Set ℝ}
    (hK : IsCompact K) (hcov : ∀ x : ℝ, ∃ n : ℤ, x + d * (n : ℝ) ∈ interior K)
    (f : LogFixedTest K) :
    compactPeriodizationQuotient d hK hcov ((periodizationCLM d hK).ker.mkQ f) =
      periodizationCLM d hK f := rfl

end
end Masullo
