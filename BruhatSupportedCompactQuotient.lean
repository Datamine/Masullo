import BruhatCompactQuotientStages
import ModulatedCompactQuotient

open Function Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 8

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)

private theorem exists_logarithmic_cutoff (a b d : ℝ) (hd : 0 < d) (hab : a + d < b) :
    ∃ c : ℝ → ℂ, ContDiff ℝ ∞ c ∧ support c ⊆ Icc a b ∧
      ∀ f : ℝ → ℂ, Periodic f d → integerPeriodization d (fun x ↦ c x * f x) = f := by
  apply integerPeriodization_extends_periodic (K := Icc a b) isCompact_Icc hd
  intro x
  rw [interior_Icc]
  exact openInterval_covers_integerTranslations hd hab x

variable (γ : G) (hγ : 0 < (m γ).toAdd)

include hm hγ in
private theorem exists_compactStage_periodization_section
    (P : WholeBruhatStage G) (N : Subgroup G)
    [T2Space (G ⧸ N)] [LocallyCompactSpace (G ⧸ N)] (Q : WholeBruhatStage (G ⧸ N))
    (hPN : P.val.1.kernel ≤ N) (hγN : Subgroup.zpowers γ ≤ N)
    (a b : ℝ) (hab : a + (m γ).toAdd < b)
    (A : (P.val.compactTests ((fun x ↦ (m x).toAdd) ⁻¹' Icc a b)) →L[ℂ] Q.val.Space)
    (hA : ∀ f x, Q.val.realize (A f) (QuotientGroup.mk x) =
      ∑' j : ℤ, P.val.realize f.val (γ ^ j * x)) :
    let U := P.val.compactTests ((fun x ↦ (m x).toAdd) ⁻¹' Icc a b)
    ∃ R : Q.val.Space →L[ℂ] U, RightInverse R A := by
  let C := (fun x ↦ (m x).toAdd) ⁻¹' Icc a b
  let U := P.val.compactTests C
  have hcut : ∃ c : ℝ → ℂ, ContDiff ℝ ∞ c ∧ support c ⊆ Icc a b ∧
      ∀ f : ℝ → ℂ, Periodic f (m γ).toAdd →
        integerPeriodization (m γ).toAdd (fun x ↦ c x * f x) = f :=
    exists_logarithmic_cutoff a b (m γ).toAdd hγ hab
  obtain ⟨c, hc, hcs, hsum⟩ := hcut
  have hR₀ : ∃ R : Q.val.Space →L[ℂ] U, ∀ g x,
      P.val.realize (R g).val x = c (m x).toAdd * Q.val.realize g (QuotientGroup.mk x) :=
    exists_bruhatCompactTests_cutoff_pullback m hm P N Q hPN a b c hc hcs
  obtain ⟨R, hR⟩ := hR₀
  let p (f : U) : G → ℂ := P.val.realize f.val
  let q (g : Q.val.Space) : G ⧸ N → ℂ := Q.val.realize g
  let periodize : U → Q.val.Space := fun f ↦ A f
  let lift : Q.val.Space → U := fun g ↦ R g
  have hQR : Injective q := Q.val.1.realizeSchwartz_injective Q.val.2
  have hA' (f : U) (x : G) : q (periodize f) (QuotientGroup.mk x) =
      ∑' j : ℤ, p f (γ ^ j * x) := hA f x
  have hR' (g : Q.val.Space) (x : G) :
      p (lift g) x = c (m x).toAdd * q g (QuotientGroup.mk x) := hR g x
  have hr : RightInverse lift periodize :=
    cyclicCutoff_rightInverse_of_values (U := ↥U) (V := Q.val.Space)
      m γ N hγN p q hQR c hsum periodize lift hA' hR'
  exact ⟨R, hr⟩

variable (K : Subgroup G)

local notation "N" => (K ⊔ Subgroup.zpowers γ : Subgroup G)
local notation "Y" => G ⧸ N
include hm hγ in
/-- Proposition 4.5.2.1(2) on a compact subgroup with a whole-group
structural stage. Periodization onto the actual quotient by the subgroup
and the period has a continuous supported right inverse. -/
theorem exists_supportedCompactQuotient_periodization_section
    [SecondCountableTopology G]
    (hms : Surjective m) (hK : IsCompact (K : Set G)) (hKm : K ≤ m.toMonoidHom.ker)
    (P : WholeBruhatStage G) (hP : P.val.1.kernel = K) (a b : ℝ) (hab : a + (m γ).toAdd < b) :
    letI : IsClosed (N : Set G) := modulatedCompactCyclicSubgroup_isClosed m K hK hKm γ hγ
    let U := bruhatSupportedInvariant m K ((fun x ↦ (m x).toAdd) ⁻¹' Icc a b)
    ∃ (T : U →L[ℂ] BruhatSchwartz Y) (S : BruhatSchwartz Y →L[ℂ] U),
      RightInverse S T ∧ ∀ (f : U) (x : G),
        (T f).val (QuotientGroup.mk x) = ∑' j : ℤ, f.val.val (γ ^ j * x) := by
  letI : IsClosed (N : Set G) := modulatedCompactCyclicSubgroup_isClosed m K hK hKm γ hγ
  letI : CompactSpace Y := modulatedCompactCyclicQuotient_compact m K hKm hm γ hγ
  let q : G → Y := QuotientGroup.mk
  let C := (fun x ↦ (m x).toAdd) ⁻¹' Icc a b
  have hIcc : IsCompact (Icc a b) := isCompact_Icc
  have hC : IsCompact C := hm.isCompact_preimage (show IsCompact (Multiplicative.toAdd ⁻¹' Icc a b)
    from hIcc)
  obtain ⟨Q, hQ, hper⟩ := exists_bruhatCyclicPeriodization_quotient_stage m hm γ hγ P
    K (le_of_eq hP.symm) N rfl inferInstance
  have hQbot : Q.val.1.kernel = ⊥ := by
    rw [hQ, hP]
    exact le_antisymm (Subgroup.map_le_iff_le_comap.2 (fun x hx ↦
      Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff x).2
        ((show K ≤ N from le_sup_left) hx)))) bot_le
  obtain ⟨eQ, heQ⟩ := Q.exists_equiv_schwartz_of_compact_bottom hQbot
  have heP : ∃ e : P.val.compactTests C ≃L[ℂ] bruhatSupportedInvariant m K C,
      ∀ u, (e u).val.val = P.val.realize u.val := by
    have hEq := bruhatSupportedInvariant_stageEquiv m P C hm hms hC
    exact hP ▸ hEq
  obtain ⟨eP, heP⟩ := heP
  have hPN : P.val.1.kernel ≤ N := hP.symm ▸ (show K ≤ N from le_sup_left)
  obtain ⟨B, hB⟩ := exists_bruhatStage_periodization_map m γ hγ P N Q hper
  let T₀ : P.val.compactTests C →L[ℂ] Q.val.Space := B.comp (P.val.compactTests C).subtypeL
  have hT₀ (u : P.val.compactTests C) (x : G) :
      Q.val.realize (T₀ u) (QuotientGroup.mk x) = ∑' j : ℤ, P.val.realize u.val (γ ^ j * x) :=
    hB u.val x
  obtain ⟨R, hTR⟩ := exists_compactStage_periodization_section
    m hm γ hγ P N Q hPN le_sup_right a b hab T₀ hT₀
  let T := eQ.toContinuousLinearMap.comp (T₀.comp eP.symm.toContinuousLinearMap)
  let S := eP.toContinuousLinearMap.comp (R.comp eQ.symm.toContinuousLinearMap)
  refine ⟨T, S, fun g ↦ ?_, fun f x ↦ ?_⟩
  · change eQ (T₀ (eP.symm (eP (R (eQ.symm g))))) = g
    let u : Q.val.Space := eQ.symm g
    have h₁ : T₀ (eP.symm (eP (R u))) = T₀ (R u) :=
      congrArg T₀ (eP.symm_apply_apply (R u))
    have h₂ : T₀ (R u) = u := hTR u
    exact (congrArg eQ (h₁.trans h₂)).trans (eQ.apply_symm_apply g)
  · change (eQ (T₀ (eP.symm f))).val (q x) = _
    have hv : P.val.realize (eP.symm f).val = f.val.val :=
      (heP (eP.symm f)).symm.trans (congrArg (fun g ↦ g.val.val) (eP.apply_symm_apply f))
    exact (congrFun (heQ (T₀ (eP.symm f))) (q x)).trans
      ((hT₀ (eP.symm f) x).trans (tsum_congr fun j ↦ congrFun hv _))
end

end Masullo
