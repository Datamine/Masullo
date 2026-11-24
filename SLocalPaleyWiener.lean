import SLocalFourierTail
import AdelicHomogeneousTheta
import SLocalZetaProduct
import AdelicPolarDistributions

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S

/-- The finite-stage Fourier box uses the normalized local absolute values. -/
def sLocalPaleyWienerBox (X : ℝ) : Set (SAdeles F S) :=
  {a | (∀ v : InfinitePlace F, ‖a.1 v‖ ^ v.mult ≤ X) ∧ ∀ v : S, ‖a.2 v‖ ≤ X}

/-- Product modulus on the full additive stage, including singular tuples. -/
def sLocalAdditiveModulus (a : SAdeles F S) : ℝ :=
  (∏ v : InfinitePlace F, ‖a.1 v‖ ^ v.mult) * ∏ v : S, ‖a.2 v‖

def sLocalPaleyWienerRegion (Y : ℝ) : Set (SAdeles F S) :=
  {a | sLocalAdditiveModulus F S a ≤ Y}

theorem sLocalAdditiveModulus_idele (g : (SAdeles F S)ˣ) :
    sLocalAdditiveModulus F S g.val = sLocalIdeleNorm F S g := by
  obtain ⟨p, rfl⟩ := (sLocalZetaIdeleCoordinates F S).symm.surjective g
  rw [sLocalZetaIdeleCoordinates_norm]
  rfl

theorem sLocalPaleyWienerBox_subset_region {X : ℝ} (hX : 0 ≤ X) :
    sLocalPaleyWienerBox F S X ⊆
      sLocalPaleyWienerRegion F S (X ^ (Fintype.card (InfinitePlace F) + S.card)) := by
  intro a ha
  have harch : (∏ v : InfinitePlace F, ‖a.1 v‖ ^ v.mult) ≤ X ^ Fintype.card (InfinitePlace F) :=
    calc
      _ ≤ ∏ _ : InfinitePlace F, X :=
        Finset.prod_le_prod (fun v _ ↦ pow_nonneg (norm_nonneg (a.1 v)) _) (fun v _ ↦ ha.1 v)
      _ = _ := by simp
  have hf : (∏ v : S, ‖a.2 v‖) ≤ X ^ S.card :=
    calc
      _ ≤ ∏ _ : S, X := Finset.prod_le_prod (fun v _ ↦ norm_nonneg (a.2 v)) (fun v _ ↦ ha.2 v)
      _ = _ := by simp
  change sLocalAdditiveModulus F S a ≤ _
  rw [sLocalAdditiveModulus, pow_add]
  exact mul_le_mul harch hf (Finset.prod_nonneg fun v _ ↦ norm_nonneg (a.2 v)) (pow_nonneg hX _)

theorem sLocalPaleyWienerBox_mono : Monotone (sLocalPaleyWienerBox F S) := by
  intro X Y h a ha
  exact ⟨fun v ↦ (ha.1 v).trans h, fun v ↦ (ha.2 v).trans h⟩

theorem sLocalPaleyWienerRegion_mono : Monotone (sLocalPaleyWienerRegion F S) :=
  fun _ _ h _ ha ↦ ha.trans h

/-- Every compact set in the base stage lies in a positive Fourier box. -/
theorem exists_sLocalPaleyWienerBox_of_isCompact {K : Set (SAdeles F S)} (hK : IsCompact K) :
    ∃ X > 0, K ⊆ sLocalPaleyWienerBox F S X := by
  let A (a : SAdeles F S) := ∑ v : InfinitePlace F, ‖a.1 v‖ ^ v.mult
  let D (a : SAdeles F S) := ∑ v : S, ‖a.2 v‖
  have ha : Continuous A :=
    continuous_finsetSum _ fun v _ ↦
      (continuous_norm.comp ((continuous_apply v).comp continuous_fst)).pow v.mult
  have hd : Continuous D :=
    continuous_finsetSum _ fun v _ ↦ continuous_norm.comp ((continuous_apply v).comp continuous_snd)
  obtain ⟨X, hX⟩ := (hK.image (ha.max hd)).bddAbove
  have hb (a : SAdeles F S) (hk : a ∈ K) : max (A a) (D a) ≤ X := hX ⟨a, hk, rfl⟩
  refine ⟨max 1 X, zero_lt_one.trans_le (le_max_left _ _), fun a hk ↦ ⟨?_, ?_⟩⟩
  · intro v
    exact (Finset.single_le_sum (fun w _ ↦ pow_nonneg (norm_nonneg (a.1 w)) _) (Finset.mem_univ v)).trans
      ((le_max_left (A a) (D a)).trans ((hb a hk).trans (le_max_right _ _)))
  · intro v
    exact (Finset.single_le_sum (fun w _ ↦ norm_nonneg (a.2 w)) (Finset.mem_univ v)).trans
      ((le_max_right (A a) (D a)).trans ((hb a hk).trans (le_max_right _ _)))

private def compactSupportIn {A : Type*} [TopologicalSpace A] (K : Set A) :
    Submodule ℂ (A → ℂ) where
  carrier := {φ | HasCompactSupport φ ∧ tsupport φ ⊆ K}
  zero_mem' := ⟨HasCompactSupport.zero, by simp⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, (tsupport_add _ _).trans (union_subset hf.2 hg.2)⟩
  smul_mem' := by
    intro c f hf
    change HasCompactSupport f ∧ tsupport f ⊆ K at hf
    have hs : tsupport (c • f) ⊆ tsupport f := by
      apply closure_mono
      intro x hx
      change c • f x ≠ 0 at hx
      change f x ≠ 0
      exact fun h ↦ hx (by rw [h, smul_zero])
    exact ⟨hf.1.of_isClosed_subset isClosed_closure hs, hs.trans hf.2⟩

/-- A Fourier level has compact Fourier support inside the given additive region. -/
def sLocalPaleyWienerTests (K : Set (SAdeles F S)) : Submodule ℂ (E F S) :=
  (compactSupportIn K).comap
    ((sLocalBruhatRestriction F S).comp
      ((E F S).subtype.comp (sLocalFourierCompression F S).toLinearMap))

theorem mem_sLocalPaleyWienerTests_iff (K : Set (SAdeles F S)) (f : E F S) :
    f ∈ sLocalPaleyWienerTests F S K ↔
      HasCompactSupport (sLocalBruhatRestriction F S (sLocalFourierCompression F S f).val) ∧
      tsupport (sLocalBruhatRestriction F S (sLocalFourierCompression F S f).val) ⊆ K :=
  Iff.rfl

theorem sLocalPaleyWienerTests_mono : Monotone (sLocalPaleyWienerTests F S) :=
  fun K L h f hf ↦
    let hf' := (mem_sLocalPaleyWienerTests_iff F S K f).mp hf
    (mem_sLocalPaleyWienerTests_iff F S L f).mpr ⟨hf'.1, hf'.2.trans h⟩

theorem exists_sLocalPaleyWienerBox_iff (f : E F S) :
    (∃ X > 0, f ∈ sLocalPaleyWienerTests F S (sLocalPaleyWienerBox F S X)) ↔
      HasCompactSupport (sLocalBruhatRestriction F S (sLocalFourierCompression F S f).val) := by
  constructor
  · rintro ⟨X, _, hf⟩
    exact ((mem_sLocalPaleyWienerTests_iff F S _ _).mp hf).1
  · intro h
    obtain ⟨X, hX, hs⟩ := exists_sLocalPaleyWienerBox_of_isCompact F S h
    exact ⟨X, hX, (mem_sLocalPaleyWienerTests_iff F S _ _).mpr ⟨h, hs⟩⟩

private theorem continuous_sLocalClassModulus : Continuous (sLocalClassModulus F S) :=
  NNReal.continuous_coe.comp (Units.continuous_val.comp (sQuotientNorm_proper F S).continuous)

/-- A bound on the product modulus of the test support is inherited by
the S-unit theta series. The product formula preserves the modulus of
each orbit summand. -/
theorem sLocalTheta_tsupport_of_ideleBound (f : SAdeles F S → ℂ) {Y : ℝ}
    (hf : ∀ g : (SAdeles F S)ˣ, f g.val ≠ 0 → sLocalIdeleNorm F S g ≤ Y) :
    tsupport (sLocalTheta F S f) ⊆ {q | sLocalClassModulus F S q ≤ Y} := by
  apply closure_minimal _ (isClosed_le (continuous_sLocalClassModulus F S) continuous_const)
  intro q hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  by_contra hn
  apply hq
  change (∑' u : Additive (sIntegerRing F S)ˣ, f (sIntegerDiagonal F S u.toMul.val * g.val)) = 0
  suffices h : ∀ u : Additive (sIntegerRing F S)ˣ, f (sIntegerDiagonal F S u.toMul.val * g.val) = 0 by
    simp only [h, tsum_zero]
  intro u
  let k := sUnitOrbitEquiv F S u
  have hk : (QuotientGroup.mk k.val : SIdeleQuotient F S) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr k.property
  have he : sLocalIdeleNorm F S k.val = 1 := by
    rw [← sLocalClassModulus_mk, hk]
    simp [sLocalClassModulus]
  by_contra hu
  have h := hf (k.val * g) (by simpa only [Units.val_mul, k, sUnitOrbitEquiv_val] using hu)
  rw [map_mul, he, one_mul] at h
  exact hn h

/-- The norm-one average inherits the same support bound. -/
theorem sLocalHomogeneousTheta_tsupport_of_ideleBound
    [MeasurableSpace (SLocalThetaNormOne F S)]
    (ν : Measure (SLocalThetaNormOne F S)) (ω : PontryaginDual (SLocalThetaNormOne F S))
    (f : GlobalBruhat F) {Y : ℝ}
    (hf : ∀ g : (SAdeles F S)ˣ, sLocalBruhatRestriction F S f g.val ≠ 0 →
      sLocalIdeleNorm F S g ≤ Y) :
    tsupport (sLocalHomogeneousTheta F S ν ω f) ⊆ {q | sLocalClassModulus F S q ≤ Y} := by
  apply closure_minimal _ (isClosed_le (continuous_sLocalClassModulus F S) continuous_const)
  intro q hq
  by_contra hn
  apply hq
  unfold sLocalHomogeneousTheta
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun k ↦ ?_)
  have hk : sLocalTheta F S (sLocalBruhatRestriction F S f) (k.val * q) = 0 := by
    by_contra hd
    have hb := sLocalTheta_tsupport_of_ideleBound F S _ hf (subset_tsupport _ hd)
    change sLocalClassModulus F S (k.val * q) ≤ Y at hb
    rw [sLocalClassModulus_normOne_mul] at hb
    exact hn hb
  change ((ω k : Circle) : ℂ) * sLocalTheta F S (sLocalBruhatRestriction F S f) (k.val * q) = 0
  rw [hk, mul_zero]

private theorem ideleNorm_le_projectedModulus (g : Idele F)
    (hg : ∀ v ∉ S, g.val.2 v ∈ v.adicCompletionIntegers F) :
    ideleNorm F g ≤ sLocalAdditiveModulus F S (sAdelesProjection F S g.val) := by
  let h := (sLocalEmbed F S ((Units.map (sAdelesProjection F S).toMonoidHom) g)).val
  have harch : h.val.1 = g.val.1 := by
    rw [sLocalEmbed_arch]
    rfl
  have hpoint (v : HeightOneSpectrum (𝓞 F)) : ‖g.val.2 v‖ ≤ ‖h.val.2 v‖ := by
    by_cases hv : v ∈ S
    · rw [sLocalEmbed_finite F S _ ⟨v, hv⟩]
      rfl
    · rw [sLocalEmbed_outside_one F S _ v hv, norm_one]
      have hm := hg v hv
      have hq : (1 : ℝ≥0) < Ideal.absNorm v.asIdeal := by
        exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
      rw [FinitePlace.norm_def]
      exact (WithZeroMulInt.toNNReal_le_one_iff hq).mpr
        ((HeightOneSpectrum.mem_adicCompletionIntegers _ F v).mp hm)
  change ideleNorm F g ≤ sLocalAdditiveModulus F S ((Units.map (sAdelesProjection F S).toMonoidHom) g).val
  rw [sLocalAdditiveModulus_idele]
  change ideleNorm F g ≤ ideleNorm F h
  change (∏ v : InfinitePlace F, ‖g.val.1 v‖ ^ v.mult) * (∏ᶠ v, ‖g.val.2 v‖) ≤
    (∏ v : InfinitePlace F, ‖h.val.1 v‖ ^ v.mult) * (∏ᶠ v, ‖h.val.2 v‖)
  rw [harch]
  exact mul_le_mul_of_nonneg_left (finprod_le_finprod (finiteIdeleNorm_hasFiniteMulSupport F g)
    (fun _ ↦ norm_nonneg _) (finiteIdeleNorm_hasFiniteMulSupport F h) hpoint)
    (Finset.prod_nonneg fun _ _ ↦ pow_nonneg (norm_nonneg _) _)

private theorem adelicTheta_zero_of_ideleNorm_support (f : Adeles F → ℂ)
    {Y : ℝ} (hf : ∀ g : Idele F, f g.val ≠ 0 → ideleNorm F g ≤ Y)
    (q : IdeleClass F) (hq : Y < ideleClassNorm F q) :
    adelicTheta F f q = 0 := by
  obtain ⟨g, rfl⟩ := ideleClassMap_surjective F q
  rw [adelicTheta_mk, thetaOnIdeles]
  suffices h : ∀ ξ : Fˣ, thetaSummand F f g ξ = 0 by simp only [h, tsum_zero]
  intro ξ
  by_contra hξ
  have h := hf (principalIdele F ξ * g) hξ
  rw [map_mul, ideleNorm_principal, one_mul, ← ideleClassNorm_mk] at h
  exact (not_lt_of_ge h) hq

private theorem Fourier_ideleNorm_support (f : E F S) {Y : ℝ}
    (hf : f ∈ sLocalPaleyWienerTests F S (sLocalPaleyWienerRegion F S Y))
    (g : Idele F) (hg : GlobalBruhat.evaluation F g.val (GlobalBruhat.fourier F f.val) ≠ 0) :
    ideleNorm F g ≤ ideleNorm F (sLocalCodifferentTailIdele F S) * Y := by
  let γ := sLocalCodifferentTailIdele F S
  let x := γ⁻¹ * g
  rw [sLocalFourier_eq_tailTranslate, GlobalBruhat.leftTranslate_apply,
    sLocalBruhatRestriction_reconstruct] at hg
  change sLocalBruhatRestriction F S (sLocalFourierCompression F S f).val
    (sAdelesProjection F S x.val) *
      (if ∀ v ∉ S, x.val.2 v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0) ≠ 0 at hg
  have ha : ∀ v ∉ S, x.val.2 v ∈ v.adicCompletionIntegers F := by
    by_contra hn
    simp [hn] at hg
  have hsupport := (mem_sLocalPaleyWienerTests_iff F S _ f).mp hf
  have hb := hsupport.2 (subset_tsupport _ (left_ne_zero_of_mul hg))
  change sLocalAdditiveModulus F S (sAdelesProjection F S x.val) ≤ Y at hb
  have hx := (ideleNorm_le_projectedModulus F S x ha).trans hb
  calc
    ideleNorm F g = ideleNorm F γ * ideleNorm F x := by rw [← map_mul, show γ * x = g by simp [x]]
    _ ≤ _ := mul_le_mul_of_nonneg_left hx (ideleNorm_pos F γ).le

/-- Global Fourier theta has uniform upper support with the factor from the
omitted codifferent. Both the finite-stage box and the product region yield
this bound. -/
theorem adelicTheta_fourier_tsupport_of_sLocalProductRegion
    (f : E F S) {Y : ℝ}
    (hf : f ∈ sLocalPaleyWienerTests F S (sLocalPaleyWienerRegion F S Y)) :
    tsupport (adelicTheta F (fun a ↦ GlobalBruhat.evaluation F a (GlobalBruhat.fourier F f.val))) ⊆
      {q | ideleClassNorm F q ≤ ideleNorm F (sLocalCodifferentTailIdele F S) * Y} := by
  apply closure_minimal _ (isClosed_le (ideleClassNorm_continuous F) continuous_const)
  intro q hq
  by_contra hn
  exact hq (adelicTheta_zero_of_ideleNorm_support F _ (Fourier_ideleNorm_support F S f hf) q
    (lt_of_not_ge hn))

local instance : MeasurableSpace (normOneIdeleClass F) := borel _

/-- The lower support assertion on the two-moment kernel follows by adelic
Riemann–Roch. The same bound is uniform across tests at the level. -/
theorem adelicHomogeneousTheta_tsupport_of_sLocalProductRegion
    (ν : Measure (normOneIdeleClass F))
    (ω : PontryaginDual (normOneIdeleClass F)) (f : E F S) {Y : ℝ} (hY : 0 < Y)
    (hf : f ∈ sLocalPaleyWienerTests F S (sLocalPaleyWienerRegion F S Y))
    (hm : GlobalBruhat.polarEvaluation F f.val = 0) :
    tsupport (adelicHomogeneousTheta F ν ω (fun a ↦ GlobalBruhat.evaluation F a f.val)) ⊆
      {q | (ideleNorm F (sLocalCodifferentTailIdele F S) * Y)⁻¹ ≤ ideleClassNorm F q} := by
  let B := ideleNorm F (sLocalCodifferentTailIdele F S) * Y
  have hB : 0 < B := mul_pos (ideleNorm_pos F _) hY
  apply closure_minimal _ (isClosed_le continuous_const (ideleClassNorm_continuous F))
  intro q hq
  by_contra hn
  apply hq
  unfold adelicHomogeneousTheta
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun k ↦ ?_)
  let r := k.val * q
  have hr : ideleClassNorm F r = ideleClassNorm F q := by
    rw [map_mul, show ideleClassNorm F k.val = 1 from k.property, one_mul]
  have hri : B < ideleClassNorm F r⁻¹ := by
    rw [map_inv, hr]
    exact (lt_inv_comm₀ (ideleClassNorm_pos F q) hB).mp (lt_of_not_ge hn)
  have hupper := adelicTheta_zero_of_ideleNorm_support F
    (fun a ↦ GlobalBruhat.evaluation F a (GlobalBruhat.fourier F f.val))
    (Fourier_ideleNorm_support F S f hf) r⁻¹ hri
  let u := GlobalBruhat.algebraicEquiv F f.val
  have h0 : u.val 0 = 0 := congrArg Prod.fst hm
  have h1 : GlobalBruhat.evaluation F 0 (GlobalBruhat.fourier F f.val) = 0 :=
    congrArg Prod.snd hm
  have h := congrFun (adelicTheta_riemannRoch F u.property).2 r
  rw [← GlobalBruhat.fourier_apply F f.val] at h
  change adelicTheta F u.val r =
    (ideleClassNorm F r)⁻¹ •
      adelicTheta F (fun a ↦ GlobalBruhat.evaluation F a (GlobalBruhat.fourier F f.val)) r⁻¹ +
    (ideleClassNorm F r)⁻¹ • GlobalBruhat.evaluation F 0 (GlobalBruhat.fourier F f.val) - u.val 0 at h
  simp only [hupper, h0, h1, smul_zero, add_zero, sub_zero] at h
  change ((ω k : Circle) : ℂ) * adelicTheta F (fun a ↦ GlobalBruhat.evaluation F a f.val) r = 0
  rw [show adelicTheta F (fun a ↦ GlobalBruhat.evaluation F a f.val) r = 0 from h, mul_zero]

variable {T : Finset (HeightOneSpectrum (𝓞 F))}

/-- The enlarged stage uses the actual transition, which inserts integer-ring
indicators at the added places. -/
def sLocalPaleyWienerStageTests (hST : S ⊆ T) (K : Set (SAdeles F S)) :
    Submodule ℂ (E F T) :=
  (sLocalPaleyWienerTests F S K).map (sLocalBruhatTransition F hST).toLinearMap

theorem sLocalPaleyWienerStageTests_mono (hST : S ⊆ T) :
    Monotone (sLocalPaleyWienerStageTests F S hST) :=
  fun _ _ h ↦ Submodule.map_mono (sLocalPaleyWienerTests_mono F S h)

theorem sLocalAbsolutePaleyWienerStageTests_le_invariant (hST : S ⊆ T) {X : ℝ} (hX : 0 ≤ X) :
    sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerBox F S X) ≤
      sLocalPaleyWienerStageTests F S hST
        (sLocalPaleyWienerRegion F S (X ^ (Fintype.card (InfinitePlace F) + S.card))) :=
  sLocalPaleyWienerStageTests_mono F S hST (sLocalPaleyWienerBox_subset_region F S hX)

private theorem sLocalFourierCompression_eq_global_on_embeddedIdeles
    (f : E F T) (u : (SAdeles F T)ˣ) :
    sLocalBruhatRestriction F T (sLocalFourierCompression F T f).val u.val =
      GlobalBruhat.evaluation F (sLocalEmbed F T u).val.val (GlobalBruhat.fourier F f.val) := by
  rw [sLocalFourier_codifferent_reconstruct, sLocalEmbed_project F T u]
  have h (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ T) :
      (sLocalEmbed F T u).val.val.2 v ∈ finitePlaceIntegerAnnihilator F v := by
    rw [sLocalEmbed_outside_one F T u v hv, finitePlaceIntegerAnnihilator_eq_differentBall]
    change ‖(1 : v.adicCompletion F)‖ ≤ _
    rw [norm_one]
    exact one_le_pow₀ (by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le)
  rw [ite_eq_left h, mul_one]
  exact sLocalBruhatCorestrict_restrict F T (GlobalBruhat.fourier F f.val) u.val

/-- The local Fourier theta upper-support clause holds uniformly at the
enlarged stage, for both the coordinate and product support bounds. -/
theorem sLocalPaleyWienerStageTests_fourierSupport
    [MeasurableSpace (SLocalThetaNormOne F T)]
    (ν : Measure (SLocalThetaNormOne F T)) (ω : PontryaginDual (SLocalThetaNormOne F T))
    (hST : S ⊆ T) (f : E F T) {Y : ℝ}
    (hf : f ∈ sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerRegion F S Y)) :
    tsupport (sLocalHomogeneousTheta F T ν ω (sLocalFourierCompression F T f).val) ⊆
      {q | sLocalClassModulus F T q ≤ ideleNorm F (sLocalCodifferentTailIdele F S) * Y} := by
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
  apply sLocalHomogeneousTheta_tsupport_of_ideleBound
  intro u hu
  rw [sLocalFourierCompression_eq_global_on_embeddedIdeles F] at hu
  exact Fourier_ideleNorm_support F S g hg (sLocalEmbed F T u).val hu

/-- The lower-support clause applies to the same enlarged-stage tests with
both evaluation moments removed. -/
theorem sLocalPaleyWienerStageTests_globalSupport
    (ν : Measure (normOneIdeleClass F)) (ω : PontryaginDual (normOneIdeleClass F))
    (hST : S ⊆ T) (f : E F T) {Y : ℝ} (hY : 0 < Y)
    (hf : f ∈ sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerRegion F S Y))
    (hm : GlobalBruhat.polarEvaluation F f.val = 0) :
    tsupport (adelicHomogeneousTheta F ν ω (fun a ↦ GlobalBruhat.evaluation F a f.val)) ⊆
      {q | (ideleNorm F (sLocalCodifferentTailIdele F S) * Y)⁻¹ ≤ ideleClassNorm F q} := by
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
  exact adelicHomogeneousTheta_tsupport_of_sLocalProductRegion F S ν ω g hY hg hm

private theorem sLocalFourierCompression_leftTranslate_restrict
    (g : (SAdeles F S)ˣ) (f : E F S) (a : SAdeles F S) :
    sLocalBruhatRestriction F S
        (sLocalFourierCompression F S (sLocalBruhatLeftTranslate F S g f)).val a =
      (sLocalIdeleNorm F S g : ℂ) •
        sLocalBruhatRestriction F S (sLocalFourierCompression F S f).val (g.val * a) := by
  let G := (sLocalEmbed F S g).val
  change sLocalBruhatRestriction F S
      (sLocalBruhatCorestrict F S (GlobalBruhat.fourier F (GlobalBruhat.leftTranslate F G f.val))).val a = _
  rw [sLocalBruhatCorestrict_restrict, globalBruhat_fourier_leftTranslate,
    map_smul, Pi.smul_apply]
  change (ideleNorm F G : ℂ) • GlobalBruhat.evaluation F (sLocalBruhatPad F S a)
      (GlobalBruhat.leftTranslate F G⁻¹ (GlobalBruhat.fourier F f.val)) =
    (sLocalIdeleNorm F S g : ℂ) • sLocalBruhatRestriction F S
      (sLocalBruhatCorestrict F S (GlobalBruhat.fourier F f.val)).val (g.val * a)
  rw [GlobalBruhat.leftTranslate_apply, inv_inv, ← sLocalBruhatPad_mul_project,
    sLocalEmbed_project F S g, sLocalBruhatCorestrict_restrict]
  rfl

theorem sLocalPaleyWienerTests_leftTranslate
    (g : (SAdeles F S)ˣ) (K L : Set (SAdeles F S))
    (hK : ∀ a : SAdeles F S, g.val * a ∈ K → a ∈ L)
    (f : E F S) (hf : f ∈ sLocalPaleyWienerTests F S K) :
    sLocalBruhatLeftTranslate F S g f ∈ sLocalPaleyWienerTests F S L := by
  obtain ⟨hc, hs⟩ := (mem_sLocalPaleyWienerTests_iff F S K f).mp hf
  apply (mem_sLocalPaleyWienerTests_iff F S L _).mpr
  let e : SAdeles F S ≃ₜ SAdeles F S :=
    { toFun := fun a ↦ g.val * a
      invFun := fun a ↦ g.inv * a
      left_inv := fun a ↦ by
        change g.inv * (g.val * a) = a
        rw [← mul_assoc, g.inv_val, one_mul]
      right_inv := fun a ↦ by
        change g.val * (g.inv * a) = a
        rw [← mul_assoc, g.val_inv, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  have hsub : tsupport (sLocalBruhatRestriction F S
        (sLocalFourierCompression F S (sLocalBruhatLeftTranslate F S g f)).val) ⊆
      e ⁻¹' tsupport (sLocalBruhatRestriction F S (sLocalFourierCompression F S f).val) := by
    apply closure_minimal _ (isClosed_closure.preimage e.continuous)
    intro a ha
    apply subset_tsupport
    intro hz
    apply ha
    rw [sLocalFourierCompression_leftTranslate_restrict]
    change sLocalBruhatRestriction F S (sLocalFourierCompression F S f).val (g.val * a) = 0 at hz
    rw [hz, smul_zero]
  exact ⟨(e.isCompact_preimage.mpr hc).of_isClosed_subset isClosed_closure hsub,
    fun a ha ↦ hK a (hs (hsub ha))⟩

theorem sLocalExpSection_embed (t : ℝ) :
    (sLocalEmbed F S (sLocalExpSection F S (Multiplicative.ofAdd t))).val =
      ideleExpSection F (Multiplicative.ofAdd t) := by
  let u := sLocalExpSection F S (Multiplicative.ofAdd t)
  let r := ideleExpSection F (Multiplicative.ofAdd t)
  change (sLocalEmbed F S u).val = r
  apply Units.ext
  apply Prod.ext
  · rw [sLocalEmbed_arch]
    rfl
  · apply RestrictedProduct.ext
    intro v
    change (sLocalEmbed F S u).val.val.2 v = r.val.2 v
    by_cases hv : v ∈ S
    · exact sLocalEmbed_finite F S u ⟨v, hv⟩
    · rw [sLocalEmbed_outside_one F S u v hv]
      rfl

theorem sLocalExpSection_arch_norm (t : ℝ) (v : InfinitePlace F) :
    ‖(sLocalExpSection F S (Multiplicative.ofAdd t)).val.1 v‖ =
      Real.exp (t / Module.finrank ℚ F) := by
  let u := sLocalExpSection F S (Multiplicative.ofAdd t)
  have h := congrArg (fun g : Idele F ↦ g.val.1 v) (sLocalExpSection_embed F S t)
  change (sLocalEmbed F S u).val.val.1 v = _ at h
  rw [sLocalEmbed_arch, (ideleExpSection_components F (Multiplicative.ofAdd t)).1 v] at h
  change u.val.1 v = infinitePlaceRealEmbedding F v (Real.exp (t / Module.finrank ℚ F)) at h
  change ‖u.val.1 v‖ = _
  rw [h, (infinitePlaceRealEmbedding_isometry F v).norm_map_of_map_zero (map_zero _),
    Real.norm_of_nonneg (Real.exp_pos _).le]

theorem sLocalExpSection_finite (t : ℝ) (v : S) :
    (sLocalExpSection F S (Multiplicative.ofAdd t)).val.2 v = 1 := by
  let u := sLocalExpSection F S (Multiplicative.ofAdd t)
  have h := congrArg (fun g : Idele F ↦ g.val.2 v.val) (sLocalExpSection_embed F S t)
  change (sLocalEmbed F S u).val.val.2 v.val = _ at h
  rw [sLocalEmbed_finite F S u v, (ideleExpSection_components F (Multiplicative.ofAdd t)).2] at h
  exact h

private theorem sLocalExpSection_arch_finite (t : ℝ) (ht : 0 ≤ t) :
    (∀ v : InfinitePlace F, 1 ≤ ‖(sLocalExpSection F S (Multiplicative.ofAdd t)).val.1 v‖ ^ v.mult) ∧
    (∀ v : S, (sLocalExpSection F S (Multiplicative.ofAdd t)).val.2 v = 1) := by
  refine ⟨fun v ↦ ?_, sLocalExpSection_finite F S t⟩
  rw [sLocalExpSection_arch_norm]
  exact one_le_pow₀ (Real.one_le_exp (div_nonneg ht (Nat.cast_nonneg _)))

/-- Positive norm translations preserve the coordinate Fourier levels. -/
theorem sLocalPaleyWienerBox_leftTranslate {X t : ℝ} (ht : 0 ≤ t)
    (f : E F S) (hf : f ∈ sLocalPaleyWienerTests F S (sLocalPaleyWienerBox F S X)) :
    sLocalBruhatLeftTranslate F S (sLocalExpSection F S (Multiplicative.ofAdd t)) f ∈
      sLocalPaleyWienerTests F S (sLocalPaleyWienerBox F S X) := by
  let u := sLocalExpSection F S (Multiplicative.ofAdd t)
  obtain ⟨harch, hfinite⟩ := sLocalExpSection_arch_finite F S t ht
  apply sLocalPaleyWienerTests_leftTranslate F S u _ _ _ f hf
  intro a ha
  refine ⟨fun v ↦ ?_, fun v ↦ ?_⟩
  · have h := ha.1 v
    change ‖u.val.1 v * a.1 v‖ ^ v.mult ≤ X at h
    rw [norm_mul, mul_pow] at h
    exact (le_mul_of_one_le_left (pow_nonneg (norm_nonneg _) _) (harch v)).trans h
  · have h := ha.2 v
    change ‖u.val.2 v * a.2 v‖ ≤ X at h
    rwa [hfinite v, one_mul] at h

/-- Positive norm translations also preserve the product Fourier levels. -/
theorem sLocalPaleyWienerRegion_leftTranslate {Y t : ℝ} (ht : 0 ≤ t)
    (f : E F S) (hf : f ∈ sLocalPaleyWienerTests F S (sLocalPaleyWienerRegion F S Y)) :
    sLocalBruhatLeftTranslate F S (sLocalExpSection F S (Multiplicative.ofAdd t)) f ∈
      sLocalPaleyWienerTests F S (sLocalPaleyWienerRegion F S Y) := by
  let u := sLocalExpSection F S (Multiplicative.ofAdd t)
  obtain ⟨harch, hfinite⟩ := sLocalExpSection_arch_finite F S t ht
  apply sLocalPaleyWienerTests_leftTranslate F S u _ _ _ f hf
  intro a ha
  change sLocalAdditiveModulus F S (u.val * a) ≤ Y at ha
  change sLocalAdditiveModulus F S a ≤ Y
  apply le_trans _ ha
  unfold sLocalAdditiveModulus
  have hA (v : InfinitePlace F) : ‖a.1 v‖ ^ v.mult ≤ ‖(u.val * a).1 v‖ ^ v.mult := by
    change _ ≤ ‖u.val.1 v * a.1 v‖ ^ v.mult
    rw [norm_mul, mul_pow]
    exact le_mul_of_one_le_left (pow_nonneg (norm_nonneg _) _) (harch v)
  have hN (v : S) : ‖(u.val * a).2 v‖ = ‖a.2 v‖ := by
    change ‖u.val.2 v * a.2 v‖ = _
    rw [hfinite v, one_mul]
  simp_rw [hN]
  exact mul_le_mul_of_nonneg_right
    (Finset.prod_le_prod (fun _ _ ↦ pow_nonneg (norm_nonneg _) _) (fun v _ ↦ hA v))
    (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)

theorem sLocalPaleyWienerStageTests_leftTranslate
    (hST : S ⊆ T) (K L : Set (SAdeles F S)) {t : ℝ}
    (hK : ∀ f ∈ sLocalPaleyWienerTests F S K,
      sLocalBruhatLeftTranslate F S (sLocalExpSection F S (Multiplicative.ofAdd t)) f ∈
        sLocalPaleyWienerTests F S L)
    (f : E F T) (hf : f ∈ sLocalPaleyWienerStageTests F S hST K) :
    sLocalBruhatLeftTranslate F T (sLocalExpSection F T (Multiplicative.ofAdd t)) f ∈
      sLocalPaleyWienerStageTests F S hST L := by
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
  refine Submodule.mem_map.mpr ⟨_, hK g hg, ?_⟩
  apply Subtype.ext
  change GlobalBruhat.leftTranslate F
      (sLocalEmbed F S (sLocalExpSection F S (Multiplicative.ofAdd t))).val g.val =
    GlobalBruhat.leftTranslate F
      (sLocalEmbed F T (sLocalExpSection F T (Multiplicative.ofAdd t))).val g.val
  rw [sLocalExpSection_embed, sLocalExpSection_embed]

theorem sLocalAbsolutePaleyWienerStageTests_leftTranslate
    (hST : S ⊆ T) {X t : ℝ} (ht : 0 ≤ t)
    (f : E F T) (hf : f ∈ sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerBox F S X)) :
    sLocalBruhatLeftTranslate F T (sLocalExpSection F T (Multiplicative.ofAdd t)) f ∈
      sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerBox F S X) :=
  sLocalPaleyWienerStageTests_leftTranslate F S hST _ _ (sLocalPaleyWienerBox_leftTranslate F S ht) f hf

theorem sLocalInvariantPaleyWienerStageTests_leftTranslate
    (hST : S ⊆ T) {Y t : ℝ} (ht : 0 ≤ t)
    (f : E F T) (hf : f ∈ sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerRegion F S Y)) :
    sLocalBruhatLeftTranslate F T (sLocalExpSection F T (Multiplicative.ofAdd t)) f ∈
      sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerRegion F S Y) :=
  sLocalPaleyWienerStageTests_leftTranslate F S hST _ _ (sLocalPaleyWienerRegion_leftTranslate F S ht) f hf

/-- Idelic translations preserve the common kernel of the two moments. -/
theorem sLocalPaleyWiener_leftTranslate_preserves_moments
    (g : (SAdeles F T)ˣ) (f : E F T) (hf : GlobalBruhat.polarEvaluation F f.val = 0) :
    GlobalBruhat.polarEvaluation F (sLocalBruhatLeftTranslate F T g f).val = 0 := by
  change GlobalBruhat.polarEvaluation F (GlobalBruhat.leftTranslate F (sLocalEmbed F T g).val f.val) = 0
  rw [polarEvaluation_leftTranslate, hf]
  simp

/-- Insertion of a printed unit indicator at any added place forces the
value at zero to vanish. Such a level has at most one independent evaluation
moment. -/
theorem sLocalPaleyWiener_unitTail_moment_codim_le_one
    (D : Submodule ℂ (E F T)) (v : T)
    (hD : ∀ f ∈ D, ∀ a : SAdeles F T, a.2 v = 0 → sLocalBruhatRestriction F T f.val a = 0) :
    let A := (GlobalBruhat.polarEvaluation F).toLinearMap.comp ((E F T).subtype.comp D.subtype)
    Module.finrank ℂ A.range ≤ 1 := by
  let A := (GlobalBruhat.polarEvaluation F).toLinearMap.comp ((E F T).subtype.comp D.subtype)
  have hzero (f : D) : (A f).1 = 0 := by
    change GlobalBruhat.evaluation F 0 f.val.val = 0
    rw [sLocalBruhatRestriction_reconstruct, hD f.val f.property]
    · exact zero_mul _
    · rw [map_zero]
      rfl
  let L : A.range →ₗ[ℂ] ℂ := (LinearMap.snd ℂ ℂ ℂ).comp A.range.subtype
  have hfirst (x : A.range) : x.val.1 = 0 := by
    obtain ⟨f, hf⟩ := x.property
    exact (congrArg Prod.fst hf).symm.trans (hzero f)
  have hinj : Injective L := by
    intro x y h
    apply Subtype.ext
    exact Prod.ext ((hfirst x).trans (hfirst y).symm) h
  exact (LinearMap.finrank_le_finrank_of_injective hinj).trans_eq (Module.finrank_self ℂ)

section HomogeneousLevels

variable [MeasurableSpace (SLocalThetaNormOne F T)] [BorelSpace (SLocalThetaNormOne F T)]
variable (ν : Measure (SLocalThetaNormOne F T)) [ν.IsHaarMeasure]
variable (ω : PontryaginDual (SLocalThetaNormOne F T))

omit [BorelSpace (SLocalThetaNormOne F T)] [ν.IsHaarMeasure] in
theorem sLocalHomogeneousTheta_translate_test
    (u : (SAdeles F T)ˣ) (f : E F T) (q : SIdeleQuotient F T) :
    sLocalHomogeneousTheta F T ν ω (sLocalBruhatLeftTranslate F T u f).val q =
      sLocalHomogeneousTheta F T ν ω f.val ((QuotientGroup.mk u : SIdeleQuotient F T)⁻¹ * q) := by
  unfold sLocalHomogeneousTheta
  refine integral_congr_ae (.of_forall fun k ↦ ?_)
  let d : SIdeleQuotient F T := QuotientGroup.mk u
  change (ω k : ℂ) * sLocalThetaOperator F T (sLocalBruhatLeftTranslate F T u f) (k.val * q) =
    (ω k : ℂ) * sLocalThetaOperator F T f (k.val * (d⁻¹ * q))
  rw [sLocalThetaOperator_leftTranslate]
  let z : SIdeleQuotient F T := k.val
  have he : d⁻¹ * (z * q) = z * (d⁻¹ * q) := mul_left_comm (d⁻¹) z q
  exact congrArg (fun x ↦ (ω k : ℂ) * sLocalThetaOperator F T f x) he

omit [BorelSpace (SLocalThetaNormOne F T)] [ν.IsHaarMeasure] in
private theorem sLocalHomogeneousTheta_smul_test
    (a : ℂ) (f : E F T) (q : SIdeleQuotient F T) :
    sLocalHomogeneousTheta F T ν ω (a • f).val q =
      a * sLocalHomogeneousTheta F T ν ω f.val q := by
  unfold sLocalHomogeneousTheta
  rw [← integral_const_mul]
  refine integral_congr_ae (.of_forall fun k ↦ ?_)
  change (ω k : ℂ) * sLocalThetaOperator F T (a • f) (k.val * q) =
    a * ((ω k : ℂ) * sLocalThetaOperator F T f (k.val * q))
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]

/-- Translation by an idele class is represented by its norm-ray
translate scaled by the norm-one character. This transfers test-level
support estimates to the homogeneous space with both moments imposed. -/
theorem sLocalPaleyWiener_homogeneousTranslate
    (hST : S ⊆ T) (K L : Set (SAdeles F S)) (c : SIdeleQuotient F T)
    (hlevel : ∀ t : ℝ, t = Real.log (sLocalClassModulus F T c) →
      ∀ f ∈ sLocalPaleyWienerStageTests F S hST K,
      sLocalBruhatLeftTranslate F T (sLocalExpSection F T (Multiplicative.ofAdd t)) f ∈
        sLocalPaleyWienerStageTests F S hST L)
    (f : E F T) (hf : f ∈ sLocalPaleyWienerStageTests F S hST K) :
    ∃ g ∈ sLocalPaleyWienerStageTests F S hST L,
      (GlobalBruhat.polarEvaluation F f.val = 0 → GlobalBruhat.polarEvaluation F g.val = 0) ∧
      ∀ q, sLocalHomogeneousTheta F T ν ω g.val q =
        sLocalHomogeneousTheta F T ν ω f.val (c⁻¹ * q) := by
  obtain ⟨⟨t,k⟩, rfl⟩ := (sLocalZetaSplit F T).surjective c
  let u := sLocalExpSection F T (Multiplicative.ofAdd t)
  let d : SIdeleQuotient F T := QuotientGroup.mk u
  let f' := sLocalBruhatLeftTranslate F T u f
  have ht : t = Real.log (sLocalClassModulus F T (sLocalZetaSplit F T (t,k))) :=
    (sLocalZetaSplit_logModulus F T (t,k)).symm
  refine ⟨(ω k : ℂ) • f', Submodule.smul_mem _ _ (hlevel t ht f hf), ?_, fun q ↦ ?_⟩
  · intro hm
    have hm' := sLocalPaleyWiener_leftTranslate_preserves_moments F u f hm
    change GlobalBruhat.polarEvaluation F ((ω k : ℂ) • f'.val) = 0
    rw [map_smul, show GlobalBruhat.polarEvaluation F f'.val = 0 from hm', smul_zero]
  · rw [sLocalHomogeneousTheta_smul_test, sLocalHomogeneousTheta_translate_test]
    change (ω k : ℂ) * sLocalHomogeneousTheta F T ν ω f.val (d⁻¹ * q) =
      sLocalHomogeneousTheta F T ν ω f.val ((d * k.val)⁻¹ * q)
    let z : SIdeleQuotient F T := k.val
    have he : (d * z)⁻¹ * q = (k⁻¹).val * (d⁻¹ * q) :=
      (congrArg (fun x : SIdeleQuotient F T ↦ x * q) (mul_inv_rev d z)).trans
        (mul_assoc z⁻¹ d⁻¹ q)
    have hχ := sLocalHomogeneousTheta_translate F T ν ω f.val k⁻¹ (d⁻¹ * q)
    rw [he, hχ, map_inv, Circle.coe_inv, inv_inv]

theorem sLocalAbsolutePaleyWiener_translate
    (hST : S ⊆ T) (X : ℝ) (f : E F T)
    (hf : f ∈ sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerBox F S X))
    (c : SIdeleQuotient F T) (hc : 1 ≤ sLocalClassModulus F T c) :
    ∃ g ∈ sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerBox F S X),
      (GlobalBruhat.polarEvaluation F f.val = 0 → GlobalBruhat.polarEvaluation F g.val = 0) ∧
      ∀ q, sLocalHomogeneousTheta F T ν ω g.val q =
        sLocalHomogeneousTheta F T ν ω f.val (c⁻¹ * q) :=
  sLocalPaleyWiener_homogeneousTranslate F S ν ω hST _ _ c (fun _ ht ↦
    sLocalAbsolutePaleyWienerStageTests_leftTranslate F S hST (ht.symm ▸ Real.log_nonneg hc)) f hf

theorem sLocalInvariantPaleyWiener_translate
    (hST : S ⊆ T) (Y : ℝ) (f : E F T)
    (hf : f ∈ sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerRegion F S Y))
    (c : SIdeleQuotient F T) (hc : 1 ≤ sLocalClassModulus F T c) :
    ∃ g ∈ sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerRegion F S Y),
      (GlobalBruhat.polarEvaluation F f.val = 0 → GlobalBruhat.polarEvaluation F g.val = 0) ∧
      ∀ q, sLocalHomogeneousTheta F T ν ω g.val q =
        sLocalHomogeneousTheta F T ν ω f.val (c⁻¹ * q) :=
  sLocalPaleyWiener_homogeneousTranslate F S ν ω hST _ _ c (fun _ ht ↦
    sLocalInvariantPaleyWienerStageTests_leftTranslate F S hST (ht.symm ▸ Real.log_nonneg hc)) f hf

end HomogeneousLevels

end

end Masullo
