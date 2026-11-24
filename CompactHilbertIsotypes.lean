import HardySobolevTranslations
import CompactGroupAveraging
import CompactCharacterCompleteness
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space

open Filter Function MeasureTheory Set Topology
open scoped Classical ENNReal InnerProductSpace

namespace Masullo

noncomputable section

section CompactAction

variable {K E : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [T2Space K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (ρ : K →* (E →L[ℂ] E))

/-- The eigenspace for a continuous circle character of a compact group. -/
abbrev compactActionIsotype (ω : PontryaginDual K) : Submodule ℂ E :=
  fixedSubmodule (twistedCircleAction ω.toMonoidHom ρ)

local instance compactActionIsotype_complete (ω : PontryaginDual K) :
    CompleteSpace (compactActionIsotype ρ ω) :=
  (fixedSubmodule_isClosed _).completeSpace_coe

private def compactActionLinearIsometry (hn : ∀ g u, ‖ρ g u‖ = ‖u‖) (g : K) : E →ₗᵢ[ℂ] E :=
  ⟨(ρ g).toLinearMap, hn g⟩

variable (hρ : Continuous (fun z : K × E => ρ z.1 z.2))
  (hn : ∀ g u, ‖ρ g u‖ = ‖u‖)
  (ν : Measure K) [ν.IsHaarMeasure] [IsProbabilityMeasure ν]

omit [T2Space K] [SecondCountableTopology K] in
include hρ hn in
/-- With probability Haar measure, the Pettis character average is the
orthogonal projection. The closed differences are precisely its kernel. -/
theorem compactActionProjection_pettis (ω : PontryaginDual K) :
    let U := compactActionIsotype ρ ω
    (∀ u, HasPositivePettisIntegral ν (fun g => twistedCircleAction ω.toMonoidHom ρ g u)
      (U.starProjection u)) ∧
    U.starProjection.ker = (actionDifferenceSpan (twistedCircleAction ω.toMonoidHom ρ)).topologicalClosure ∧
    (∃ e : (E ⧸ (actionDifferenceSpan (twistedCircleAction ω.toMonoidHom ρ)).topologicalClosure) ≃L[ℂ] U,
      ∀ u, (e (Submodule.Quotient.mk u) : E) = U.starProjection u) := by
  let A := twistedCircleAction ω.toMonoidHom ρ
  let U := compactActionIsotype ρ ω
  obtain ⟨P, hP, hrange, _, _, hquot, hker⟩ :=
    (compactGroupIsotypicAverage ρ hρ ω.toMonoidHom ω.continuous ν).2
  have hreal : ν.real univ = 1 := by simp [Measure.real]
  have horth : P = U.starProjection := by
    ext u : 1
    symm
    apply U.eq_starProjection_of_mem_of_inner_eq_zero
    · exact hrange.subset (mem_range_self u)
    · intro v hv
      apply inner_eq_zero_symm.mp
      have hv' (g : K) : ⟪v, A g u⟫_ℂ = ⟪v, u⟫_ℂ := by
        have hfix : A g v = v := hv g
        let T : E →ₗᵢ[ℂ] E := ⟨(A g).toLinearMap, fun x => by
          change ‖(((ω g)⁻¹ : Circle) : ℂ) • ρ g x‖ = _
          rw [norm_smul, Circle.norm_coe, one_mul, hn]⟩
        have he := T.inner_map_map v u
        change ⟪A g v, A g u⟫_ℂ = ⟪v, u⟫_ℂ at he
        rwa [hfix] at he
      have he : ⟪v, P u⟫_ℂ = ⟪v, u⟫_ℂ := by
        change (innerSL ℂ v) (P u) = _
        rw [(hP u (innerSL ℂ v)).2]
        change (∫ g, ⟪v, A g u⟫_ℂ ∂ν) = _
        simp_rw [hv', integral_const, hreal, one_smul]
      rw [inner_sub_right, he, sub_self]
  refine ⟨fun u => horth ▸ hP u, horth ▸ hker, ?_⟩
  rw [← hker]
  obtain ⟨e, he⟩ := hquot
  exact ⟨e, fun u => (he u).trans (DFunLike.congr_fun horth u)⟩

omit [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] [CompleteSpace E] in
include hn in
private theorem compactActionIsotype_orthogonal :
    OrthogonalFamily ℂ (fun ω : PontryaginDual K => compactActionIsotype ρ ω)
      (fun ω => (compactActionIsotype ρ ω).subtypeₗᵢ) := by
  intro ω η hne u v
  obtain ⟨g, hg⟩ : ∃ g, ω g ≠ η g := by
    by_contra! h
    exact hne (DFunLike.ext _ _ h)
  have hu := (mem_circleIsotype_iff ω.toMonoidHom ρ u.val).mp u.property g
  have hv := (mem_circleIsotype_iff η.toMonoidHom ρ v.val).mp v.property g
  have h := (compactActionLinearIsometry ρ hn g).inner_map_map u.val v.val
  change ⟪ρ g u.val, ρ g v.val⟫_ℂ = _ at h
  change ρ g u.val = (ω g : ℂ) • u.val at hu
  change ρ g v.val = (η g : ℂ) • v.val at hv
  rw [hu, hv, inner_smul_left, inner_smul_right, ← mul_assoc, ← Circle.coe_inv_eq_conj] at h
  change ⟪u.val, v.val⟫_ℂ = 0
  have h' : ((((ω g)⁻¹ : Circle) : ℂ) * (η g : ℂ) - 1) * ⟪u.val, v.val⟫_ℂ = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  refine (mul_eq_zero.mp h').resolve_left (fun hzero => hg ?_)
  have hCircle : (ω g)⁻¹ * η g = 1 := Subtype.ext (sub_eq_zero.mp hzero)
  exact inv_mul_eq_one.mp hCircle

include hρ hn ν in
private theorem compactActionIsotype_total :
    (⨆ ω : PontryaginDual K, compactActionIsotype ρ ω).topologicalClosure = ⊤ := by
  let H := (⨆ ω : PontryaginDual K, compactActionIsotype ρ ω).topologicalClosure
  letI : CompleteSpace H := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  apply (Submodule.orthogonal_eq_bot_iff (K := H)).mp
  apply (Submodule.eq_bot_iff _).mpr
  intro u hu
  let f (g : K) := ⟪u, ρ g u⟫_ℂ
  have hf : Continuous f := (innerSL ℂ u).continuous.comp
    (hρ.comp (continuous_id.prodMk continuous_const))
  have hLp : MemLp f 2 ν := hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcoeff (ω : PontryaginDual K) : ∫ g, star (ω g : ℂ) * f g ∂ν = 0 := by
    let U := compactActionIsotype ρ ω
    have hm : U.starProjection u ∈ H :=
      (le_iSup (fun τ : PontryaginDual K => compactActionIsotype ρ τ) ω |>.trans
        (Submodule.le_topologicalClosure _)) (U.starProjection_apply_mem u)
    have he := ((compactActionProjection_pettis ρ hρ hn ν ω).1 u (innerSL ℂ u)).2
    have hz := H.inner_left_of_mem_orthogonal hm hu
    change ⟪u, U.starProjection u⟫_ℂ = _ at he
    rw [hz] at he
    calc
      _ = ∫ g, ⟪u, twistedCircleAction ω.toMonoidHom ρ g u⟫_ℂ ∂ν := by
        apply integral_congr_ae (Eventually.of_forall fun g => ?_)
        change star (ω g : ℂ) * ⟪u, ρ g u⟫_ℂ =
          ⟪u, (((ω g)⁻¹ : Circle) : ℂ) • ρ g u⟫_ℂ
        rw [inner_smul_right, Circle.coe_inv_eq_conj]
        rfl
      _ = 0 := he.symm
  letI : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  have hae := ae_eq_zero_of_character_integral_eq_zero ν hLp hcoeff
  have hz := (hf.ae_eq_iff_eq (μ := ν) continuous_const).mp hae
  have hone := congrFun hz 1
  change ⟪u, ρ 1 u⟫_ℂ = 0 at hone
  rw [map_one] at hone
  exact inner_self_eq_zero.mp hone

/-- The representation space is the Hilbert sum of its closed character isotypes. -/
def compactActionIsotypeSum :
    E ≃ₗᵢ[ℂ] lp (fun ω : PontryaginDual K => compactActionIsotype ρ ω) 2 :=
  (IsHilbertSum.mkInternal _ (compactActionIsotype_orthogonal ρ hn)
    (compactActionIsotype_total ρ hρ hn ν).ge).linearIsometryEquiv

/-- The Hilbert-sum coordinates are exactly the character projections. -/
theorem compactActionIsotypeSum_apply (ω : PontryaginDual K) (u : E) :
    compactActionIsotypeSum ρ hρ hn ν u ω =
      (compactActionIsotype ρ ω).orthogonalProjectionOnto u := by
  let V := fun ω : PontryaginDual K => compactActionIsotype ρ ω
  let H := IsHilbertSum.mkInternal V (compactActionIsotype_orthogonal ρ hn)
    (compactActionIsotype_total ρ hρ hn ν).ge
  let J := H.linearIsometryEquiv
  change J u ω = (V ω).orthogonalProjectionOnto u
  apply ext_inner_left ℂ
  intro x
  calc
    ⟪x, J u ω⟫_ℂ = ⟪lp.single 2 ω x, J u⟫_ℂ := (lp.inner_single_left ω x (J u)).symm
    _ = ⟪J.symm (lp.single 2 ω x), u⟫_ℂ := by
      rw [← J.symm.inner_map_map, LinearIsometryEquiv.symm_apply_apply]
    _ = ⟪x, (V ω).orthogonalProjectionOnto u⟫_ℂ := by
      rw [H.linearIsometryEquiv_symm_apply_single]
      exact ((V ω).inner_orthogonalProjectionOnto_eq_of_mem_left x u).symm

omit [T2Space K] [SecondCountableTopology K] in
include hρ hn ν in
/-- The isotypic coordinate is a surjective open map onto its closed range. -/
theorem compactActionProjection_open_surjective (ω : PontryaginDual K) :
    IsOpenMap (compactActionIsotype ρ ω).orthogonalProjectionOnto ∧
      Surjective (compactActionIsotype ρ ω).orthogonalProjectionOnto := by
  let U := compactActionIsotype ρ ω
  let D := (actionDifferenceSpan (twistedCircleAction ω.toMonoidHom ρ)).topologicalClosure
  obtain ⟨e, he⟩ := (compactActionProjection_pettis ρ hρ hn ν ω).2.2
  have h : (U.orthogonalProjectionOnto : E → U) = e ∘ D.mkQL :=
    funext fun u => Subtype.ext (he u).symm
  rw [h]
  exact ⟨e.toHomeomorph.isOpenMap.comp D.isOpenQuotientMap_mkQL.isOpenMap,
    e.surjective.comp D.isOpenQuotientMap_mkQL.surjective⟩

include hρ hn ν in
/-- The Hilbert-sum transform taken coordinatewise into the locally convex product. -/
theorem compactActionProjection_product :
    let P (u : E) (ω : PontryaginDual K) := (compactActionIsotype ρ ω).orthogonalProjectionOnto u
    Continuous P ∧ Injective P ∧
      ∃ e : E ≃ₗᵢ[ℂ] lp (fun ω : PontryaginDual K => compactActionIsotype ρ ω) 2,
        ∀ u ω, e u ω = P u ω := by
  let J := compactActionIsotypeSum ρ hρ hn ν
  refine ⟨continuous_pi fun ω => (compactActionIsotype ρ ω).orthogonalProjectionOnto.continuous,
    ?_, J, fun u ω => compactActionIsotypeSum_apply ρ hρ hn ν ω u⟩
  intro u v hv
  apply J.injective
  ext ω
  rw [compactActionIsotypeSum_apply, compactActionIsotypeSum_apply]
  exact congrArg Subtype.val (congrFun hv ω)

/-- The projection, topological quotient and Hilbert sum assertions of
Proposition 10.1.1.5 for a compact character action. -/
def HasCompactIsotypeDecomposition : Prop :=
  (∀ ω : PontryaginDual K,
    let U := compactActionIsotype ρ ω
    let D := (actionDifferenceSpan (twistedCircleAction ω.toMonoidHom ρ)).topologicalClosure
    (∀ u, HasPositivePettisIntegral ν (fun g => twistedCircleAction ω.toMonoidHom ρ g u)
      (U.starProjection u)) ∧
    IsOpenMap U.orthogonalProjectionOnto ∧ Surjective U.orthogonalProjectionOnto ∧
    U.starProjection.ker = D ∧
    ∃ e : (E ⧸ D) ≃L[ℂ] U, ∀ u, e (Submodule.Quotient.mk u) = U.orthogonalProjectionOnto u) ∧
  (let P (u : E) (ω : PontryaginDual K) := (compactActionIsotype ρ ω).orthogonalProjectionOnto u
   Continuous P ∧ Injective P ∧
    ∃ e : E ≃ₗᵢ[ℂ] lp (fun ω : PontryaginDual K => compactActionIsotype ρ ω) 2,
      ∀ u ω, e u ω = P u ω)

include hρ hn in
theorem hasCompactIsotypeDecomposition : HasCompactIsotypeDecomposition ρ ν := by
  refine ⟨fun ω => ?_, compactActionProjection_product ρ hρ hn ν⟩
  obtain ⟨hP, hker, e, he⟩ := compactActionProjection_pettis ρ hρ hn ν ω
  obtain ⟨ho, hs⟩ := compactActionProjection_open_surjective ρ hρ hn ν ω
  exact ⟨hP, ho, hs, hker, e, fun u => Subtype.ext (he u)⟩

/-- Normalizing on the whole compact group gives probability Haar measure. -/
def compactActionHaarProbability : Measure K := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)

instance compactActionHaarProbability_isHaar :
    (compactActionHaarProbability (K := K)).IsHaarMeasure := inferInstanceAs
  (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)).IsHaarMeasure

instance compactActionHaarProbability_isProbability :
    IsProbabilityMeasure (compactActionHaarProbability (K := K)) :=
  ⟨by simpa only [compactActionHaarProbability, TopologicalSpace.PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K)))⟩


omit [T2Space K] in
include hρ hn in
/-- The printed average with an arbitrary Haar measure is scaled by its
total mass. Probability normalization gives isometric coordinates. -/
theorem compactActionProjection_pettis_haar (μ : Measure K) [μ.IsHaarMeasure]
    (ω : PontryaginDual K) (u : E) :
    HasPositivePettisIntegral μ (fun g => twistedCircleAction ω.toMonoidHom ρ g u)
      (μ.real univ • (compactActionIsotype ρ ω).starProjection u) := by
  let A := twistedCircleAction ω.toMonoidHom ρ
  let U := compactActionIsotype ρ ω
  let v := U.starProjection u
  let η := compactActionHaarProbability (K := K)
  have hμ : μ = μ univ • η := by
    simpa only [η, compactActionHaarProbability, TopologicalSpace.PositiveCompacts.coe_top] using
      (Measure.haarMeasure_unique μ (⊤ : TopologicalSpace.PositiveCompacts K))
  have hP := (compactActionProjection_pettis ρ hρ hn η ω).1 u
  intro ℓ
  obtain ⟨hi, he⟩ := hP ℓ
  constructor
  · rw [hμ]
    exact hi.smul_measure (measure_ne_top μ _)
  · have hint : (∫ g, ℓ (A g u) ∂μ) = μ.real univ • ∫ g, ℓ (A g u) ∂η := by
      conv_lhs => rw [hμ]
      exact integral_smul_measure (fun g => ℓ (A g u)) _
    change ℓ (μ.real univ • v) = ∫ g, ℓ (A g u) ∂μ
    change ℓ v = ∫ g, ℓ (A g u) ∂η at he
    rw [hint, ← he, ContinuousLinearMap.map_smul_of_tower]

omit [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] [CompleteSpace E] in
/-- The closed span of differences can be formed on any dense linear range.
Thus the quotient of the completed space uses exactly the closed relations
from the original tests. -/
theorem compactActionCoinvariant_closure_of_dense {D : Type*} [AddCommGroup D] [Module ℂ D]
    [TopologicalSpace D] (J : D →L[ℂ] E) (hJ : DenseRange J) (ω : PontryaginDual K) :
    (Submodule.span ℂ (range fun p : K × D =>
      J p.2 - twistedCircleAction ω.toMonoidHom ρ p.1 (J p.2))).topologicalClosure =
      (actionDifferenceSpan (twistedCircleAction ω.toMonoidHom ρ)).topologicalClosure := by
  let A := twistedCircleAction ω.toMonoidHom ρ
  let T := Submodule.span ℂ (range fun p : K × D => J p.2 - A p.1 (J p.2))
  change T.topologicalClosure = (actionDifferenceSpan A).topologicalClosure
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, u⟩, rfl⟩
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(k, J u), rfl⟩)
  · apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, u⟩, rfl⟩
    change u - A k u ∈ T.topologicalClosure
    refine hJ.induction_on (p := fun x => x - A k x ∈ T.topologicalClosure) u
      ((Submodule.isClosed_topologicalClosure T).preimage (continuous_id.sub (A k).continuous)) ?_
    intro v
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(k, v), rfl⟩)

end CompactAction

section RestrictedAction

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  (m : G →* Multiplicative ℝ) (hm : Continuous m) (l r s : ℝ) (hs : 0 ≤ s)
  (K : Subgroup G) (V : Submodule ℂ (Lp ℂ 2 μ))

private abbrev ambientAction := hardySobolevMulTranslation μ m hm l r s hs

/-- On the kernel of the logarithmic modulus, the two amplitude factors
cancel and weighted translation preserves the norm. -/
theorem hardySobolevMulTranslation_norm_of_normOne (g : G) (hg : m g = 1) (u : Lp ℂ 2 μ) :
    ‖hardySobolevMulTranslation μ m hm l r s hs g u‖ = ‖u‖ := by
  let h := measurePreserving_mul_left μ g⁻¹
  have he : hardySobolevMulTranslation μ m hm l r s hs g u =
      Lp.compMeasurePreserving (g⁻¹ * ·) h u := by
    apply Lp.ext
    filter_upwards [hardySobolevMulTranslation_ae μ m hm l r s hs g u,
      Lp.coeFn_compMeasurePreserving u h] with q h₁ h₂
    have hq : m (g⁻¹ * q) = m q := by rw [map_mul, map_inv, hg, inv_one, one_mul]
    have hpos : 0 < hardySobolevAmplitude l r s (m q).toAdd := by
      unfold hardySobolevAmplitude hardySobolevWeight
      exact Real.sqrt_pos.mpr (mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _))
        (Real.rpow_pos_of_pos (by positivity) _))
    rw [h₁, h₂, hq, div_self hpos.ne', Complex.ofReal_one, one_mul]
    rfl
  rw [he, Lp.norm_compMeasurePreserving]

variable (hinv : ∀ k : K, MapsTo (ambientAction μ m hm l r s hs k.val) V V)

/-- Restriction of the weighted translations to an invariant closed subspace
and a subgroup of norm-one elements. -/
def hardySobolevRestrictedAction : K →* (V →L[ℂ] V) where
  toFun k := ((ambientAction μ m hm l r s hs k.val).comp V.subtypeL).codRestrict _
    (fun u => hinv k u.property)
  map_one' := by
    ext u : 1
    apply Subtype.ext
    exact hardySobolevMulTranslation_one μ m hm l r s hs u.val
  map_mul' g h := by
    ext u : 1
    apply Subtype.ext
    exact hardySobolevMulTranslation_mul μ m hm l r s hs g.val h.val u.val

theorem hardySobolevRestrictedAction_norm (hk : ∀ g : K, m g.val = 1) (g : K) (u : V) :
    ‖hardySobolevRestrictedAction μ m hm l r s hs K V hinv g u‖ = ‖u‖ :=
  hardySobolevMulTranslation_norm_of_normOne μ m hm l r s hs g.val (hk g) u.val

theorem hardySobolevRestrictedAction_continuous [R1Space G] [μ.InnerRegularCompactLTTop]
    [IsLocallyFiniteMeasure μ] :
    Continuous (fun p : K × V => hardySobolevRestrictedAction μ m hm l r s hs K V hinv p.1 p.2) := by
  have hc := continuous_hardySobolevMulTranslation μ m hm l r s hs
  have hp : Continuous (fun p : K × V => (p.1.val, p.2.val)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  exact (hc.comp hp).subtype_mk _

/-- The compact isotype decomposition applies to any closed invariant
weighted subspace. -/
theorem hardySobolevRestrictedAction_decomposition
    [R1Space G] [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ]
    [T2Space K] [CompactSpace K] [SecondCountableTopology K] [BorelSpace K] [CompleteSpace V]
    (hk : ∀ k : K, m k.val = 1) (ν : Measure K) [ν.IsHaarMeasure] [IsProbabilityMeasure ν] :
    HasCompactIsotypeDecomposition (hardySobolevRestrictedAction μ m hm l r s hs K V hinv) ν :=
  hasCompactIsotypeDecomposition _
    (hardySobolevRestrictedAction_continuous μ m hm l r s hs K V hinv)
    (hardySobolevRestrictedAction_norm μ m hm l r s hs K V hinv hk) ν

end RestrictedAction

end

end Masullo
