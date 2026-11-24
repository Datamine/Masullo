import SLocalThetaKernels
import SLocalZetaProduct
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Topology.Metrizable.Urysohn

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField

namespace Masullo

noncomputable section

/-- Complex-valued meromorphic representatives on the plane. -/
def meromorphicRepresentatives : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | Meromorphic f}
  zero_mem' := Meromorphic.const 0
  add_mem' hf hg := Meromorphic.add hf hg
  smul_mem' c _ hf := Meromorphic.const_smul hf c

/-- Two representatives define the same meromorphic function if their
difference is zero in every punctured germ, including at removable points. -/
def zeroMeromorphicGerms : Submodule ℂ meromorphicRepresentatives where
  carrier := {f | ∀ z : ℂ, (f : ℂ → ℂ) =ᶠ[𝓝[≠] z] 0}
  zero_mem' _ := EventuallyEq.rfl
  add_mem' hf hg z := by
    filter_upwards [hf z, hg z] with w hw hw'
    change (_ : ℂ) + _ = 0
    rw [show _ = (0 : ℂ) from hw, show _ = (0 : ℂ) from hw', add_zero]
  smul_mem' c f hf z := by
    filter_upwards [hf z] with w hw
    change c * (f : ℂ → ℂ) w = 0
    rw [show (f : ℂ → ℂ) w = 0 from hw, mul_zero]

/-- Meromorphic functions with their usual equality of punctured germs. -/
abbrev PlaneMeromorphicFunctions := meromorphicRepresentatives ⧸ zeroMeromorphicGerms

private theorem meromorphic_germs_zero_of_eqOn_right {g : ℂ → ℂ}
    (hg : Meromorphic g) (he : EqOn g 0 {z | 0 < z.re}) :
    ∀ z : ℂ, g =ᶠ[𝓝[≠] z] 0 := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h0 : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
  have hg₀ : g =ᶠ[𝓝[≠] (1 : ℂ)] 0 :=
    (eventually_mem_set.mpr (hopen.mem_nhds h0)).filter_mono nhdsWithin_le_nhds |>.mono he
  intro z
  apply meromorphicOrderAt_eq_top_iff.mp
  by_contra hz
  have ho := hg.meromorphicOn (s := (univ : Set ℂ))
  exact ho.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ z) (mem_univ 1) hz
    (meromorphicOrderAt_eq_top_iff.mpr hg₀)

/-- The identity theorem in the vector space of meromorphic functions. -/
theorem planeMeromorphicFunctions_mk_eq_of_eqOn_right
    (f g : meromorphicRepresentatives)
    (h : EqOn (f : ℂ → ℂ) (g : ℂ → ℂ) {z | 0 < z.re}) :
    zeroMeromorphicGerms.mkQ f = zeroMeromorphicGerms.mkQ g := by
  apply sub_eq_zero.mp
  rw [← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change ∀ z : ℂ, ((f : ℂ → ℂ) - (g : ℂ → ℂ)) =ᶠ[𝓝[≠] z] 0
  refine meromorphic_germs_zero_of_eqOn_right (Meromorphic.sub f.property g.property) ?_
  intro z hz
  exact sub_eq_zero.mpr (h hz)

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev K := SLocalThetaNormOne F S
private abbrev E := sLocalBruhatImage F S
private abbrev ArchUnits := (InfiniteAdeleRing F)ˣ

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]

private abbrev continuedZeta (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

/-- The continued Mellin transform on one unitary component, with its
values taken in the vector space of meromorphic functions. -/
def sLocalMeromorphicZetaComponent (ω : PontryaginDual (K F S)) :
    E F S →ₗ[ℂ] PlaneMeromorphicFunctions := by
  let Z : E F S →ₗ[ℂ] meromorphicRepresentatives := {
    toFun f := ⟨continuedZeta F S μ ω f, sLocalProductZetaContinued_meromorphic F S μ ω _ _ f⟩
    map_add' f g := by
      apply Subtype.ext
      funext z
      simp only [continuedZeta, sLocalProductZetaContinued, map_add]
      rfl
    map_smul' c f := by
      apply Subtype.ext
      funext z
      change continuedZeta F S μ ω (c • f) z = c • continuedZeta F S μ ω f z
      simp only [continuedZeta, sLocalProductZetaContinued, map_smul] }
  exact zeroMeromorphicGerms.mkQ.comp Z

/-- The full S-local zeta operator has one meromorphic function on each
unitary component of quasi-character space. -/
def sLocalMeromorphicZetaOperator :
    E F S →ₗ[ℂ] (PontryaginDual (K F S) → PlaneMeromorphicFunctions) :=
  LinearMap.pi fun ω => sLocalMeromorphicZetaComponent F S μ ω

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable [MeasurableSpace (ArchUnits F)] [BorelSpace (ArchUnits F)]
variable (ν : Measure (K F S)) [ν.IsHaarMeasure]

private abbrev productHaar :=
  sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)

variable (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μ) Measure.count
  (sLocalClassHaar F S ν))

include hν in
theorem sLocalContinuedZeta_eq_theta (ω : PontryaginDual (K F S)) (f : E F S)
    {z : ℂ} (hz : 0 < z.re) :
    continuedZeta F S μ ω f z = sLocalThetaZetaIntegral F S ν ω f z := by
  letI : (productHaar F S μ).IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  exact ((sLocalIdelicZeta_meromorphic_continuation F S μ ω f).2 hz).trans
    (sLocalIdelicZeta_integrable_eq_theta F S (productHaar F S μ) ν hν ω f z hz).2

/-- Any meromorphic representative agreeing with the original product Haar
integral determines the same component of the meromorphic Mellin transform. -/
theorem sLocalMeromorphicZetaComponent_eq_of_agrees
    (ω : PontryaginDual (K F S)) (f : E F S) (g : meromorphicRepresentatives)
    (hg : EqOn (g : ℂ → ℂ) (sLocalIdelicZetaIntegral F S (productHaar F S μ) ω f)
      {z | 0 < z.re}) :
    sLocalMeromorphicZetaComponent F S μ ω f = zeroMeromorphicGerms.mkQ g := by
  change zeroMeromorphicGerms.mkQ ⟨continuedZeta F S μ ω f,
    sLocalProductZetaContinued_meromorphic F S μ ω _ _ f⟩ = _
  apply planeMeromorphicFunctions_mk_eq_of_eqOn_right
  intro z hz
  exact ((sLocalIdelicZeta_meromorphic_continuation F S μ ω f).2 hz).trans (hg hz).symm

include hν in
/-- Lemma 5.1.2.2(2). The homogeneous theta kernel equals the kernel of
the restriction of the continued S-local zeta function to its character component. -/
theorem sLocalHomogeneousTheta_zero_iff_meromorphicZeta
    (ω : PontryaginDual (K F S)) (f : E F S) :
    (∀ q, sLocalHomogeneousTheta F S ν ω f.val q = 0) ↔
      sLocalMeromorphicZetaComponent F S μ ω f = 0 := by
  change _ ↔ Submodule.Quotient.mk (p := zeroMeromorphicGerms)
    (⟨continuedZeta F S μ ω f, sLocalProductZetaContinued_meromorphic F S μ ω _ _ f⟩ :
      meromorphicRepresentatives) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change _ ↔ ∀ z : ℂ, continuedZeta F S μ ω f =ᶠ[𝓝[≠] z] 0
  constructor
  · intro hf
    apply meromorphic_germs_zero_of_eqOn_right
      (sLocalProductZetaContinued_meromorphic F S μ ω _ _ f)
    intro z hz
    change continuedZeta F S μ ω f z = 0
    rw [sLocalContinuedZeta_eq_theta F S μ ν hν ω f hz,
      (sLocalThetaZeta_integrable_eq_radial F S ν ω f z hz).2]
    simp [sLocalRadialMellin, hf]
  · intro hf
    apply (sLocalHomogeneousTheta_zero_iff_verticalZeta F S ν ω f 1 zero_lt_one).2
    intro y
    let z := (1 : ℂ) + (y : ℂ) * Complex.I
    have hz : 0 < z.re := by simp [z]
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hzero : sLocalThetaZetaIntegral F S ν ω f =ᶠ[𝓝[≠] z] 0 := by
      filter_upwards [(eventually_mem_set.mpr (hopen.mem_nhds hz)).filter_mono nhdsWithin_le_nhds,
        hf z] with w hw he
      exact (sLocalContinuedZeta_eq_theta F S μ ν hν ω f hw).symm.trans he
    have hC : ContinuousAt (sLocalThetaZetaIntegral F S ν ω f) z :=
      (sLocalThetaZeta_analytic F S ν ω f z hz).continuousAt
    exact tendsto_nhds_unique (hC.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hzero.symm)

variable [ν.WeaklyRegular]

include hν in
/-- Lemma 5.1.2.2(1). The kernel of the full continued S-local Mellin
transform is the kernel of the ordinary S-local theta operator. -/
theorem sLocalMeromorphicZetaOperator_ker_of_weil :
    (sLocalMeromorphicZetaOperator F S μ).ker = (sLocalThetaOperator F S).ker := by
  ext f
  simp only [LinearMap.mem_ker]
  rw [sLocalTheta_zero_iff_homogeneous_zero F S ν f]
  rw [funext_iff]
  exact forall_congr' fun ω =>
    (sLocalHomogeneousTheta_zero_iff_meromorphicZeta F S μ ν hν ω f).symm
/-- The ordinary theta kernel is independent of the choice of local Haar
measures used to form the product zeta integral. -/
theorem sLocalMeromorphicZetaOperator_ker :
    (sLocalMeromorphicZetaOperator F S μ).ker = (sLocalThetaOperator F S).ker := by
  letI : (productHaar F S μ).IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  obtain ⟨ν, hν, hw⟩ := sLocalClassHaar_exists_weil F S (productHaar F S μ)
  letI : ν.IsHaarMeasure := hν
  letI : SecondCountableTopology ((SAdeles F S)ˣ) := sLocalIdeles_secondCountable F S
  letI : SecondCountableTopology (SIdeleQuotient F S) :=
    QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.secondCountableTopology
      QuotientGroup.isOpenQuotientMap_mk.isOpenMap
  letI : T1Space (SIdeleQuotient F S) := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
  letI : SecondCountableTopology (K F S) := IsInducing.subtypeVal.secondCountableTopology
  letI : CompactSpace (K F S) := sLocalThetaNormOne_compact F S
  letI : ν.WeaklyRegular :=
    (Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν).weaklyRegular
  exact sLocalMeromorphicZetaOperator_ker_of_weil F S μ ν hw

/-- The full meromorphic zeta operator descends to the actual theta quotient. -/
def sLocalQuotientMeromorphicZeta :
    SLocalThetaQuotient F S →ₗ[ℂ] (PontryaginDual (K F S) → PlaneMeromorphicFunctions) :=
  Submodule.liftQ _ (sLocalMeromorphicZetaOperator F S μ)
    (sLocalMeromorphicZetaOperator_ker F S μ).ge

theorem sLocalQuotientMeromorphicZeta_injective :
    Injective (sLocalQuotientMeromorphicZeta F S μ) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  exact (sLocalMeromorphicZetaOperator_ker F S μ).le


end

end Masullo
