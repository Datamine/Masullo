import BruhatFractionalTraces
import FractionalCutoffRows

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

section Transport

variable {A B C D E F : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup C] [NormedSpace ℂ C] [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem map_submodule_eq_of_mem (e : A ≃L[ℂ] B)
    (L : Submodule ℂ A) (Q : Submodule ℂ B) (h : ∀ x, x ∈ L ↔ e x ∈ Q) :
    L.map e.toLinearMap = Q := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  change (∃ z : A, z ∈ L ∧ e z = e x) ↔ e x ∈ Q
  constructor
  · rintro ⟨z, hz, he⟩
    exact he ▸ (h z).mp hz
  · intro hx
    exact ⟨x, (h x).mpr hx, rfl⟩

private theorem closure_range_equiv {I : Type*} (e : A ≃L[ℂ] B)
    (f : I → A) (S : Set A) (T : Set B)
    (hf : closure (range f) = S) (h : ∀ x, x ∈ S ↔ e x ∈ T) :
    closure (range (e ∘ f)) = T := by
  have hc : closure (e '' range f) = e '' closure (range f) :=
    (e.toHomeomorph.image_closure (range f)).symm
  rw [range_comp, hc, hf]
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  constructor
  · rintro ⟨z, hz, he⟩
    exact he ▸ (h z).mp hz
  · intro hx
    exact ⟨x, (h x).mpr hx, rfl⟩

end Transport

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
  (ν : Measure m.toMonoidHom.ker) [IsFiniteMeasure ν]

local notation "K" => m.toMonoidHom.ker
local notation "H" => modulatedLogMeasure m τ hτ ν
local notation "W[" a "," b "," s "]" => hardySobolevMeasure H (modulatedLog m) a b s
local notation "E[" I "]" => ModulatedExponentialInductive m I
local notation "dx" => (volume : Measure ℝ)

/-- Mellin transformation of the original weighted Haar space, expressed
as the compatible pair of fractional endpoint traces. A half-line uses
the repeated finite endpoint and its one-sided support constraint. -/
def fractionalGroupIntervalMellinEquiv {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    Lp ℂ 2 W[a,b,s] ≃L[ℂ] fractionalIntervalEndpointSpace ν hab s :=
  (bruhatCompactIntervalGroupProductEquiv m τ hτ ν hab s).toContinuousLinearEquiv.trans
    (fractionalIntervalEndpointEquiv ν hab s)

/-- Analytic cutoff by support of the inverse Fourier coordinate. Testing
the first endpoint suffices because the two endpoint coordinates are compatible. -/
def fractionalIntervalAnalyticCutoff {a b : ℝ} (hab : a ≤ b) (s : ℝ) (U : Set ℝ) :
    Submodule ℂ (fractionalIntervalEndpointSpace ν hab s) :=
  (fractionalMellinSupportedSpace ν s U).comap
    ((LinearMap.fst ℂ (FractionalMellinTensor ν s) (FractionalMellinTensor ν s)).comp
      (fractionalIntervalEndpointSpace ν hab s).subtype)

private theorem fractionalGroupIntervalMellin_support {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (U : Set ℝ) (f : Lp ℂ 2 W[a,b,s]) :
    fractionalGroupIntervalMellinEquiv m τ hτ ν hab s f ∈ fractionalIntervalAnalyticCutoff m ν hab s U ↔
      ∀ᵐ g ∂W[a,b,s], modulatedLog m g ∉ U → f g = 0 := by
  let e := intervalGroupChart m τ hτ
  let Q : FractionalMellinTensor ν s ≃ₗᵢ[ℂ] Lp ℂ 2 (ν.prod (stripMeasure 0 0 s)) :=
    completedLpTwoTensorEquiv
  let u := bruhatCompactIntervalGroupProductEquiv m τ hτ ν hab s f
  let v := Q (fractionalIntervalTrace ν hab s (left_mem_Icc.mpr hab) u)
  have hmp : MeasurePreserving e (ν.prod (stripMeasure a b s)) W[a,b,s] := by
    rw [← modulatedInterval_weightedHaar_split m τ hτ ν hab]
    exact intervalGroupChart_preserving m τ hτ ν (stripMeasure a b s)
  have hBase (c d : ℝ) : ν.prod dx ≪ ν.prod (stripMeasure c d s) :=
    Measure.AbsolutelyContinuous.rfl.prod (absolutelyContinuous_amplitudeMeasure dx _
      (stripSobolevAmplitude_continuous c d s).measurable (stripSobolevAmplitude_pos c d s))
  have hStrip (c d : ℝ) : ν.prod (stripMeasure c d s) ≪ ν.prod dx :=
    Measure.AbsolutelyContinuous.rfl.prod (amplitudeMeasure_absolutelyContinuous dx _)
  have hv : (v : K × ℝ → ℂ) =ᵐ[ν.prod dx] fun p => Real.exp (a * p.2) • f (e p) := by
    filter_upwards [fractionalIntervalTrace_coordinates_ae ν hab s (left_mem_Icc.mpr hab) u,
      (hBase a b).ae_le (bruhatCompactIntervalGroupProductEquiv_ae m τ hτ ν hab s f)] with p h₁ h₂
    exact h₁.trans (congrArg (Real.exp (a * p.2) • ·) h₂)
  change (∀ᵐ p ∂ν.prod (stripMeasure 0 0 s), p.2 ∉ U → v p = 0) ↔ _
  constructor
  · intro h
    have hQ : ∀ᵐ p ∂ν.prod (stripMeasure a b s), modulatedLog m (e p) ∉ U → f (e p) = 0 := by
      apply (hStrip a b).ae_le
      filter_upwards [(hBase 0 0).ae_le h, hv] with p hp hv hU
      have hm : modulatedLog m (e p) = p.2 := intervalGroupChart_log m τ hτ p
      have hz := hp (hm ▸ hU)
      rw [hv] at hz
      exact (smul_eq_zero.mp hz).resolve_left (Real.exp_pos _).ne'
    filter_upwards [(hmp.symm e.toMeasurableEquiv).quasiMeasurePreserving.ae hQ] with g hg
    change modulatedLog m (e (e.symm g)) ∉ U → f (e (e.symm g)) = 0 at hg
    exact e.apply_symm_apply g ▸ hg
  · intro h
    apply (hStrip 0 0).ae_le
    filter_upwards [(hBase a b).ae_le (hmp.quasiMeasurePreserving.ae h), hv] with p hp hv hU
    have hm : modulatedLog m (e p) = p.2 := intervalGroupChart_log m τ hτ p
    change modulatedLog m (e p) ∉ U → f (e p) = 0 at hp
    exact hv.trans (by rw [hp (hm.symm ▸ hU), smul_zero])


private theorem support_iff_indicator {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (U : Set X) (f : X → ℂ) :
    (∀ᵐ x ∂μ, x ∉ U → f x = 0) ↔ f =ᵐ[μ] U.indicator f := by
  constructor
  · intro h
    filter_upwards [h] with x hx
    by_cases hn : x ∈ U
    · exact (indicator_of_mem hn _).symm
    · rw [indicator_of_notMem hn]
      exact hx hn
  · intro h
    filter_upwards [h] with x hx hn
    exact hx.trans (indicator_of_notMem hn _)

private theorem fractionalGroupIntervalMellin_mapsCutoff {a b : ℝ} (hab : a ≤ b)
    (s : ℝ) (U : Set ℝ) (L : Submodule ℂ (Lp ℂ 2 W[a,b,s]))
    (hL : (L : Set (Lp ℂ 2 W[a,b,s])) =
      {f : Lp ℂ 2 W[a,b,s] | (f : G → ℂ) =ᵐ[W[a,b,s]] (modulatedLog m ⁻¹' U).indicator (f : G → ℂ)}) :
    L.map (fractionalGroupIntervalMellinEquiv m τ hτ ν hab s).toLinearMap =
      fractionalIntervalAnalyticCutoff m ν hab s U := by
  apply map_submodule_eq_of_mem
  intro f
  have hf : f ∈ L ↔ (f : G → ℂ) =ᵐ[W[a,b,s]]
      (modulatedLog m ⁻¹' U).indicator (f : G → ℂ) := Set.ext_iff.mp hL f
  exact hf.trans ((support_iff_indicator (modulatedLog m ⁻¹' U) (f : G → ℂ)).symm.trans
    (fractionalGroupIntervalMellin_support m τ hτ ν hab s U f).symm)

set_option maxHeartbeats 1200000 in
/-- The fractional Paley–Wiener cutoff diagram. The vertical maps are
the actual Mellin equivalence restricted to the three cutoff subspaces.
Use the full ray for a compact base and the admissible support ray for
a half-line base. The analytic quotient retains the upper support cutoff. -/
theorem fractionalGroupInterval_cutoffDiagram {a b : ℝ} (hab : a ≤ b) (s c : ℝ)
    (hc : c ≤ 0) (R : Set ℝ) (hR : MeasurableSet R) :
    let E := Lp ℂ 2 W[a,b,s]
    let F := fractionalGroupIntervalMellinEquiv m τ hτ ν hab s
    let S := fun (U : Set ℝ) => {f : E |
      (f : G → ℂ) =ᵐ[W[a,b,s]] (modulatedLog m ⁻¹' (U ∩ R)).indicator (f : G → ℂ)}
    let T := fun (U : Set ℝ) => fractionalIntervalAnalyticCutoff m ν hab s (U ∩ R)
    ∃ (L M Q : Submodule ℂ E)
      (D : FractionalCutoffRows L M Q (T (Icc c 0)) (T (Ici c)) (T (Ici 0))),
      (L : Set E) = S (Icc c 0) ∧ (M : Set E) = S (Ici c) ∧ (Q : Set E) = S (Ici 0) ∧
      (∀ x, (D.physicalInclusion x).val = x.val) ∧
      (∀ x, ((D.physicalProjection x).val : G → ℂ) =ᵐ[W[a,b,s]]
        (modulatedLog m ⁻¹' (Ici 0 ∩ R)).indicator (x.val : G → ℂ)) ∧
      (∀ x, (D.leftMellin x).val = F x.val) ∧ (∀ x, (D.middleMellin x).val = F x.val) ∧
      (∀ x, (D.rightMellin x).val = F x.val) := by
  intro E F S T
  let P (y x : E) : Prop :=
    (y : G → ℂ) =ᵐ[W[a,b,s]] (modulatedLog m ⁻¹' (Ici 0 ∩ R)).indicator (x : G → ℂ)
  exact assemble_fractionalCutoffRows F S T (Icc c 0) (Ici c) (Ici 0) P
    (fun U X hX => fractionalGroupIntervalMellin_mapsCutoff m τ hτ ν hab s (U ∩ R) X hX)
    (bruhatInterval_physicalExact_relative m τ hτ ν hab s c hc R hR)

/-- The vertical map in the interval diagram takes the endpoint traces of
the original Schwartz–Bruhat function. -/
theorem fractionalGroupIntervalMellin_onTest {I : Set ℝ} {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ) (f : E[I]) :
    (fractionalGroupIntervalMellinEquiv m τ hτ ν hab s
      (bruhatCompactIntervalGroupInclusion m τ hτ ν ha hb hab s f)).val =
    (fractionalMellinTensor ν a s (bruhatIntervalEndpointInclusion m τ hτ ν ⟨a, ha⟩ s f),
     fractionalMellinTensor ν b s (bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, hb⟩ s f)) := by
  let J := bruhatCompactIntervalGroupProductEquiv m τ hτ ν hab s
  let u := bruhatCompactIntervalInclusion m τ hτ ν ha hb hab s f
  have hu : J (bruhatCompactIntervalGroupInclusion m τ hτ ν ha hb hab s f) = u :=
    J.apply_symm_apply u
  change (fractionalIntervalEndpointEquiv ν hab s
    (J (bruhatCompactIntervalGroupInclusion m τ hτ ν ha hb hab s f))).val = _
  rw [hu]
  exact Prod.ext
    (bruhatFractionalIntervalTrace_onTest m τ hτ ν ha hb hab (left_mem_Icc.mpr hab) ha s f)
    (bruhatFractionalIntervalTrace_onTest m τ hτ ν ha hb hab (right_mem_Icc.mpr hab) hb s f)

private theorem fractionalGroupInterval_cutoffClosure_of_physical {A : Type*}
    {a b : ℝ} (hab : a ≤ b) (s : ℝ) (U : Set ℝ) (f : A → Lp ℂ 2 W[a,b,s])
    (hf : closure (range f) = {u | ∀ᵐ g ∂W[a,b,s], modulatedLog m g ∉ U → u g = 0}) :
    closure (range (fractionalGroupIntervalMellinEquiv m τ hτ ν hab s ∘ f)) =
      (fractionalIntervalAnalyticCutoff m ν hab s U : Set _) := by
  exact closure_range_equiv (fractionalGroupIntervalMellinEquiv m τ hτ ν hab s) f
    _ _ hf (fun u => (fractionalGroupIntervalMellin_support m τ hτ ν hab s U u).symm)

set_option maxHeartbeats 650000 in
/-- The compact-base analytic cutoff is the closure of the original Mellin
transforms of strict-support tests. The finite endpoint traces used here
agree with the integrals on the original tests. -/
theorem fractionalGroupCompact_cutoffClosure [ν.WeaklyRegular] (hm : IsProperMap m)
    {I : Set ℝ} {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (s : ℝ)
    {U : Set ℝ} (hU : IsOpen U) :
    closure (range (fun f : bruhatIntervalCutoffTests m I U =>
      fractionalGroupIntervalMellinEquiv m τ hτ ν hab s
        (bruhatCompactIntervalGroupInclusion m τ hτ ν ha hb hab s f.val))) =
    (fractionalIntervalAnalyticCutoff m ν hab s U : Set _) :=
  fractionalGroupInterval_cutoffClosure_of_physical m τ hτ ν hab s U _
    (bruhatCompactIntervalGroupCutoff_closure m τ hτ ν hm ha hb hab s hU)

set_option maxHeartbeats 650000 in
/-- The right-half-line analytic cutoff is the closure of the original
finite-norm transforms with the additional strict cutoff. -/
theorem fractionalGroupRightHalfLine_cutoffClosure [ν.WeaklyRegular] (hm : IsProperMap m)
    {I : Set ℝ} {a : ℝ} (ha : a ∈ I) (s : ℝ) {U : Set ℝ} (hU : IsOpen U) :
    closure (range (fun f : bruhatIntervalCutoffTests m I (U ∩ Iic 0) =>
      fractionalGroupIntervalMellinEquiv m τ hτ ν (a := a) le_rfl s
        (bruhatCompactIntervalGroupInclusion m τ hτ ν ha ha le_rfl s f.val))) =
    (fractionalIntervalAnalyticCutoff m ν (a := a) le_rfl s (U ∩ Iic 0) : Set _) :=
  fractionalGroupInterval_cutoffClosure_of_physical m τ hτ ν le_rfl s (U ∩ Iic 0) _
    (bruhatRightHalfLine_cutoff_closure m τ hτ ν hm ha s hU)

set_option maxHeartbeats 650000 in
/-- The left-half-line analytic cutoff is the closure of the original
finite-norm transforms with the additional strict cutoff. -/
theorem fractionalGroupLeftHalfLine_cutoffClosure [ν.WeaklyRegular] (hm : IsProperMap m)
    {I : Set ℝ} {a : ℝ} (ha : a ∈ I) (s : ℝ) {U : Set ℝ} (hU : IsOpen U) :
    closure (range (fun f : bruhatIntervalCutoffTests m I (U ∩ Ici 0) =>
      fractionalGroupIntervalMellinEquiv m τ hτ ν (a := a) le_rfl s
        (bruhatCompactIntervalGroupInclusion m τ hτ ν ha ha le_rfl s f.val))) =
    (fractionalIntervalAnalyticCutoff m ν (a := a) le_rfl s (U ∩ Ici 0) : Set _) :=
  fractionalGroupInterval_cutoffClosure_of_physical m τ hτ ν le_rfl s (U ∩ Ici 0) _
    (bruhatLeftHalfLine_cutoff_closure m τ hτ ν hm ha s hU)


/-- On the whole-real-line base, the transformed finite-norm Bruhat tests
have the zero completion. Every supported completion in its cutoff row
is therefore zero as well. -/
theorem fractionalGroupWholeLine_traceClosure_zero [ν.IsOpenPosMeasure]
    {I : Set ℝ} (t : I) (s : ℝ) :
    let T := {f : E[I] //
      hardySobolevIntervalENorm H (modulatedLog m) univ s f.val ≠ ⊤}
    closure (range (fun f : T =>
      fractionalMellinTensor ν t s (bruhatIntervalEndpointInclusion m τ hτ ν t s f.val))) =
      ({0} : Set (FractionalMellinTensor ν s)) := by
  intro T
  let M := (fractionalMellinTensor ν t s).toLinearIsometry.toContinuousLinearMap.comp
    (bruhatIntervalEndpointInclusion m τ hτ ν t s)
  have hf (f : T) : f.val = 0 :=
    (bruhatWholeLine_finite_iff m τ hτ ν t.property s f.val).mp f.property
  let z : T := ⟨0, (bruhatWholeLine_finite_iff m τ hτ ν t.property s (0 : E[I])).mpr rfl⟩
  have hRange : range (fun f : T => M f.val) = ({0} : Set (FractionalMellinTensor ν s)) := by
    ext y
    constructor
    · rintro ⟨f, rfl⟩
      exact mem_singleton_iff.mpr ((congrArg (fun x : E[I] => M x) (hf f)).trans M.map_zero)
    · rintro (rfl : y = 0)
      exact ⟨z, M.map_zero⟩
  change closure (range (fun f : T => M f.val)) = _
  rw [hRange, closure_singleton]

end
end Masullo
