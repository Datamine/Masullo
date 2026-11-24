import ScalarFractionalInterval
import FractionalCutoffRows
import HardySobolevCompactTests

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

local notation "dx" => (volume : Measure ℝ)

private theorem scalar_strip_to_volume (a b s : ℝ) : stripMeasure a b s ≪ dx :=
  amplitudeMeasure_absolutelyContinuous dx _

private theorem scalar_volume_to_strip (a b s : ℝ) : dx ≪ stripMeasure a b s :=
  absolutelyContinuous_amplitudeMeasure dx _
    (stripSobolevAmplitude_continuous a b s).measurable (stripSobolevAmplitude_pos a b s)

/-- The interval trace has its cutoff read from the inverse Fourier
coordinate of its first endpoint. -/
def scalarFractionalCutoff {a b : ℝ} (hab : a ≤ b) (s : ℝ) (U : Set ℝ) :
    Submodule ℂ (scalarFractionalInterval a b hab s) where
  carrier := {u | ∀ᵐ x ∂dx, x ∉ U → u.val.1 x = 0}
  zero_mem' := by
    have h : ((0 : MellinFrequencySobolev s) : ℝ → ℂ) =ᵐ[dx] (0 : ℝ → ℂ) :=
      (scalar_volume_to_strip 0 0 s).ae_le (Lp.coeFn_zero ℂ 2 (stripMeasure 0 0 s))
    exact h.mono fun _ hx _ => hx
  add_mem' {u v} hu hv := by
    change ∀ᵐ x ∂dx, x ∉ U → (u.val.1 + v.val.1) x = 0
    have he := (scalar_volume_to_strip 0 0 s).ae_le (Lp.coeFn_add u.val.1 v.val.1)
    filter_upwards [hu, hv, he] with x hx hy hz hn
    exact hz.trans (by change u.val.1 x + v.val.1 x = 0; rw [hx hn, hy hn, add_zero])
  smul_mem' z u hu := by
    change ∀ᵐ x ∂dx, x ∉ U → (z • u.val.1) x = 0
    have he := (scalar_volume_to_strip 0 0 s).ae_le (Lp.coeFn_smul z u.val.1)
    filter_upwards [hu, he] with x hx hz hn
    exact hz.trans (by change z • u.val.1 x = 0; rw [hx hn, smul_zero])

theorem scalarFractionalCutoff_mem_iff {a b : ℝ} (hab : a ≤ b) (s : ℝ) (U : Set ℝ)
    (f : StripSobolev a b s) :
    scalarFractionalIntervalEquiv hab s f ∈ scalarFractionalCutoff hab s U ↔
      ∀ᵐ x ∂dx, x ∉ U → f x = 0 := by
  change (∀ᵐ x ∂dx, x ∉ U → scalarFractionalTrace hab (left_mem_Icc.mpr hab) s f x = 0) ↔ _
  have he := scalarFractionalTrace_ae hab (left_mem_Icc.mpr hab) s f
  constructor
  · intro hf
    filter_upwards [hf, he] with x hx he hn
    exact (smul_eq_zero.mp (he.symm.trans (hx hn))).resolve_left (Real.exp_pos _).ne'
  · intro hf
    filter_upwards [hf, he] with x hx he hn
    exact he.trans (by rw [hx hn, smul_zero])

private theorem scalarFractionalCutoff_map {a b : ℝ} (hab : a ≤ b) (s : ℝ) (U : Set ℝ)
    (L : Submodule ℂ (StripSobolev a b s))
    (hL : (L : Set (StripSobolev a b s)) =
      {f : StripSobolev a b s | (f : ℝ → ℂ) =ᵐ[stripMeasure a b s] U.indicator (f : ℝ → ℂ)}) :
    L.map (scalarFractionalIntervalEquiv hab s).toLinearMap = scalarFractionalCutoff hab s U := by
  let M := scalarFractionalIntervalEquiv hab s
  have hiff (f : StripSobolev a b s) : f ∈ L ↔ M f ∈ scalarFractionalCutoff hab s U := by
    rw [scalarFractionalCutoff_mem_iff]
    change f ∈ (L : Set (StripSobolev a b s)) ↔ _
    rw [hL]
    constructor
    · intro h
      filter_upwards [(scalar_volume_to_strip a b s).ae_le h] with x hx hn
      exact hx.trans (indicator_of_notMem hn _)
    · intro h
      apply (scalar_strip_to_volume a b s).ae_le
      filter_upwards [h] with x hx
      by_cases hm : x ∈ U
      · exact (indicator_of_mem hm _).symm
      · rw [indicator_of_notMem hm]
        exact hx hm
  ext u
  obtain ⟨f, rfl⟩ := M.surjective u
  change (∃ g : StripSobolev a b s, g ∈ L ∧ M g = M f) ↔ M f ∈ scalarFractionalCutoff hab s U
  constructor
  · rintro ⟨g, hg, he⟩
    exact he ▸ (hiff g).mp hg
  · intro hf
    exact ⟨f, (hiff f).mpr hf, rfl⟩

set_option maxHeartbeats 750000 in
/-- The scalar short exact cutoff diagram in fractional Mellin coordinates.
Take `R = univ` for a compact base, and at the repeated finite endpoint
use the admissible radial support for either half-line. -/
theorem scalarFractional_cutoffDiagram {a b : ℝ} (hab : a ≤ b) (s c : ℝ) (hc : c ≤ 0)
    (R : Set ℝ) (hR : MeasurableSet R) :
    let E := StripSobolev a b s
    let F := scalarFractionalIntervalEquiv hab s
    let S := fun U : Set ℝ => {f : E |
      (f : ℝ → ℂ) =ᵐ[stripMeasure a b s] (U ∩ R).indicator (f : ℝ → ℂ)}
    let T := fun U => scalarFractionalCutoff hab s (U ∩ R)
    ∃ (L M Q : Submodule ℂ E)
      (D : FractionalCutoffRows L M Q (T (Icc c 0)) (T (Ici c)) (T (Ici 0))),
      (L : Set E) = S (Icc c 0) ∧ (M : Set E) = S (Ici c) ∧ (Q : Set E) = S (Ici 0) ∧
      (∀ x, (D.physicalInclusion x).val = x.val) ∧
      (∀ x, ((D.physicalProjection x).val : ℝ → ℂ) =ᵐ[stripMeasure a b s]
        (Ici 0 ∩ R).indicator (x.val : ℝ → ℂ)) ∧
      (∀ x, (D.leftMellin x).val = F x.val) ∧ (∀ x, (D.middleMellin x).val = F x.val) ∧
      (∀ x, (D.rightMellin x).val = F x.val) := by
  intro E F S T
  let P (y x : E) : Prop :=
    (y : ℝ → ℂ) =ᵐ[stripMeasure a b s] (Ici 0 ∩ R).indicator (x : ℝ → ℂ)
  have hn : ∀ᵐ x : ℝ ∂stripMeasure a b s, x ≠ 0 := (scalar_strip_to_volume a b s).ae_le ((dx).ae_ne 0)
  exact assemble_fractionalCutoffRows F S T (Icc c 0) (Ici c) (Ici 0) P
    (fun U L hL => scalarFractionalCutoff_map hab s (U ∩ R) L hL)
    (lpTwo_cutoff_exact_relative (stripMeasure a b s) id measurable_id c hc hn R hR)


/-- The original scalar tests with strict topological support generate the
weighted cutoff for an arbitrary decay set containing the finite endpoints. -/
theorem scalarStrip_cutoffTestClosure_of_ae (J : Set ℝ) (a b : J) (s : ℝ)
    {U V : Set ℝ} (hV : IsOpen V) (hVU : V ⊆ U) (hUV : ∀ᵐ x ∂dx, x ∈ U ↔ x ∈ V) :
    closure {u | ∃ f : PositiveRealExponentialDecay J, tsupport f.val ⊆ U ∧
      stripSobolevTest J a b s f = u} =
        (supportedSobolevCompletion a b s V : Set (StripSobolev a b s)) := by
  let S := supportedSobolevCompletion a b s V
  have hs : IsClosed (S : Set (StripSobolev a b s)) := by
    rw [supportedSobolevCompletion_eq_closure_of_compactTests a b s hV]
    exact isClosed_closure
  apply le_antisymm
  · apply closure_minimal _ hs
    rintro _ ⟨f, hf, rfl⟩
    apply (mem_supportedSobolevCompletion_iff a b s hV _).mpr
    filter_upwards [(scalar_volume_to_strip a b s).ae_le (stripSobolevTest_ae J a b s f), hUV]
      with x hx he h
    exact hx.trans (image_eq_zero_of_notMem_tsupport (fun ht => h (he.mp (hf ht))))
  · rw [supportedSobolevCompletion_eq_closure_of_compactTests a b s hV]
    apply closure_mono
    rintro _ ⟨f, hC, hS, rfl⟩
    let g : PositiveRealExponentialDecay J := ⟨f.val,
      mem_logExponentialDecaySubmodule_of_hasCompactSupport J hC
        (smooth_exponentialProfile univ ⟨0, mem_univ _⟩ f)⟩
    refine ⟨g, hS.trans hVU, Lp.ext ?_⟩
    exact (stripSobolevTest_ae J a b s g).trans
      (stripSobolevTest_ae univ ⟨a, mem_univ _⟩ ⟨b, mem_univ _⟩ s f).symm

/-- The closure of the original scalar Mellin traces with strict support is
the corresponding analytic subspace. -/
theorem scalarFractional_cutoffTestClosure_of_ae (J : Set ℝ) (a b : J) (hab : (a : ℝ) ≤ b) (s : ℝ)
    {U V : Set ℝ} (hV : IsOpen V) (hVU : V ⊆ U) (hUV : ∀ᵐ x ∂dx, x ∈ U ↔ x ∈ V) :
    closure {z | ∃ f : PositiveRealExponentialDecay J, tsupport f.val ⊆ U ∧
      scalarFractionalIntervalEquiv hab s (stripSobolevTest J a b s f) = z} =
        (scalarFractionalCutoff hab s U : Set (scalarFractionalInterval a b hab s)) := by
  let F := scalarFractionalIntervalEquiv hab s
  let S : Set (StripSobolev a b s) := {u | ∃ f : PositiveRealExponentialDecay J,
    tsupport f.val ⊆ U ∧ stripSobolevTest J a b s f = u}
  have hS : closure S = (supportedSobolevCompletion a b s V : Set (StripSobolev a b s)) :=
    scalarStrip_cutoffTestClosure_of_ae J a b s hV hVU hUV
  have he : {z | ∃ f : PositiveRealExponentialDecay J, tsupport f.val ⊆ U ∧
      F (stripSobolevTest J a b s f) = z} = F '' S := by
    ext z
    constructor
    · rintro ⟨f, hU, rfl⟩
      exact ⟨_, ⟨f, hU, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, rfl⟩
  have hF : closure (F '' S) = F '' closure S := (F.toHomeomorph.image_closure S).symm
  change closure {z | ∃ f : PositiveRealExponentialDecay J, tsupport f.val ⊆ U ∧
      F (stripSobolevTest J a b s f) = z} = _
  rw [he, hF, hS]
  ext z
  obtain ⟨u, rfl⟩ := F.surjective z
  have hSupport : (∀ᵐ x ∂dx, x ∉ U → u x = 0) ↔ (∀ᵐ x ∂dx, x ∉ V → u x = 0) :=
    eventually_congr (hUV.mono fun x hx => by simp only [hx])
  constructor
  · rintro ⟨v, hv, he⟩
    exact (scalarFractionalCutoff_mem_iff hab s U u).mpr (hSupport.mpr
      ((mem_supportedSobolevCompletion_iff a b s hV u).mp (F.injective he ▸ hv)))
  · intro h
    exact ⟨u, (mem_supportedSobolevCompletion_iff a b s hV u).mpr
      (hSupport.mp ((scalarFractionalCutoff_mem_iff hab s U u).mp h)), rfl⟩

theorem scalarFractional_cutoffTestClosure (J : Set ℝ) (a b : J) (hab : (a : ℝ) ≤ b) (s : ℝ)
    {U : Set ℝ} (hU : IsOpen U) :
    closure {z | ∃ f : PositiveRealExponentialDecay J, tsupport f.val ⊆ U ∧
      scalarFractionalIntervalEquiv hab s (stripSobolevTest J a b s f) = z} =
        (scalarFractionalCutoff hab s U : Set (scalarFractionalInterval a b hab s)) :=
  scalarFractional_cutoffTestClosure_of_ae J a b hab s hU subset_rfl (.of_forall fun _ => Iff.rfl)

/-- Physical closure of the strict lower-ray tests, realized by the
closed-ray indicator. -/
theorem scalarStrip_lowerCutoff (J : Set ℝ) (a b : J) (s c : ℝ) :
    ∃ P : StripSobolev a b s →L[ℂ] StripSobolev a b s,
      IsStarProjection P ∧ P.IsPositive ∧
      (∀ u, (P u : ℝ → ℂ) =ᵐ[dx] (Ici c).indicator (u : ℝ → ℂ)) ∧
      closure {u | ∃ f : PositiveRealExponentialDecay J, tsupport f.val ⊆ Ioi c ∧
        stripSobolevTest J a b s f = u} = range P := by
  obtain ⟨P, hP, hpos, hr, hae⟩ := supportedSobolev_lowerCutoff_eq_projection a b s c
  exact ⟨P, hP, hpos, hae, (scalarStrip_cutoffTestClosure_of_ae J a b s isOpen_Ioi subset_rfl (.of_forall fun _ => Iff.rfl)).trans hr.symm⟩


/-- The lower cutoff inside a half-line finite-norm model. The tests may
have topological support touching the zero fibre of the admissible ray. -/
theorem scalarFractional_lowerCutoff_relative (J : Set ℝ) (b : J) (s c : ℝ)
    {R V : Set ℝ} (hV : IsOpen V) (hVR : V ⊆ R) (hRV : ∀ᵐ x ∂dx, x ∈ R ↔ x ∈ V) :
    (∃ P : StripSobolev b b s →L[ℂ] StripSobolev b b s,
      IsStarProjection P ∧ P.IsPositive ∧
      (∀ u, (P u : ℝ → ℂ) =ᵐ[dx] (Ici c ∩ R).indicator (u : ℝ → ℂ)) ∧
      closure {u | ∃ f : PositiveRealExponentialDecay J, tsupport f.val ⊆ Ioi c ∩ R ∧
        stripSobolevTest J b b s f = u} = range P) ∧
    closure {z | ∃ f : PositiveRealExponentialDecay J, tsupport f.val ⊆ Ioi c ∩ R ∧
      scalarFractionalIntervalEquiv le_rfl s (stripSobolevTest J b b s f) = z} =
        (scalarFractionalCutoff (a := (b : ℝ)) le_rfl s (Ioi c ∩ R) :
          Set (scalarFractionalInterval b b le_rfl s)) := by
  have hOpen : IsOpen (Ioi c ∩ V) := isOpen_Ioi.inter hV
  have hsub : Ioi c ∩ V ⊆ Ioi c ∩ R := inter_subset_inter_right _ hVR
  have hUV : ∀ᵐ x ∂dx, x ∈ Ioi c ∩ R ↔ x ∈ Ioi c ∩ V :=
    hRV.mono fun x hx => by simp only [mem_inter_iff, hx]
  refine ⟨?_, scalarFractional_cutoffTestClosure_of_ae J b b le_rfl s hOpen hsub hUV⟩
  obtain ⟨P, hP, hpos, _, hr, hPae⟩ := supportedSobolevCompletion_eq_cutoff b b s hOpen
  refine ⟨P, hP, hpos, fun u => ?_, (scalarStrip_cutoffTestClosure_of_ae J b b s hOpen hsub hUV).trans hr.symm⟩
  refine (hPae u).trans ?_
  filter_upwards [hUV, (dx).ae_ne c] with x hx hxc
  have hm : c < x ↔ c ≤ x := ⟨le_of_lt, fun h => lt_of_le_of_ne h hxc.symm⟩
  have he : x ∈ Ioi c ∩ V ↔ x ∈ Ici c ∩ R := by
    rw [← hx]
    simp only [mem_inter_iff, mem_Ioi, mem_Ici, hm]
  by_cases hn : x ∈ Ioi c ∩ V
  · rw [indicator_of_mem hn, indicator_of_mem (he.mp hn)]
  · rw [indicator_of_notMem hn, indicator_of_notMem (fun h => hn (he.mpr h))]

theorem scalarFractional_halfLineRays :
    (∀ᵐ x ∂dx, x ∈ Iic (0 : ℝ) ↔ x ∈ Iio 0) ∧
      (∀ᵐ x ∂dx, x ∈ Ici (0 : ℝ) ↔ x ∈ Ioi 0) := by
  constructor
  · filter_upwards [(dx).ae_ne (0 : ℝ)] with x hx
    change x ≤ 0 ↔ x < 0
    exact ⟨fun h => lt_of_le_of_ne h hx, le_of_lt⟩
  · filter_upwards [(dx).ae_ne (0 : ℝ)] with x hx
    change 0 ≤ x ↔ 0 < x
    exact ⟨fun h => lt_of_le_of_ne h hx.symm, le_of_lt⟩

/-- On the two half-lines, finite norm on an original test is equivalent
to its topological support lying in the appropriate closed logarithmic ray. -/
theorem scalarFractional_halfLineTestSupport (J : Set ℝ) (b : J)
    (s : ℝ) (f : PositiveRealExponentialDecay J) :
    (hardySobolevIntervalENorm dx id (Ici (b : ℝ)) s f.val ≠ ⊤ ↔ tsupport f.val ⊆ Iic 0) ∧
    (hardySobolevIntervalENorm dx id (Iic (b : ℝ)) s f.val ≠ ⊤ ↔ tsupport f.val ⊆ Ici 0) := by
  constructor
  · rw [scalarHardySobolev_Ici_finite_iff]
    refine ⟨fun h => closure_minimal (fun x hx => ?_) isClosed_Iic, fun h x hx =>
      image_eq_zero_of_notMem_tsupport (fun hs => (not_le_of_gt hx) (h hs))⟩
    exact le_of_not_gt (fun ht => hx (h x ht))
  · rw [scalarHardySobolev_Iic_finite_iff]
    refine ⟨fun h => closure_minimal (fun x hx => ?_) isClosed_Ici, fun h x hx =>
      image_eq_zero_of_notMem_tsupport (fun hs => (not_le_of_gt hx) (h hs))⟩
    exact le_of_not_gt (fun ht => hx (h x ht))


/-- The supported scalar physical and analytic completions are equivalent. -/
def scalarFractional_supportedEquiv {a b : ℝ} (hab : a ≤ b) (s : ℝ) {U : Set ℝ}
    (hU : IsOpen U) :
    supportedSobolevCompletion a b s U ≃L[ℂ] scalarFractionalCutoff hab s U := by
  let M := scalarFractionalIntervalEquiv hab s
  let S := supportedSobolevCompletion a b s U
  let T := scalarFractionalCutoff hab s U
  refine M.ofSubmodules S T ?_
  ext u
  obtain ⟨f, rfl⟩ := M.surjective u
  have hiff (g : StripSobolev a b s) : g ∈ S ↔ M g ∈ T :=
    (mem_supportedSobolevCompletion_iff a b s hU g).trans
      (scalarFractionalCutoff_mem_iff hab s U g).symm
  change (∃ g : StripSobolev a b s, g ∈ S ∧ M g = M f) ↔ M f ∈ T
  exact ⟨fun ⟨g, hg, he⟩ => he ▸ (hiff g).mp hg, fun h => ⟨f, (hiff f).mpr h, rfl⟩⟩

/-- On the upper logarithmic ray, the quotient carries the finite upper
endpoint norm and is the supported boundary space of the left half-plane. -/
def scalarFractional_upperCutoffEquiv {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    scalarFractionalCutoff hab s (Ioi 0) ≃L[ℂ]
      scalarFractionalCutoff (a := b) le_rfl s (Ioi 0) :=
  (scalarFractional_supportedEquiv hab s isOpen_Ioi).symm.trans
    ((supportedSobolev_upperEndpointEquiv a b s).toContinuousLinearEquiv.trans
      (scalarFractional_supportedEquiv le_rfl s isOpen_Ioi))

theorem scalarFractional_upperTrace_onSupport {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (f : supportedSobolevCompletion a b s (Ioi 0)) :
    scalarFractionalTrace hab (right_mem_Icc.mpr hab) s f.val =
      fractionalMellinLine b s (supportedSobolev_upperEndpointEquiv a b s f).val := by
  apply Lp.ext
  apply (scalar_strip_to_volume 0 0 s).ae_le
  filter_upwards [scalarFractionalTrace_ae hab (right_mem_Icc.mpr hab) s f.val,
    fractionalMellinLine_ae b s (supportedSobolev_upperEndpointEquiv a b s f).val,
    supportedSobolev_upperEndpointEquiv_ae a b s f] with x h₁ h₂ h₃
  exact h₁.trans ((congrArg (Real.exp (b * x) • ·) h₃).symm.trans h₂.symm)

theorem scalarFractional_upperCutoff_open_eq_closed {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    scalarFractionalCutoff hab s (Ioi 0) = scalarFractionalCutoff hab s (Ici 0) := by
  ext u
  change (∀ᵐ x ∂dx, x ∉ Ioi 0 → u.val.1 x = 0) ↔
    (∀ᵐ x ∂dx, x ∉ Ici 0 → u.val.1 x = 0)
  exact eventually_congr (scalarFractional_halfLineRays.2.mono fun x hx => by simp only [hx])

/-- The left term has the entire Paley–Wiener growth characterization,
with the interval factor continuous through real part zero. -/
theorem scalarFractional_band_iff {a b s c : ℝ} (hab : a ≤ b) (hs : 0 ≤ s) (hc : c ≤ 0)
    (u : supportedSobolevCompletion a b s (Ioi c)) :
    scalarFractionalIntervalEquiv hab s u.val ∈ scalarFractionalCutoff hab s (Icc c 0) ↔
      ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
        (∀ z : ℂ, z.re < b → F z = cutoffMellinIntegral u.val 0 z) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ z : ℂ, ‖F z‖ ≤ C * Real.sqrt (∫ x in Icc c 0, Real.exp (2 * z.re * x)) := by
  rw [scalarFractionalCutoff_mem_iff, ← cutoffMellinIntegral_paleyWiener_iff hc hs,
    mem_supportedSobolevCompletion_iff a b s isOpen_Ioo]
  apply eventually_congr
  filter_upwards [(dx).ae_ne c, (dx).ae_ne (0 : ℝ)] with x h₁ h₂
  have he : x ∈ Icc c 0 ↔ x ∈ Ioo c 0 :=
    ⟨fun h => ⟨lt_of_le_of_ne h.1 h₁.symm, lt_of_le_of_ne h.2 h₂⟩, fun h => Ioo_subset_Icc_self h⟩
  simp only [he]

/-- There is no nonzero upper-cutoff term on a right-half-line base. -/
theorem scalarFractional_rightHalfLine_quotient_zero (b s : ℝ) :
    scalarFractionalCutoff (a := b) le_rfl s (Ici 0 ∩ Iic 0) = ⊥ := by
  let M := scalarFractionalIntervalEquiv (a := b) le_rfl s
  apply eq_bot_iff.mpr
  intro z hz
  obtain ⟨f, rfl⟩ := M.surjective z
  have h := (scalarFractionalCutoff_mem_iff le_rfl s (Ici 0 ∩ Iic 0) f).mp hz
  have hf : (f : ℝ → ℂ) =ᵐ[dx] (0 : ℝ → ℂ) := by
    filter_upwards [h, (dx).ae_ne (0 : ℝ)] with x hx hn
    exact hx (fun hs => hn (le_antisymm hs.2 hs.1))
  have hz₀ : f = 0 := by
    apply Lp.ext
    filter_upwards [(scalar_strip_to_volume b b s).ae_le hf,
      Lp.coeFn_zero ℂ 2 (stripMeasure b b s)] with x hx h₀
    exact hx.trans h₀.symm
  have hm : M f = 0 := (congrArg (fun f : StripSobolev b b s => M f) hz₀).trans M.map_zero
  exact hm.symm ▸ Submodule.zero_mem _

/-- The whole-line scalar finite-norm test completion is zero. -/
theorem scalarFractional_wholeLine_closure_zero (J : Set ℝ) (b : J) (s : ℝ) :
    closure {u | ∃ f : PositiveRealExponentialDecay J,
      hardySobolevIntervalENorm dx id univ s f.val ≠ ⊤ ∧
        scalarFractionalIntervalEquiv le_rfl s (stripSobolevTest J b b s f) = u} =
      ({0} : Set (scalarFractionalInterval b b le_rfl s)) := by
  have h : {u | ∃ f : PositiveRealExponentialDecay J,
      hardySobolevIntervalENorm dx id univ s f.val ≠ ⊤ ∧
        scalarFractionalIntervalEquiv le_rfl s (stripSobolevTest J b b s f) = u} =
      ({0} : Set (scalarFractionalInterval b b le_rfl s)) := by
    ext u
    constructor
    · rintro ⟨f, hf, rfl⟩
      have he := (scalarHardySobolev_univ_finite_iff s J b f).mp hf
      simp [he]
    · rintro (rfl : u = 0)
      refine ⟨0, (scalarHardySobolev_univ_finite_iff s J b 0).mpr rfl, ?_⟩
      simp
  rw [h, closure_singleton]

end
end Masullo
