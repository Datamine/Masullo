import BruhatDistributionSupport
import BruhatCompactMultipliers
import SchwartzLocalUnits
import BruhatSchwartzTranslation
import BruhatSchwartzStructure
import CompactGroupAveraging
import Mathlib.MeasureTheory.Measure.Haar.Unique

open Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 1500000

/-- The support defined by annihilation of all tests in a neighborhood. -/
abbrev distributionSupport {X V : Type*} [TopologicalSpace X]
    (test : V → X → ℂ) (T : V → ℂ) : Set X :=
  (distributionVanishingLocus test T)ᶜ

private theorem exists_test_of_mem_distributionSupport {X V : Type*} [TopologicalSpace X]
    (test : V → X → ℂ) (T : V → ℂ) {x : X} (hx : x ∈ distributionSupport test T)
    {O : Set X} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ f : V, tsupport (test f) ⊆ O ∧ T f ≠ 0 := by
  by_contra! he
  exact hx ⟨O, hO, hxO, he⟩

private theorem tsupport_fourfold_product {X Y Z A : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace A]
    {f : X → ℂ} {g : Y → ℂ} {h : Z → ℂ} {k : A → ℂ}
    {s : X × Y × Z × A → ℂ}
    (hs : ∀ x, s x = f x.1 * g x.2.1 * h x.2.2.1 * k x.2.2.2) :
    tsupport s ⊆ tsupport f ×ˢ (tsupport g ×ˢ (tsupport h ×ˢ tsupport k)) := by
  apply closure_minimal _
    ((isClosed_tsupport f).prod ((isClosed_tsupport g).prod
      ((isClosed_tsupport h).prod (isClosed_tsupport k))))
  intro x hx
  have hn : f x.1 * g x.2.1 * h x.2.2.1 * k x.2.2.2 ≠ 0 := hs x ▸ hx
  obtain ⟨h3, h4⟩ := mul_ne_zero_iff.mp hn
  obtain ⟨h2, h3⟩ := mul_ne_zero_iff.mp h3
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h2
  exact ⟨subset_tsupport _ h1, subset_tsupport _ h2, subset_tsupport _ h3, subset_tsupport _ h4⟩

/-- The inclusion from right to left in (D.1.8.4) follows from the pairings
on pure tensor tests. The hypotheses describe their actual pointwise products. -/
theorem distributionSupport_fourfold_product_subset
    {X Y Z A V₁ V₂ V₃ V₄ V : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace A]
    (t₁ : V₁ → X → ℂ) (t₂ : V₂ → Y → ℂ) (t₃ : V₃ → Z → ℂ) (t₄ : V₄ → A → ℂ)
    (t : V → X × Y × Z × A → ℂ)
    (d₁ : V₁ → ℂ) (d₂ : V₂ → ℂ) (d₃ : V₃ → ℂ) (d₄ : V₄ → ℂ) (d : V → ℂ)
    (hpair : ∀ (f₁ : V₁) (f₂ : V₂) (f₃ : V₃) (f₄ : V₄),
      ∃ f : V, (∀ x, t f x = t₁ f₁ x.1 * t₂ f₂ x.2.1 * t₃ f₃ x.2.2.1 * t₄ f₄ x.2.2.2) ∧
        d f = d₁ f₁ * d₂ f₂ * d₃ f₃ * d₄ f₄) :
    distributionSupport t₁ d₁ ×ˢ (distributionSupport t₂ d₂ ×ˢ
      (distributionSupport t₃ d₃ ×ˢ distributionSupport t₄ d₄)) ⊆ distributionSupport t d := by
  rintro x ⟨h1, h2, h3, h4⟩ ⟨O, hO, hxO, hzero⟩
  obtain ⟨U₁, hU₁, V, hV, hUV⟩ := mem_nhds_prod_iff.mp (hO.mem_nhds hxO)
  obtain ⟨U₂, hU₂, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hV
  obtain ⟨U₃, hU₃, U₄, hU₄, hWU⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨V₁', hs₁, ho₁, hx₁⟩ := mem_nhds_iff.mp hU₁
  obtain ⟨V₂', hs₂, ho₂, hx₂⟩ := mem_nhds_iff.mp hU₂
  obtain ⟨V₃', hs₃, ho₃, hx₃⟩ := mem_nhds_iff.mp hU₃
  obtain ⟨V₄', hs₄, ho₄, hx₄⟩ := mem_nhds_iff.mp hU₄
  obtain ⟨f₁, ht₁, hz₁⟩ := exists_test_of_mem_distributionSupport t₁ d₁ h1 ho₁ hx₁
  obtain ⟨f₂, ht₂, hz₂⟩ := exists_test_of_mem_distributionSupport t₂ d₂ h2 ho₂ hx₂
  obtain ⟨f₃, ht₃, hz₃⟩ := exists_test_of_mem_distributionSupport t₃ d₃ h3 ho₃ hx₃
  obtain ⟨f₄, ht₄, hz₄⟩ := exists_test_of_mem_distributionSupport t₄ d₄ h4 ho₄ hx₄
  obtain ⟨f, hf, hd⟩ := hpair f₁ f₂ f₃ f₄
  have hsub : tsupport (t f) ⊆ O :=
    (tsupport_fourfold_product hf).trans fun y hy ↦
      hUV ⟨hs₁ (ht₁ hy.1), hVW ⟨hs₂ (ht₂ hy.2.1),
        hWU ⟨hs₃ (ht₃ hy.2.2.1), hs₄ (ht₄ hy.2.2.2)⟩⟩⟩
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hz₁ hz₂) hz₃) hz₄) (hd ▸ hzero f hsub)

section BruhatProducts

open Filter

variable {G H I J : Type*}
  [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
  [CommGroup I] [TopologicalSpace I] [IsTopologicalGroup I] [T2Space I] [LocallyCompactSpace I]
  [CommGroup J] [TopologicalSpace J] [IsTopologicalGroup J] [T2Space J] [LocallyCompactSpace J]

local notation "S" => BruhatSchwartz
local notation "X" => G × H × I × J
/-- The support of a functional on the full Schwartz–Bruhat space. -/
abbrev bruhatDistributionSupport {Y : Type*} [CommGroup Y] [TopologicalSpace Y]
    [IsTopologicalGroup Y] [T2Space Y] [LocallyCompactSpace Y] (d : S Y →L[ℂ] ℂ) : Set Y :=
  distributionSupport (fun f : S Y ↦ f.val) d

/-- The localization argument for D.1.8.3. Once pure tensors separate
continuous functionals on compactly supported tests, their pairings determine the
support. Local multipliers are constructed in the full Schwartz–Bruhat topology. -/
theorem bruhatDistribution_tensor_support_of_separation
    (d₁ : S G →L[ℂ] ℂ) (d₂ : S H →L[ℂ] ℂ) (d₃ : S I →L[ℂ] ℂ) (d₄ : S J →L[ℂ] ℂ)
    (d : S X →L[ℂ] ℂ) (b : S G → S H → S I → S J → S X)
    (hb : ∀ f g s t (x : X),
      (b f g s t).val x = f.val x.1 * g.val x.2.1 * s.val x.2.2.1 * t.val x.2.2.2)
    (hd : ∀ f g s t, d (b f g s t) = d₁ f * d₂ g * d₃ s * d₄ t)
    (hsep : ∀ L : S X →L[ℂ] ℂ, (∀ f g s t, L (b f g s t) = 0) →
      ∀ v, HasCompactSupport v.val → L v = 0) :
    bruhatDistributionSupport d = bruhatDistributionSupport d₁ ×ˢ
      (bruhatDistributionSupport d₂ ×ˢ (bruhatDistributionSupport d₃ ×ˢ bruhatDistributionSupport d₄)) := by
  have hlocal {x : X} {U₁ : Set G} {U₂ : Set H} {U₃ : Set I} {U₄ : Set J}
      (ho₁ : IsOpen U₁) (ho₂ : IsOpen U₂) (ho₃ : IsOpen U₃) (ho₄ : IsOpen U₄)
      (hmem : x ∈ U₁ ×ˢ (U₂ ×ˢ (U₃ ×ˢ U₄)))
      (hkill : ∀ f g s t, tsupport f.val ⊆ U₁ → tsupport g.val ⊆ U₂ →
        tsupport s.val ⊆ U₃ → tsupport t.val ⊆ U₄ → d (b f g s t) = 0) :
      x ∈ distributionVanishingLocus (fun f : S X ↦ f.val) d := by
    obtain ⟨u₁, hc₁, hs₁, hu₁, _⟩ := exists_bruhatSchwartz_local_unit ho₁ hmem.1
    obtain ⟨u₂, hc₂, hs₂, hu₂, _⟩ := exists_bruhatSchwartz_local_unit ho₂ hmem.2.1
    obtain ⟨u₃, hc₃, hs₃, hu₃, _⟩ := exists_bruhatSchwartz_local_unit ho₃ hmem.2.2.1
    obtain ⟨u₄, hc₄, hs₄, hu₄, _⟩ := exists_bruhatSchwartz_local_unit ho₄ hmem.2.2.2
    let u := b u₁ u₂ u₃ u₄
    have hcu : HasCompactSupport u.val :=
      (hc₁.prod (hc₂.prod (hc₃.prod hc₄))).of_isClosed_subset isClosed_closure
        (tsupport_fourfold_product (hb u₁ u₂ u₃ u₄))
    let M := bruhatSchwartz_compactMultiplier u hcu
    let M₁ := bruhatSchwartz_compactMultiplier u₁ hc₁
    let M₂ := bruhatSchwartz_compactMultiplier u₂ hc₂
    let M₃ := bruhatSchwartz_compactMultiplier u₃ hc₃
    let M₄ := bruhatSchwartz_compactMultiplier u₄ hc₄
    have hcompat (f : S G) (g : S H) (s : S I) (t : S J) :
        M (b f g s t) = b (M₁ f) (M₂ g) (M₃ s) (M₄ t) := by
      apply Subtype.ext
      funext y
      change _ = (b (M₁ f) (M₂ g) (M₃ s) (M₄ t)).val y
      rw [hb]
      simp only [M, M₁, M₂, M₃, M₄, bruhatSchwartz_compactMultiplier_apply, u, hb]
      ring
    have hzero (f : S X) (hf : HasCompactSupport f.val) : d (M f) = 0 := hsep (d.comp M) (fun f g s t ↦ by
      change d (M (b f g s t)) = 0
      rw [hcompat]
      exact hkill _ _ _ _
        (tsupport_mul_subset_left.trans hs₁) (tsupport_mul_subset_left.trans hs₂)
        (tsupport_mul_subset_left.trans hs₃) (tsupport_mul_subset_left.trans hs₄)) f hf
    have hu : u.val =ᶠ[𝓝 x] fun _ ↦ 1 := by
      filter_upwards [continuous_fst.continuousAt.eventually hu₁,
        (continuous_fst.comp continuous_snd).continuousAt.eventually hu₂,
        (continuous_fst.comp (continuous_snd.comp continuous_snd)).continuousAt.eventually hu₃,
        (continuous_snd.comp (continuous_snd.comp continuous_snd)).continuousAt.eventually hu₄]
        with y h₁ h₂ h₃ h₄
      change u₁.val y.1 = 1 at h₁
      change u₂.val y.2.1 = 1 at h₂
      change u₃.val y.2.2.1 = 1 at h₃
      change u₄.val y.2.2.2 = 1 at h₄
      simp only [u, hb, h₁, h₂, h₃, h₄, mul_one]
    obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp hu
    refine ⟨W, hWo, hxW, fun f hf ↦ ?_⟩
    have he : M f = f := by
      apply Subtype.ext
      funext y
      change u.val y * f.val y = f.val y
      by_cases hy : y ∈ tsupport f.val
      · rw [show u.val y = 1 from hW (hf hy), one_mul]
      · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    have hc : HasCompactSupport f.val := hcu.of_isClosed_subset isClosed_closure
      (hf.trans fun y hy ↦ subset_tsupport _ (show u.val y ≠ 0 by
        rw [show u.val y = 1 from hW hy]; exact one_ne_zero))
    exact he ▸ hzero f hc
  apply Subset.antisymm ?_ (distributionSupport_fourfold_product_subset _ _ _ _ _
    _ _ _ _ _ (fun f g s t ↦ ⟨b f g s t, hb f g s t, hd f g s t⟩))
  intro x hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨O, hO, hxO, hvan⟩
    exact hx (hlocal hO isOpen_univ isOpen_univ isOpen_univ ⟨hxO, trivial, trivial, trivial⟩
      (fun f g s t h _ _ _ ↦ by rw [hd, hvan f h]; simp))
  · rintro ⟨O, hO, hxO, hvan⟩
    exact hx (hlocal isOpen_univ hO isOpen_univ isOpen_univ ⟨trivial, hxO, trivial, trivial⟩
      (fun f g s t _ h _ _ ↦ by rw [hd, hvan g h]; simp))
  · rintro ⟨O, hO, hxO, hvan⟩
    exact hx (hlocal isOpen_univ isOpen_univ hO isOpen_univ ⟨trivial, trivial, hxO, trivial⟩
      (fun f g s t _ _ h _ ↦ by rw [hd, hvan s h]; simp))
  · rintro ⟨O, hO, hxO, hvan⟩
    exact hx (hlocal isOpen_univ isOpen_univ isOpen_univ hO ⟨trivial, trivial, trivial, hxO⟩
      (fun f g s t _ _ _ h ↦ by rw [hd, hvan t h]; simp))

section Convolution

open Function MeasureTheory

variable {Y : Type*} [CommGroup Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
  [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- Convolution with a compact test, expressed as a Pettis integral of translations
in the full Schwartz–Bruhat topology. -/
private theorem exists_bruhatSchwartz_convolution (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]
    (f k : S Y) (hf : HasCompactSupport f.val) :
    ∃ u : S Y, HasPositivePettisIntegral μ
      (fun x ↦ f.val x • bruhatSchwartz_translate x k) u := by
  letI : UniformSpace (S Y) := bruhatSchwartzUniformSpace
  letI : IsUniformAddGroup (S Y) := isUniformAddGroup_of_addCommGroup
  letI : T2Space (S Y) := bruhatSchwartz_t2
  let W := PolynormableSpace.withSeminorms ℂ (S Y)
  letI : ContinuousSMul ℂ (S Y) := W.continuousSMul
  letI : LocallyConvexSpace ℝ (S Y) := W.toLocallyConvexSpace
  letI : QuasiCompleteSpace ℂ (S Y) := bruhatSchwartz_quasiComplete
  apply exists_positivePettisIntegral_of_hasCompactSupport μ
  · exact (bruhatSchwartz_continuous f).smul
      (continuous_bruhatSchwartz_translate.comp (continuous_id.prodMk continuous_const))
  · exact hf.of_isClosed_subset isClosed_closure (closure_mono fun x hx hfx ↦
      hx (show f.val x • bruhatSchwartz_translate x k = 0 by rw [hfx, zero_smul]))

omit [SecondCountableTopology Y] in
/-- Commutativity of the convolution follows from Haar inversion and translation. -/
private theorem bruhatSchwartz_convolution_comm (μ : Measure Y)
    [μ.IsMulLeftInvariant] [μ.IsInvInvariant] {f k u v : S Y}
    (hu : HasPositivePettisIntegral μ (fun x ↦ f.val x • bruhatSchwartz_translate x k) u)
    (hv : HasPositivePettisIntegral μ (fun x ↦ k.val x • bruhatSchwartz_translate x f) v) :
    u = v := by
  apply Subtype.ext
  funext y
  let ev : S Y →L[ℂ] ℂ :=
    ⟨{ toFun := fun a ↦ a.val y, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl },
      bruhatSchwartz_continuous_eval y⟩
  change ev u = ev v
  rw [(hu ev).2, (hv ev).2]
  simp only [map_smul, smul_eq_mul]
  change (∫ x, f.val x * (bruhatSchwartz_translate x k).val y ∂μ) =
    ∫ x, k.val x * (bruhatSchwartz_translate x f).val y ∂μ
  simp only [bruhatSchwartz_translate_apply]
  rw [← integral_div_left_eq_self (fun x ↦ k.val x * f.val (x⁻¹ * y)) μ y]
  congr 1
  funext x
  have h : (y / x)⁻¹ * y = x := by simp [div_eq_mul_inv, mul_assoc]
  rw [h, mul_comm x⁻¹ y, ← div_eq_mul_inv, mul_comm]

end Convolution

section Separation

open Function MeasureTheory

variable [SecondCountableTopology G] [SecondCountableTopology H]
  [SecondCountableTopology I] [SecondCountableTopology J]

/-- Pure product tests determine continuous functionals on compact tests.
A nonnegative product local unit of small support gives a convolution
average of translates arbitrarily close to the original functional value. -/
theorem bruhatSchwartz_pure_products_separate_compact
    (b : S G → S H → S I → S J → S X)
    (hb : ∀ f g s t (x : X),
      (b f g s t).val x = f.val x.1 * g.val x.2.1 * s.val x.2.2.1 * t.val x.2.2.2)
    (L : S X →L[ℂ] ℂ) (hL : ∀ f g s t, L (b f g s t) = 0)
    (f : S X) (hf : HasCompactSupport f.val) : L f = 0 := by
  by_contra hne
  let ε := ‖L f‖ / 2
  have hnorm : 0 < ‖L f‖ := norm_pos_iff.mpr hne
  have hε : 0 < ε := by dsimp [ε]; positivity
  have ht : bruhatSchwartz_translate (1 : X) f = f := by
    apply Subtype.ext
    funext x
    simp
  let A (x : X) := L (bruhatSchwartz_translate x f)
  have hA : Continuous A := L.continuous.comp
    (continuous_bruhatSchwartz_translate.comp (continuous_id.prodMk continuous_const))
  have hN : {x | ‖L f - A x‖ < ε} ∈ 𝓝 (1 : X) :=
    (isOpen_lt (continuous_const.sub hA).norm continuous_const).mem_nhds (by
      change ‖L f - L (bruhatSchwartz_translate (1 : X) f)‖ < ε
      simpa only [ht, sub_self, norm_zero] using hε)
  obtain ⟨U₁, hU₁, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hN
  obtain ⟨U₂, hU₂, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hV
  obtain ⟨U₃, hU₃, U₄, hU₄, hWU⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨V₁, hs₁, ho₁, hx₁⟩ := mem_nhds_iff.mp hU₁
  obtain ⟨V₂, hs₂, ho₂, hx₂⟩ := mem_nhds_iff.mp hU₂
  obtain ⟨V₃, hs₃, ho₃, hx₃⟩ := mem_nhds_iff.mp hU₃
  obtain ⟨V₄, hs₄, ho₄, hx₄⟩ := mem_nhds_iff.mp hU₄
  obtain ⟨u₁, hc₁, ht₁, he₁, hp₁⟩ := exists_bruhatSchwartz_local_unit ho₁ hx₁
  obtain ⟨u₂, hc₂, ht₂, he₂, hp₂⟩ := exists_bruhatSchwartz_local_unit ho₂ hx₂
  obtain ⟨u₃, hc₃, ht₃, he₃, hp₃⟩ := exists_bruhatSchwartz_local_unit ho₃ hx₃
  obtain ⟨u₄, hc₄, ht₄, he₄, hp₄⟩ := exists_bruhatSchwartz_local_unit ho₄ hx₄
  let k := b u₁ u₂ u₃ u₄
  have hsub := tsupport_fourfold_product (hb u₁ u₂ u₃ u₄)
  have hk : HasCompactSupport k.val :=
    (hc₁.prod (hc₂.prod (hc₃.prod hc₄))).of_isClosed_subset isClosed_closure hsub
  have hk1 : k.val (1 : X) = 1 := by
    change (b u₁ u₂ u₃ u₄).val (1, 1, 1, 1) = 1
    rw [hb, he₁.eq_of_nhds, he₂.eq_of_nhds, he₃.eq_of_nhds, he₄.eq_of_nhds]
    simp
  have hkr (x : X) : ((k.val x).re : ℂ) = k.val x ∧ 0 ≤ (k.val x).re := by
    have he (z : ℂ) (hz : z.im = 0) : (z.re : ℂ) = z := by
      apply Complex.ext <;> simp [hz]
    change (((b u₁ u₂ u₃ u₄).val x).re : ℂ) = (b u₁ u₂ u₃ u₄).val x ∧
      0 ≤ ((b u₁ u₂ u₃ u₄).val x).re
    rw [hb, ← he _ (hp₁ x.1).2, ← he _ (hp₂ x.2.1).2,
      ← he _ (hp₃ x.2.2.1).2, ← he _ (hp₄ x.2.2.2).2]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re, true_and]
    exact mul_nonneg (mul_nonneg (mul_nonneg (hp₁ _).1 (hp₂ _).1) (hp₃ _).1) (hp₄ _).1
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  let μ : Measure X := Measure.haar
  obtain ⟨u, hu⟩ := exists_bruhatSchwartz_convolution μ f k hf
  obtain ⟨v, hv⟩ := exists_bruhatSchwartz_convolution μ k f hk
  have hzero (x : X) : L (bruhatSchwartz_translate x k) = 0 := by
    have he : bruhatSchwartz_translate x k =
        b (bruhatSchwartz_translate x.1 u₁) (bruhatSchwartz_translate x.2.1 u₂)
          (bruhatSchwartz_translate x.2.2.1 u₃) (bruhatSchwartz_translate x.2.2.2 u₄) := by
      apply Subtype.ext
      funext y
      simp only [bruhatSchwartz_translate_apply, k, hb]
      rfl
    rw [he, hL]
  have hu0 : L u = 0 := by
    rw [(hu L).2]
    simp [hzero]
  have hv0 : (∫ x, k.val x * A x ∂μ) = 0 := by
    calc
      _ = L v := by simpa [A, Function.comp_apply, smul_eq_mul] using (hv L).2.symm
      _ = 0 := bruhatSchwartz_convolution_comm μ hu hv ▸ hu0
  have hkri : Integrable (fun x ↦ (k.val x).re) μ :=
    (Complex.continuous_re.comp (bruhatSchwartz_continuous k)).integrable_of_hasCompactSupport
      (hk.comp_left Complex.zero_re)
  let m := ∫ x, (k.val x).re ∂μ
  have hm : 0 < m := integral_pos_of_integrable_nonneg_nonzero
    (Complex.continuous_re.comp (bruhatSchwartz_continuous k)) hkri
    (fun x ↦ (hkr x).2) (x := (1 : X)) (by simp [hk1])
  have hki : Integrable k.val μ :=
    (bruhatSchwartz_continuous k).integrable_of_hasCompactSupport hk
  have hInt : (∫ x, k.val x ∂μ) = (m : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (ae_of_all _ fun x ↦ (hkr x).1.symm)
  have hdiff : (∫ x, k.val x * (L f - A x) ∂μ) = (m : ℂ) * L f := by
    simp_rw [mul_sub]
    have hI : Integrable (fun x ↦ k.val x * A x) μ := by
      simpa only [A, Function.comp_def, map_smul, smul_eq_mul] using (hv L).1
    rw [integral_sub (hki.mul_const _) hI, hv0, sub_zero, integral_mul_const, hInt]
  have hbound : ‖(m : ℂ) * L f‖ ≤ m * ε := by
    rw [← hdiff, ← integral_mul_const]
    apply norm_integral_le_of_norm_le (hkri.mul_const ε)
    apply ae_of_all
    intro x
    rw [norm_mul, ← (hkr x).1, Complex.norm_real, Real.norm_of_nonneg (hkr x).2]
    by_cases hx : x ∈ tsupport k.val
    · have hs := hsub hx
      exact mul_le_mul_of_nonneg_left
        (le_of_lt (show ‖L f - A x‖ < ε from hUV
          ⟨hs₁ (ht₁ hs.1), hVW ⟨hs₂ (ht₂ hs.2.1),
            hWU ⟨hs₃ (ht₃ hs.2.2.1), hs₄ (ht₄ hs.2.2.2)⟩⟩⟩)) (hkr x).2
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hm.le] at hbound
  have hle := le_of_mul_le_mul_left hbound hm
  dsimp [ε] at hle
  linarith

/-- Proposition D.1.8.3. The pure-test pairings defining a tensor distribution
determine its support as the product of the supports of its four factors. -/
theorem bruhatDistribution_tensor_support
    (d₁ : S G →L[ℂ] ℂ) (d₂ : S H →L[ℂ] ℂ) (d₃ : S I →L[ℂ] ℂ) (d₄ : S J →L[ℂ] ℂ)
    (d : S X →L[ℂ] ℂ)
    (hpair : ∀ (f : S G) (g : S H) (s : S I) (t : S J),
      ∃ u : S X, (∀ x, u.val x = f.val x.1 * g.val x.2.1 * s.val x.2.2.1 * t.val x.2.2.2) ∧
        d u = d₁ f * d₂ g * d₃ s * d₄ t) :
    bruhatDistributionSupport d = bruhatDistributionSupport d₁ ×ˢ
      (bruhatDistributionSupport d₂ ×ˢ (bruhatDistributionSupport d₃ ×ˢ bruhatDistributionSupport d₄)) := by
  choose b hb using hpair
  exact bruhatDistribution_tensor_support_of_separation d₁ d₂ d₃ d₄ d b
    (fun f g s t ↦ (hb f g s t).1) (fun f g s t ↦ (hb f g s t).2)
    (bruhatSchwartz_pure_products_separate_compact b (fun f g s t ↦ (hb f g s t).1))

end Separation

end BruhatProducts

end

end Masullo
