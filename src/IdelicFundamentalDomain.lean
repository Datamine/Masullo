import ArchimedeanFundamentalDomain

open Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField SchwartzMap nonZeroDivisors

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

abbrev NormOneIdeles := (ideleNorm F).ker
private abbrev FiniteUnits := (FiniteAdeleRing (𝓞 F) F)ˣ
abbrev IntegralFiniteUnits := (finiteIntegralSubmonoid F).units

private def normOneIntegralBlock : Set (NormOneIdeles F) :=
  (Subtype.val : NormOneIdeles F → Idele F) ⁻¹' (ideleDivisor F).ker

private theorem normOneIntegralBlock_open : IsOpen (normOneIntegralBlock F) :=
  (ideleDivisor_ker_open F).preimage continuous_subtype_val

private def normOneIntegralArch (a : normOneIntegralBlock F) : archNormOne F :=
  ⟨(Homeomorph.prodUnits a.val.val).1, (archNormOne_iff F _).mpr (by
    have ha : ideleNorm F a.val.val = 1 := a.val.property
    rwa [ideleNorm_eq_arch_of_finite_integral F _ a.property] at ha)⟩

private def normOneIntegralFinite (a : normOneIntegralBlock F) : IntegralFiniteUnits F :=
  ⟨(Homeomorph.prodUnits a.val.val).2, (ideleDivisor_ker_iff_prodUnits F _).mp a.property⟩

private def assembleNormOneIntegralBlock (p : archNormOne F × IntegralFiniteUnits F) :
    normOneIntegralBlock F := by
  let a : Idele F := Homeomorph.prodUnits.symm (p.1.val, p.2.val)
  have hp : Homeomorph.prodUnits a = (p.1.val, p.2.val) := Homeomorph.apply_symm_apply _ _
  have ha : a ∈ (ideleDivisor F).ker := (ideleDivisor_ker_iff_prodUnits F a).mpr (by
    rw [hp]
    exact p.2.property)
  have hn : a ∈ (ideleNorm F).ker := by
    change ideleNorm F a = 1
    rw [ideleNorm_eq_arch_of_finite_integral F a ha]
    have h := congrArg (fun p : InfiniteIdeles F × FiniteUnits F => ‖p.1.val‖) hp
    exact h.trans ((archNormOne_iff F _).mp p.1.property)
  exact ⟨⟨a, hn⟩, ha⟩

/-- The norm-one integral block has the product topology on the
Archimedean norm-one group and the finite integral units. -/
private def normOneIntegralBlockHomeomorph :
    normOneIntegralBlock F ≃ₜ archNormOne F × IntegralFiniteUnits F where
  toFun a := (normOneIntegralArch F a, normOneIntegralFinite F a)
  invFun := assembleNormOneIntegralBlock F
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    exact Homeomorph.prodUnits.symm_apply_apply a.val.val
  right_inv p := by
    have h := (Homeomorph.prodUnits (α := InfiniteAdeleRing F)
      (β := FiniteAdeleRing (𝓞 F) F)).apply_symm_apply (p.1.val, p.2.val)
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  continuous_toFun := by
    have hv : Continuous (fun a : normOneIntegralBlock F => a.val.val) :=
      (continuous_subtype_val : Continuous (Subtype.val : NormOneIdeles F → Idele F)).comp
        (continuous_subtype_val : Continuous (Subtype.val : normOneIntegralBlock F → NormOneIdeles F))
    have h : Continuous (fun a : normOneIntegralBlock F =>
        (Homeomorph.prodUnits (α := InfiniteAdeleRing F) (β := FiniteAdeleRing (𝓞 F) F)) a.val.val) :=
      Homeomorph.prodUnits.continuous.comp hv
    exact (h.fst.subtype_mk _).prodMk (h.snd.subtype_mk _)
  continuous_invFun := by
    have h : Continuous (fun p : archNormOne F × IntegralFiniteUnits F =>
        (Homeomorph.prodUnits (α := InfiniteAdeleRing F) (β := FiniteAdeleRing (𝓞 F) F)).symm
          (p.1.val, p.2.val)) :=
      Homeomorph.prodUnits.symm.continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd))
    exact (h.subtype_mk _).subtype_mk _

def normOneIntegralEmbed (p : archNormOne F × IntegralFiniteUnits F) : NormOneIdeles F :=
  ((normOneIntegralBlockHomeomorph F).symm p).val

theorem normOneIntegralEmbed_open :
    IsOpenEmbedding (normOneIntegralEmbed F) :=
  (normOneIntegralBlock_open F).isOpenEmbedding_subtypeVal.comp
    (normOneIntegralBlockHomeomorph F).symm.isOpenEmbedding

/-- The open integral block inclusion respects the actual idele multiplication. -/
def normOneIntegralEmbedHom :
    archNormOne F × IntegralFiniteUnits F →* NormOneIdeles F where
  toFun := normOneIntegralEmbed F
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    rfl

theorem normOneIntegralEmbed_divisor (p : archNormOne F × IntegralFiniteUnits F) :
    ideleDivisor F (normOneIntegralEmbedHom F p).val = 1 :=
  ((normOneIntegralBlockHomeomorph F).symm p).property

/-- The integral cell using the manuscript's Archimedean sector. -/
def ideleIntegralCell (A : Set (archNormOne F)) : Set (NormOneIdeles F) :=
  normOneIntegralEmbed F '' (A ×ˢ univ)

private theorem ideleIntegralCell_mem_iff (A : Set (archNormOne F)) (a : NormOneIdeles F) :
    a ∈ ideleIntegralCell F A ↔
      ∃ ha : a ∈ normOneIntegralBlock F,
        normOneIntegralArch F ⟨a, ha⟩ ∈ A := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    let x := (normOneIntegralBlockHomeomorph F).symm p
    refine ⟨x.property, ?_⟩
    have he : (normOneIntegralBlockHomeomorph F) x = p :=
      (normOneIntegralBlockHomeomorph F).apply_symm_apply p
    change ((normOneIntegralBlockHomeomorph F) x).1 ∈ _
    rw [he]
    exact hp.1
  · rintro ⟨ha, hx⟩
    let p := (normOneIntegralBlockHomeomorph F) ⟨a, ha⟩
    refine ⟨p, ⟨hx, mem_univ _⟩, ?_⟩
    exact congrArg Subtype.val ((normOneIntegralBlockHomeomorph F).symm_apply_apply ⟨a, ha⟩)

/-- The integral cell using the manuscript's Archimedean sector. -/
def ideleFundamentalCell (v : InfinitePlace F) : Set (NormOneIdeles F) :=
  ideleIntegralCell F (archFundamentalDomain F v)

private theorem ideleFundamentalCell_mem_iff (v : InfinitePlace F) (a : NormOneIdeles F) :
    a ∈ ideleFundamentalCell F v ↔
      ∃ ha : a ∈ normOneIntegralBlock F,
        normOneIntegralArch F ⟨a, ha⟩ ∈ archFundamentalDomain F v :=
  ideleIntegralCell_mem_iff F _ a

theorem ideleFundamentalCell_containedCompact (v : InfinitePlace F) :
    ∃ K : Set (NormOneIdeles F), IsCompact K ∧ ideleFundamentalCell F v ⊆ K := by
  letI : CompactSpace (IntegralFiniteUnits F) :=
    isCompact_iff_compactSpace.mp (finiteIntegralUnits_compact (F := F))
  refine ⟨normOneIntegralEmbed F '' (closure (archFundamentalDomain F v) ×ˢ univ), ?_, ?_⟩
  · exact ((archFundamentalDomain_compact_closure F v).prod isCompact_univ).image
      (normOneIntegralEmbed_open F).continuous
  · exact image_mono (prod_mono subset_closure subset_rfl)

theorem ideleFundamentalCell_interior (v : InfinitePlace F) :
    (interior (ideleFundamentalCell F v)).Nonempty := by
  obtain ⟨a, ha⟩ := archFundamentalDomain_interior F v
  let p : archNormOne F × IntegralFiniteUnits F := (a, 1)
  refine ⟨normOneIntegralEmbed F p, interior_maximal (t := normOneIntegralEmbed F ''
    (interior (archFundamentalDomain F v) ×ˢ (univ : Set (IntegralFiniteUnits F)))) ?_ ?_ ?_⟩
  · exact image_mono (prod_mono interior_subset subset_rfl)
  · exact (normOneIntegralEmbed_open F).isOpenMap _ (isOpen_interior.prod isOpen_univ)
  · exact ⟨p, ⟨ha, mem_univ _⟩, rfl⟩


/-- Principal ideles as elements of the norm-one group. -/
def principalNormOne : Fˣ →* NormOneIdeles F :=
  (principalIdele F).codRestrict _ (ideleNorm_principal F)

def normOneIdealClass : NormOneIdeles F →* ClassGroup (𝓞 F) :=
  (ideleIdealClass F).comp (ideleNorm F).ker.subtype

private theorem normOneIdealClass_principal (t : Fˣ) :
    normOneIdealClass F (principalNormOne F t) = 1 :=
  (ideleIdealClass_ker_iff F _).mpr ⟨t, 1, by
    change principalIdele F t = principalIdele F t * 1
    rw [mul_one]⟩

private theorem normOneIdealClass_cell (A : Set (archNormOne F)) {a : NormOneIdeles F}
    (ha : a ∈ ideleIntegralCell F A) : normOneIdealClass F a = 1 := by
  obtain ⟨h, _⟩ := (ideleIntegralCell_mem_iff F A a).mp ha
  exact (ideleIdealClass_ker_iff F a.val).mpr ⟨1, ⟨a.val, h⟩, by simp⟩

private theorem normOneIntegralArch_global_mul (u : (𝓞 F)ˣ) (b : NormOneIdeles F)
    (hb : b ∈ normOneIntegralBlock F)
    (hp : principalNormOne F (integralUnitToField F u) * b ∈ normOneIntegralBlock F) :
    normOneIntegralArch F ⟨principalNormOne F (integralUnitToField F u) * b, hp⟩ =
      globalUnitArch F u * normOneIntegralArch F ⟨b, hb⟩ := rfl

private theorem globalUnit_mul_integralBlock (u : (𝓞 F)ˣ) (b : NormOneIdeles F)
    (hb : b ∈ normOneIntegralBlock F) :
    principalNormOne F (integralUnitToField F u) * b ∈ normOneIntegralBlock F :=
  (ideleDivisor F).ker.mul_mem
    ((principalIdele_integral_iff F _).mpr ⟨u, rfl⟩) hb

theorem ideleIntegralCell_no_translate (A : Set (archNormOne F))
    (hA : ∀ a : archNormOne F, ∃! u : (𝓞 F)ˣ, globalUnitArch F u * a ∈ A) (b : NormOneIdeles F)
    (hb : b ∈ ideleIntegralCell F A) (t : Fˣ)
    (ht : principalNormOne F t * b ∈ ideleIntegralCell F A) : t = 1 := by
  obtain ⟨h₀, hb'⟩ := (ideleIntegralCell_mem_iff F A b).mp hb
  obtain ⟨h₁, ht'⟩ := (ideleIntegralCell_mem_iff F A _).mp ht
  have hx : principalIdele F t ∈ (ideleDivisor F).ker := by
    have h := (ideleDivisor F).ker.mul_mem h₁ ((ideleDivisor F).ker.inv_mem h₀)
    change (principalIdele F t * b.val) * b.val⁻¹ ∈ _ at h
    rwa [mul_inv_cancel_right] at h
  obtain ⟨u, hu⟩ := (principalIdele_integral_iff F t).mp hx
  subst t
  rw [normOneIntegralArch_global_mul F u b h₀ h₁] at ht'
  obtain ⟨w, _, he⟩ := hA (normOneIntegralArch F ⟨b, h₀⟩)
  have ho : globalUnitArch F 1 * normOneIntegralArch F ⟨b, h₀⟩ ∈ A := by
    simpa only [map_one, one_mul] using hb'
  rw [show u = 1 from (he u ht').trans (he 1 ho).symm, map_one]

theorem ideleIntegralCell_unique (A : Set (archNormOne F))
    (hA : ∀ a : archNormOne F, ∃! u : (𝓞 F)ˣ, globalUnitArch F u * a ∈ A) (a : NormOneIdeles F)
    (ha : normOneIdealClass F a = 1) :
    ∃! t : Fˣ, principalNormOne F t * a ∈ ideleIntegralCell F A := by
  obtain ⟨s, b, hn, he⟩ := (ideleNormOne_idealClass_ker_iff F a).mp ha
  let b₀ : NormOneIdeles F := ⟨b.val, by
    change ideleNorm F b.val = 1
    rw [ideleNorm_eq_arch_of_finite_integral F _ b.property, hn]⟩
  have h₀ : b₀ ∈ normOneIntegralBlock F := b.property
  obtain ⟨u, hu, _⟩ := hA (normOneIntegralArch F ⟨b₀, h₀⟩)
  let t := integralUnitToField F u / s
  have hab : a = principalNormOne F s * b₀ := Subtype.ext he
  have htb : principalNormOne F t * a = principalNormOne F (integralUnitToField F u) * b₀ := by
    rw [hab, ← mul_assoc, ← map_mul]
    change principalNormOne F (integralUnitToField F u / s * s) * b₀ = _
    rw [div_mul_cancel]
  have ht : principalNormOne F t * a ∈ ideleIntegralCell F A := by
    rw [htb, ideleIntegralCell_mem_iff]
    refine ⟨globalUnit_mul_integralBlock F u b₀ h₀, ?_⟩
    rwa [normOneIntegralArch_global_mul F u b₀ h₀]
  refine ⟨t, ht, ?_⟩
  intro w hw
  have heq : principalNormOne F (w / t) * (principalNormOne F t * a) =
      principalNormOne F w * a := by
    rw [← mul_assoc, ← map_mul, div_mul_cancel]
  have hm : principalNormOne F (w / t) * (principalNormOne F t * a) ∈ ideleIntegralCell F A := by
    rwa [heq]
  exact div_eq_one.mp (ideleIntegralCell_no_translate F A hA _ ht (w / t) hm)

theorem ideleFundamentalCell_no_translate (v : InfinitePlace F) (b : NormOneIdeles F)
    (hb : b ∈ ideleFundamentalCell F v) (t : Fˣ)
    (ht : principalNormOne F t * b ∈ ideleFundamentalCell F v) : t = 1 :=
  ideleIntegralCell_no_translate F _ (archFundamentalDomain_unique F v) b hb t ht

theorem ideleFundamentalCell_unique (v : InfinitePlace F) (a : NormOneIdeles F)
    (ha : normOneIdealClass F a = 1) :
    ∃! t : Fˣ, principalNormOne F t * a ∈ ideleFundamentalCell F v :=
  ideleIntegralCell_unique F _ (archFundamentalDomain_unique F v) a ha

theorem ideleFundamentalCell_divisor_zero (v : InfinitePlace F) {a : NormOneIdeles F}
    (ha : a ∈ ideleFundamentalCell F v) : ideleDivisor F a.val = 1 :=
  ((ideleFundamentalCell_mem_iff F v a).mp ha).choose

theorem ideleFundamentalCell_mul_integral_arch_one (v : InfinitePlace F) (a b : NormOneIdeles F)
    (hb : ideleDivisor F b.val = 1) (hbArch : b.val.val.1 = 1) :
    a * b ∈ ideleFundamentalCell F v ↔ a ∈ ideleFundamentalCell F v := by
  have hb₀ : b ∈ normOneIntegralBlock F := hb
  have block (x : NormOneIdeles F) (hx : x ∈ normOneIntegralBlock F) :
      x * b ∈ normOneIntegralBlock F := (ideleDivisor F).ker.mul_mem hx hb₀
  have coord (x : NormOneIdeles F) (hx : x ∈ normOneIntegralBlock F) :
      normOneIntegralArch F ⟨x * b, block x hx⟩ = normOneIntegralArch F ⟨x, hx⟩ := by
    apply Subtype.ext
    apply Units.ext
    change x.val.val.1 * b.val.val.1 = x.val.val.1
    rw [hbArch, mul_one]
  rw [ideleFundamentalCell_mem_iff, ideleFundamentalCell_mem_iff]
  constructor
  · rintro ⟨hab, hab'⟩
    have ha : a ∈ normOneIntegralBlock F := by
      have h := (ideleDivisor F).ker.mul_mem hab ((ideleDivisor F).ker.inv_mem hb₀)
      change (a.val * b.val) * b.val⁻¹ ∈ _ at h
      rwa [mul_inv_cancel_right] at h
    exact ⟨ha, coord a ha ▸ hab'⟩
  · rintro ⟨ha, ha'⟩
    exact ⟨block a ha, (coord a ha).symm ▸ ha'⟩

/-- The union of translates of the integral cell by representatives of
the finite ideal-class group, as in (A.2.3.14). -/
def ideleDomainFromArchCell (A : Set (archNormOne F)) (g : ClassGroup (𝓞 F) → NormOneIdeles F) :
    Set (NormOneIdeles F) :=
  ⋃ c, (Homeomorph.mulLeft (g c)) '' ideleIntegralCell F A

def ideleFundamentalDomain (v : InfinitePlace F) (g : ClassGroup (𝓞 F) → NormOneIdeles F) :
    Set (NormOneIdeles F) :=
  ideleDomainFromArchCell F (archFundamentalDomain F v) g

/-- The union has compact closure and nonempty interior. -/
theorem ideleFundamentalDomain_topology (v : InfinitePlace F)
    (g : ClassGroup (𝓞 F) → NormOneIdeles F) :
    IsCompact (closure (ideleFundamentalDomain F v g)) ∧
    (interior (ideleFundamentalDomain F v g)).Nonempty := by
  letI : T2Space (Idele F) := ideles_hausdorff
  obtain ⟨K, hK, hcell⟩ := ideleFundamentalCell_containedCompact F v
  let D := ⋃ c, (Homeomorph.mulLeft (g c)) '' K
  have hD : IsCompact D := isCompact_iUnion fun c => hK.image (Homeomorph.mulLeft (g c)).continuous
  constructor
  · apply hD.closure_of_subset
    apply iUnion_mono
    intro c
    exact image_mono hcell
  · obtain ⟨a, ha⟩ := ideleFundamentalCell_interior F v
    let e := Homeomorph.mulLeft (g 1)
    have hopen : IsOpen (e '' interior (ideleFundamentalCell F v)) := e.isOpenMap _ isOpen_interior
    have hg : e '' ideleFundamentalCell F v ⊆ ideleFundamentalDomain F v g := by
      unfold ideleFundamentalDomain
      exact subset_iUnion (fun c => (Homeomorph.mulLeft (g c)) '' ideleFundamentalCell F v) 1
    exact ⟨e a, interior_maximal ((image_mono interior_subset).trans hg) hopen ⟨a, ha, rfl⟩⟩

/-- Lemma 2.2.2.1(3) on the full radial family of the idelic fundamental
domain. The norm section leaves all finite coordinates fixed, so the compact
set of finite inverses from the norm-one domain supplies one fractional ideal
for all positive moduli. This uses the domain reduction in the Apache-2.0
RiemannMasullo proof at e12e4c4. -/
theorem pure_theta_fractionalIdeal_bound_fundamentalDomain (v : InfinitePlace F)
    (r : ClassGroup (𝓞 F) → NormOneIdeles F)
    (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (ψ : FiniteBruhat F)
    (hψ : ∀ y, ‖ψ.toLocallyConstant y‖ ≤ 1) :
    ∃ I : FractionalIdeal (𝓞 F)⁰ F, ∀ t : Multiplicative ℝ,
      ∀ u ∈ ideleFundamentalDomain F v r,
        let g : Idele F := ideleExpSection F t * u.val
        let inner (ξ : {ξ : Fˣ // (ξ : F) ∈ I}) :=
          ‖φ (mixedArch g.val * mixedEmbedding F (ξ.val : F))‖
        Summable inner ∧
          (∑' ξ, ‖thetaSummand F (bruhatTensor F φ ψ) g ξ‖) ≤ ∑' ξ, inner ξ := by
  let inverseFinite (u : NormOneIdeles F) := (u.val⁻¹).val.2
  have hcont : Continuous inverseFinite := by
    have h : Continuous (fun a : Idele F => a.inv.2) :=
      continuous_snd.comp Units.continuous_coe_inv
    exact h.comp continuous_subtype_val
  obtain ⟨I, hI⟩ := pure_theta_fractionalIdeal_bound φ ψ hψ
    (((ideleFundamentalDomain_topology F v r).1).image hcont)
  refine ⟨I, fun t u hu => hI _ ?_⟩
  refine ⟨u, subset_closure hu, ?_⟩
  change (u.val⁻¹).val.2 = ((ideleExpSection F t * u.val)⁻¹).val.2
  rw [mul_inv_rev]
  change (u.val⁻¹).val.2 = (u.val⁻¹).val.2 * ((ideleExpSection F t)⁻¹).val.2
  rw [← map_inv (ideleExpSection F), (ideleExpSection_components F t⁻¹).2, mul_one]

private theorem ideleDomainFromArchCell_mem_iff (A : Set (archNormOne F))
    (g : ClassGroup (𝓞 F) → NormOneIdeles F)
    (hg : ∀ c, normOneIdealClass F (g c) = c) (a : NormOneIdeles F) :
    a ∈ ideleDomainFromArchCell F A g ↔
      (g (normOneIdealClass F a))⁻¹ * a ∈ ideleIntegralCell F A := by
  constructor
  · intro h
    obtain ⟨c, b, hb, he⟩ := mem_iUnion.mp h
    change g c * b = a at he
    have hc : normOneIdealClass F a = c := by
      rw [← he, map_mul, hg, normOneIdealClass_cell F A hb]
      exact mul_one c
    rw [hc, ← he, inv_mul_cancel_left]
    exact hb
  · intro h
    exact mem_iUnion.mpr ⟨normOneIdealClass F a, ⟨_, h, mul_inv_cancel_left _ _⟩⟩

/-- Each principal orbit has a unique representative in the global
norm-one idelic fundamental domain. -/
theorem ideleDomainFromArchCell_unique (A : Set (archNormOne F))
    (hA : ∀ a : archNormOne F, ∃! u : (𝓞 F)ˣ, globalUnitArch F u * a ∈ A)
    (g : ClassGroup (𝓞 F) → NormOneIdeles F)
    (hg : ∀ c, normOneIdealClass F (g c) = c) (a : NormOneIdeles F) :
    ∃! t : Fˣ, principalNormOne F t * a ∈ ideleDomainFromArchCell F A g := by
  let c := normOneIdealClass F a
  let b := (g c)⁻¹ * a
  have hb : normOneIdealClass F b = 1 := by
    change normOneIdealClass F ((g c)⁻¹ * a) = 1
    rw [map_mul, map_inv, hg]
    exact inv_mul_cancel c
  obtain ⟨t, ht, hu⟩ := ideleIntegralCell_unique F A hA b hb
  have he (w : Fˣ) : principalNormOne F w * a ∈ ideleDomainFromArchCell F A g ↔
      principalNormOne F w * b ∈ ideleIntegralCell F A := by
    rw [ideleDomainFromArchCell_mem_iff F A g hg, map_mul, normOneIdealClass_principal]
    have h₁ : 1 * normOneIdealClass F a = c := one_mul _
    rw [h₁]
    change (g c)⁻¹ * (principalNormOne F w * a) ∈ _ ↔
      principalNormOne F w * ((g c)⁻¹ * a) ∈ _
    rw [mul_left_comm]
  exact ⟨t, (he t).mpr ht, fun w hw => hu w ((he w).mp hw)⟩

theorem ideleFundamentalDomain_unique (v : InfinitePlace F)
    (g : ClassGroup (𝓞 F) → NormOneIdeles F)
    (hg : ∀ c, normOneIdealClass F (g c) = c) (a : NormOneIdeles F) :
    ∃! t : Fˣ, principalNormOne F t * a ∈ ideleFundamentalDomain F v g :=
  ideleDomainFromArchCell_unique F _ (archFundamentalDomain_unique F v) g hg a

/-- Only finitely many principal translates of the closed domain meet
any compact subset of the norm-one idele group. -/
theorem ideleFundamentalDomain_finite_translates (v : InfinitePlace F)
    (g : ClassGroup (𝓞 F) → NormOneIdeles F) {K : Set (NormOneIdeles F)}
    (hK : IsCompact K) :
    {t : Fˣ | ∃ x ∈ closure (ideleFundamentalDomain F v g), principalNormOne F t * x ∈ K}.Finite := by
  let val : NormOneIdeles F → Idele F := Subtype.val
  have hD := (ideleFundamentalDomain_topology F v g).1
  refine (principalIdele_finite_translates F (hK.image (f := val) continuous_subtype_val)
    (hD.image (f := val) continuous_subtype_val)).subset ?_
  rintro t ⟨x, hx, ht⟩
  exact ⟨x.val, ⟨x, hx, rfl⟩, ⟨principalNormOne F t * x, ht, rfl⟩⟩


theorem ideleFundamentalDomain_measurable [MeasurableSpace (NormOneIdeles F)]
    [BorelSpace (NormOneIdeles F)] (v : InfinitePlace F)
    (g : ClassGroup (𝓞 F) → NormOneIdeles F) :
    MeasurableSet (ideleFundamentalDomain F v g) := by
  letI : MeasurableSpace (archNormOne F) := borel _
  letI : BorelSpace (archNormOne F) := ⟨rfl⟩
  have he : MeasurableEmbedding (Subtype.val : normOneIntegralBlock F → NormOneIdeles F) :=
    (normOneIntegralBlock_open F).isOpenEmbedding_subtypeVal.measurableEmbedding
  have hf : Continuous (normOneIntegralArch F) := (normOneIntegralBlockHomeomorph F).continuous.fst
  have hd : MeasurableSet (ideleFundamentalCell F v) := by
    have hs : ideleFundamentalCell F v =
        (Subtype.val : normOneIntegralBlock F → NormOneIdeles F) ''
          ((normOneIntegralArch F) ⁻¹' archFundamentalDomain F v) := by
      ext a
      rw [ideleFundamentalCell_mem_iff]
      constructor
      · rintro ⟨ha, hx⟩
        exact ⟨⟨a, ha⟩, hx, rfl⟩
      · rintro ⟨⟨a, ha⟩, hx, rfl⟩
        exact ⟨ha, hx⟩
    rw [hs]
    exact he.measurableSet_image.mpr (hf.measurable (archFundamentalDomain_measurable F v))
  exact MeasurableSet.iUnion fun c => (Homeomorph.mulLeft (g c)).toMeasurableEquiv.measurableEmbedding
    |>.measurableSet_image.mpr hd

end

end Masullo
