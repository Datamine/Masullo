import ArchimedeanGammaProductTest
import FiniteMellinShellTest

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev L (v : S) := v.val.adicCompletion F
private abbrev FiniteTests := locallyConstantTests (∀ v : S, L F S v)
private abbrev Characters := PontryaginDual (SLocalThetaNormOne F S)

variable [∀ v : S, MeasurableSpace (L F S v)ˣ] [∀ v : S, BorelSpace (L F S v)ˣ]
variable (μ : ∀ v : S, Measure (L F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]

private theorem finiteProductUnitTests_continued
    (χ : ∀ v : S, (L F S v)ˣ →ₜ* Circle) (g : ∀ v : S, locallyConstantTests (L F S v))
    (A : S → ℂ) (hA : ∀ v z, 0 < z.re → finiteZetaIntegral F v.val (μ v) (χ v) (g v) z = A v)
    (c : ℂ) :
    letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
    (fun z ↦ sLocalFiniteZetaContinued F S μ χ z (locallyConstantTestPiProduct g)) =ᶠ[𝓝[≠] c]
      fun _ ↦ ∏ v, A v := by
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  refine boundedPoleMellinSpace_unique_germs
    (isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re) ⟨1, by simp⟩
    (sLocalFiniteZetaContinued_meromorphic F S μ χ _) (Meromorphic.const _) ?_ c
  intro z hz
  change sLocalFiniteZetaContinued F S μ χ z (locallyConstantTestPiProduct g) = ∏ v, A v
  rw [(sLocalFiniteZetaContinued_eq_integral F S μ χ _ z hz).2]
  let h (v : S) (u : (L F S v)ˣ) :=
    (g v).val u.val * (χ v u : ℂ) * finiteZetaWeight F v.val z u
  have he : sLocalFiniteZetaIntegrand F S χ (locallyConstantTestPiProduct g) z =
      fun u ↦ ∏ v, h v (u v) := by
    funext u
    simp only [sLocalFiniteZetaIntegrand, locallyConstantTestPiProduct_apply,
      ← Finset.prod_mul_distrib, h, mul_assoc]
  rw [he, integral_fintype_prod_eq_prod h]
  exact Finset.prod_congr rfl (fun v _ ↦ hA v z hz)

private abbrev ArchDenominator (ω : Characters F S) :=
  archimedeanNumberFieldZetaDenominator F
    (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω)

private abbrev Z (ω : Characters F S) (f : sLocalBruhatImage F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

private theorem exists_sLocalArchGammaPureWitness (ω : Characters F S) :
    ∃ (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
      (g : ∀ v : S, locallyConstantTests (v.val.adicCompletion F)),
      (∀ v, (g v).val 0 = 0) ∧ ∃ A : ℂ, A ≠ 0 ∧ ∀ c : ℂ,
        Z F S μ ω (sLocalBruhatPure F S φ (locallyConstantTestPiProduct g)) =ᶠ[𝓝[≠] c]
          fun z ↦ A * (ArchDenominator F S ω z)⁻¹ := by
  let a := sLocalRealArchParameters F S ω
  let j := sLocalComplexArchParameters F S ω
  let χ := sLocalFiniteZetaPhases F S ω
  obtain ⟨φ, hφ⟩ := exists_archimedeanGammaProductTest F a j
    (sLocalRealArchParameters_re F S ω) (sLocalComplexArchParameters_re F S ω)
  choose g A h0 hA hI _ using fun v : S ↦ exists_finiteMellinUnitTest F v.val (μ v) (χ v)
  let ψ := locallyConstantTestPiProduct g
  refine ⟨φ, g, h0,
    ∏ v, A v, Finset.prod_ne_zero_iff.mpr (fun v _ ↦ hA v), fun c ↦ ?_⟩
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  filter_upwards [finiteProductUnitTests_continued F S μ χ g A hI c, hφ c] with z hgz hφz
  change archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z
    (sLocalFiniteZetaSchwartzTest F S μ χ z (sLocalBruhatPure F S φ ψ)) = _
  rw [sLocalFiniteZetaSchwartzTest, sLocalBruhatContractFinite_pure, map_smul, smul_eq_mul]
  exact congrArg₂ (· * ·) hgz hφz

/-- The full finite principal-value range contains a test whose actual
S-local Mellin transform is a nonzero constant times the archimedean
Euler product, as a germ at every center. -/
theorem exists_sLocalArchGammaWitness (ω : Characters F S) :
    ∃ (f : sLocalBruhatImage F S), f ∈ sLocalFiniteNonzeroTestSubspace F S Finset.univ ∧
      ∃ A : ℂ, A ≠ 0 ∧ ∀ c : ℂ,
        Z F S μ ω f =ᶠ[𝓝[≠] c] fun z ↦ A * (ArchDenominator F S ω z)⁻¹ := by
  obtain ⟨φ, g, h0, A, hA, he⟩ := exists_sLocalArchGammaPureWitness F S μ ω
  exact ⟨sLocalBruhatPure F S φ (locallyConstantTestPiProduct g),
    Submodule.subset_span ⟨φ, g, fun v _ ↦ h0 v, rfl⟩, A, hA, he⟩

private theorem translatedDenominator_factor {I : Type*} [Fintype I]
    (D : I → ℂ → ℂ) (b : I → ℂ) (c : ℂ)
    (hD : ∀ i, AnalyticAt ℂ (D i) (c + b i))
    (hs : ∀ i, D i (c + b i) = 0 → analyticOrderAt (D i) (c + b i) = 1) :
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U c ∧ U c ≠ 0 ∧
      (fun z ↦ ∏ i, D i (z + b i)) =ᶠ[𝓝 c] fun z ↦
        (z - c) ^ (Finset.univ.filter (fun i ↦ D i (c + b i) = 0)).card * U z := by
  obtain ⟨U, hU, hU₀, he, _⟩ := analytic_finset_prod_factor_simpleZeros Finset.univ
    (fun i z ↦ D i (z + b i)) c
    (fun i _ ↦ (hD i).comp (f := fun z : ℂ ↦ z + b i) (analyticAt_id.add analyticAt_const))
    (fun i _ hi ↦ by
      let g (z : ℂ) := z + b i
      have hg : AnalyticAt ℂ g c := analyticAt_id.add analyticAt_const
      have hd : HasDerivAt g 1 c := (hasDerivAt_id c).add_const (b i)
      change analyticOrderAt (D i ∘ g) c = 1
      rw [analyticOrderAt_comp_of_deriv_ne_zero hg (by rw [hd.deriv]; exact one_ne_zero)]
      exact hs i hi)
  exact ⟨U, hU, hU₀, he⟩

private theorem sLocalArchGammaWitness_order (ω : Characters F S) (f : sLocalBruhatImage F S)
    (A : ℂ) (hA : A ≠ 0) (c : ℂ)
    (he : Z F S μ ω f =ᶠ[𝓝[≠] c] fun z ↦ A * (ArchDenominator F S ω z)⁻¹) :
    meromorphicOrderAt (Z F S μ ω f) c = -(sLocalArchPoleCount F S ω c : WithTop ℤ) := by
  let a := sLocalRealArchParameters F S ω
  let j := sLocalComplexArchParameters F S ω
  obtain ⟨U, hU, hU₀, hu⟩ := translatedDenominator_factor
    (fun i ↦ realArchZetaDenominator (a i).2) (fun i ↦ (a i).1) c
    (fun i ↦ realArchZetaDenominator_analytic (a i).2 _) (fun i ↦ realArchZetaDenominator_simple_zero _ _)
  obtain ⟨V, hV, hV₀, hv⟩ := translatedDenominator_factor
    (fun i ↦ complexArchZetaDenominator (j i).2) (fun i ↦ (j i).1) c
    (fun i ↦ complexArchZetaDenominator_analytic (j i).2 _) (fun i ↦ complexArchZetaDenominator_simple_zero _ _)
  have hD := archimedeanNumberFieldZetaDenominator_analytic F a j c
  have hOrd : analyticOrderAt (ArchDenominator F S ω) c = sLocalArchPoleCount F S ω c := by
    refine hD.analyticOrderAt_eq_natCast.mpr ⟨fun z ↦ U z * V z, hU.mul hV, mul_ne_zero hU₀ hV₀, ?_⟩
    filter_upwards [hu, hv] with z hz hz'
    dsimp only [ArchDenominator, archimedeanNumberFieldZetaDenominator, smul_eq_mul]
    rw [hz, hz']
    change _ = (z - c) ^
      ((Finset.univ.filter fun i ↦ realArchZetaDenominator (a i).2 (c + (a i).1) = 0).card +
        (Finset.univ.filter fun i ↦ complexArchZetaDenominator (j i).2 (c + (j i).1) = 0).card) *
        (U z * V z)
    rw [pow_add]
    ring
  rw [meromorphicOrderAt_congr he]
  change meromorphicOrderAt ((fun _ : ℂ ↦ A) * (ArchDenominator F S ω)⁻¹) c = _
  rw [meromorphicOrderAt_mul (Meromorphic.const A c) hD.meromorphicAt.inv,
    meromorphicOrderAt_const, ite_eq_right hA, zero_add,
    meromorphicOrderAt_inv, hD.meromorphicOrderAt_eq, hOrd, ENat.map_natCast]
  rfl

/-- A single pure test attains the full archimedean multiplicity at
every center. Its finite factors vanish at the respective origins. -/
theorem exists_sLocalArchFullPoleOrderPureTest (ω : Characters F S) :
    ∃ (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
      (g : ∀ v : S, locallyConstantTests (v.val.adicCompletion F)),
      (∀ v, (g v).val 0 = 0) ∧ ∀ c : ℂ,
        meromorphicOrderAt (Z F S μ ω (sLocalBruhatPure F S φ (locallyConstantTestPiProduct g))) c =
          -(sLocalArchPoleCount F S ω c : WithTop ℤ) := by
  obtain ⟨φ, g, h0, A, hA, he⟩ := exists_sLocalArchGammaPureWitness F S μ ω
  exact ⟨φ, g, h0, fun c ↦ sLocalArchGammaWitness_order F S μ ω _ A hA c (he c)⟩

/-- The same test attains the full surviving multiplicity at every
archimedean pole, even when several local Gamma factors have that pole. -/
theorem exists_sLocalArchFullPoleOrderTest (ω : Characters F S) :
    ∃ (f : sLocalBruhatImage F S), f ∈ sLocalFiniteNonzeroTestSubspace F S Finset.univ ∧
      ∀ c : ℂ, meromorphicOrderAt (Z F S μ ω f) c = -(sLocalArchPoleCount F S ω c : WithTop ℤ) := by
  obtain ⟨φ, g, h0, he⟩ := exists_sLocalArchFullPoleOrderPureTest F S μ ω
  exact ⟨sLocalBruhatPure F S φ (locallyConstantTestPiProduct g),
    Submodule.subset_span ⟨φ, g, fun v _ ↦ h0 v, rfl⟩, he⟩

/-- A pole of exact positive order has a nonzero leading Laurent coefficient. -/
theorem sLocalLaurentCoeff_ne_zero_of_exact_order (ω : Characters F S) (f : sLocalBruhatImage F S)
    (c : ℂ) (n : ℕ) (hn : 0 < n) (ho : meromorphicOrderAt (Z F S μ ω f) c = -(n : WithTop ℤ)) :
    sLocalLaurentCoeff F S μ ω c n f ≠ 0 := by
  intro hZero
  have hAll (k : ℕ) (hk : n - 1 < k) : sLocalLaurentCoeff F S μ ω c k f = 0 := by
    by_cases he : k = n
    · simpa only [he] using hZero
    · apply (sLocalLaurentCoeff_vanish_iff F S μ ω c n f).mpr
      · rw [ho]
        rfl
      · omega
  have hBad := (sLocalLaurentCoeff_vanish_iff F S μ ω c (n - 1) f).mp hAll
  rw [ho] at hBad
  change (↑(-((n - 1 : ℕ) : ℤ)) : WithTop ℤ) ≤ ↑(-(n : ℤ)) at hBad
  rw [WithTop.coe_le_coe] at hBad
  omega

/-- One test makes the highest allowed Laurent coefficient nonzero
at every archimedean pole. -/
theorem exists_sLocalArchTopLaurentTest (ω : Characters F S) :
    ∃ (f : sLocalBruhatImage F S), f ∈ sLocalFiniteNonzeroTestSubspace F S Finset.univ ∧
      ∀ c : ℂ, 0 < sLocalArchPoleCount F S ω c →
        sLocalLaurentCoeff F S μ ω c (sLocalArchPoleCount F S ω c) f ≠ 0 := by
  obtain ⟨f, hf, ho⟩ := exists_sLocalArchFullPoleOrderTest F S μ ω
  exact ⟨f, hf, fun c hc ↦ sLocalLaurentCoeff_ne_zero_of_exact_order F S μ ω f c _ hc (ho c)⟩

end

end Masullo
