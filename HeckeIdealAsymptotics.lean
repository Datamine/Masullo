import HeckeEulerProducts
import FourierSymbols
import IdeleIdealClasses
import FinitePrincipalValue

open Filter Function Ideal IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.Units
  Set Topology UniqueFactorizationMonoid
open scoped NumberField nonZeroDivisors

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The imaginary norm character with frequency (t). -/
def ideleNormCircle (t : ℝ) : PontryaginDual (IdeleClass F) where
  toFun g := Circle.exp (t * Real.log (ideleClassNorm F g))
  map_one' := by simp
  map_mul' g h := by
    rw [(ideleClassNorm F).map_mul g h,
      Real.log_mul (ideleClassNorm_pos F g).ne' (ideleClassNorm_pos F h).ne',
      mul_add, Circle.exp_add]
  continuous_toFun := Circle.exp.continuous.comp
    (continuous_const.mul ((ideleClassNorm_continuous F).log fun g ↦ (ideleClassNorm_pos F g).ne'))

@[simp] theorem ideleNormCircle_neg (t : ℝ) : ideleNormCircle F (-t) = (ideleNormCircle F t)⁻¹ := by
  apply DFunLike.ext
  intro g
  change Circle.exp ((-t) * Real.log (ideleClassNorm F g)) =
    (Circle.exp (t * Real.log (ideleClassNorm F g)))⁻¹
  rw [neg_mul, Circle.exp_neg]

/-- A unitary character trivial on norm-one classes has a unique negative
imaginary norm twist. -/
theorem ideleNormCircle_existsUnique (χ : PontryaginDual (IdeleClass F))
    (hχ : ∀ k : normOneIdeleClass F, χ k.val = 1) :
    ∃! t : ℝ, χ = ideleNormCircle F (-t) := by
  let σ : Multiplicative ℝ →ₜ* IdeleClass F :=
    ⟨ideleClassExpSection F, ideleClassExpSection_continuous F⟩
  let γ := χ.comp σ
  obtain ⟨t, ht, huniq⟩ := realCharacter_exp γ
  refine ⟨-t, ?_, ?_⟩
  · change χ = ideleNormCircle F (- -t)
    rw [neg_neg]
    ext g
    let k := ideleClassNormOnePart F g
    let r := ideleClassLogNorm F g
    have he : k.val * σ r = g := (ideleClassSplit F).symm_apply_apply g
    calc
      (χ g : ℂ) = (χ (k.val * σ r) : ℂ) := congrArg (fun x ↦ (χ x : ℂ)) he.symm
      _ = (γ r : ℂ) := by rw [map_mul, hχ k, one_mul]; rfl
      _ = Complex.exp ((t : ℂ) * Complex.I * (r.toAdd : ℂ)) := ht r.toAdd
      _ = (ideleNormCircle F t g : ℂ) := by
        change _ = (Circle.exp (t * Real.log (ideleClassNorm F g)) : ℂ)
        rw [Circle.coe_exp, Complex.ofReal_mul]
        change Complex.exp ((t : ℂ) * Complex.I * (r.toAdd : ℂ)) =
          Complex.exp ((t : ℂ) * (r.toAdd : ℂ) * Complex.I)
        ring_nf
  · intro a ha
    have ha' : -a = t := huniq (-a) fun x ↦ by
      change (χ (ideleClassExpSection F (Multiplicative.ofAdd x)) : ℂ) = _
      rw [ha]
      change (Circle.exp ((-a) * Real.log (ideleClassNorm F
        (ideleClassExpSection F (Multiplicative.ofAdd x)))) : ℂ) = _
      rw [ideleClassNorm_expSection, Real.log_exp, Circle.coe_exp, Complex.ofReal_mul]
      change Complex.exp ((-a : ℝ) * (x : ℂ) * Complex.I) =
        Complex.exp (((-a : ℝ) : ℂ) * Complex.I * (x : ℂ))
      ring_nf
    exact neg_eq_iff_eq_neg.mp ha'

/-- Hecke's ideal weight with ramified prime factors omitted from the Euler product.
An ideal divisible by a ramified prime has weight zero. -/
def finiteHeckeIdealWeight (χ : PontryaginDual (IdeleClass F)) (I : Ideal (𝓞 F)) : ℂ :=
  open Classical in
  if I = ⊥ then 0 else
    ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      heckeEulerCoefficient F χ (chosenFiniteUniformizer F) v ^
        Multiset.count v.asIdeal (normalizedFactors I)

@[simp] theorem finiteHeckeIdealWeight_one (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    finiteHeckeIdealWeight F 1 I = 1 := by
  classical
  unfold finiteHeckeIdealWeight
  rw [ite_eq_right hI]
  apply finprod_eq_one_of_forall_eq_one
  intro v
  have h : unramifiedFiniteCharacter F 1 v := fun _ _ ↦ rfl
  simp [heckeEulerCoefficient, h, PontryaginDual.one_apply]

private abbrev NonzeroIdeals := nonZeroDivisors (Ideal (𝓞 F))
private abbrev IdealsUpTo (x : ℝ) := {I : NonzeroIdeals F // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ x}

private theorem idealsUpTo_finite (x : ℝ) : Finite (IdealsUpTo F x) := by
  by_cases hx : 0 ≤ x
  · unfold IdealsUpTo
    simp_rw [← Nat.le_floor_iff hx]
    exact (Ideal.finite_setOfPred_absNorm_le₀ ⌊x⌋₊).to_subtype
  · letI : IsEmpty (IdealsUpTo F x) := ⟨fun I ↦ hx ((Nat.cast_nonneg _).trans I.property)⟩
    infer_instance

/-- Ideal summation with the norm bound in Equation (B.6.1.3). -/
def finiteHeckeIdealSummatory (χ : PontryaginDual (IdeleClass F)) (x : ℝ) : ℂ :=
  ∑ᶠ I : IdealsUpTo F x, finiteHeckeIdealWeight F χ I.val.val

/-- The unweighted ideal count divided by the norm bound tends to the
Dedekind zeta residue. -/
theorem finiteHeckeIdealSummatory_one_tendsto :
    Tendsto (fun x : ℝ ↦ finiteHeckeIdealSummatory F 1 x / x) atTop
      (𝓝 (dedekindZeta_residue F : ℂ)) := by
  classical
  have hlim := (Complex.continuous_ofReal.tendsto _).comp (Ideal.tendsto_norm_le_div_atTop₀ F)
  rw [← dedekindZeta_residue_def] at hlim
  refine hlim.congr fun x ↦ ?_
  rw [Function.comp_apply, Complex.ofReal_div, Complex.ofReal_natCast]
  congr 1
  letI : Finite (IdealsUpTo F x) := idealsUpTo_finite F x
  letI : Fintype (IdealsUpTo F x) := Fintype.ofFinite _
  change (Nat.card (IdealsUpTo F x) : ℂ) = finiteHeckeIdealSummatory F 1 x
  unfold finiteHeckeIdealSummatory
  rw [Nat.card_eq_fintype_card, finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl fun I _ ↦ finiteHeckeIdealWeight_one F I.val.val
      (mem_nonZeroDivisors_iff_ne_zero.mp I.val.property),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- Lemma B.6.1.2(1). Undoing the unique norm twist gives the trivial weight,
with mean equal to the Dedekind zeta residue in class-number normalization. -/
theorem finiteHeckeIdealSummatory_normTwist_tendsto (χ : PontryaginDual (IdeleClass F))
    (hχ : ∀ k : normOneIdeleClass F, χ k.val = 1) :
    (∃! t : ℝ, χ = ideleNormCircle F (-t)) ∧
      ∀ t, χ = ideleNormCircle F (-t) →
        Tendsto (fun x : ℝ ↦ finiteHeckeIdealSummatory F (χ * ideleNormCircle F t) x / x)
          atTop (𝓝 (dedekindZeta_residue F : ℂ)) := by
  refine ⟨ideleNormCircle_existsUnique F χ hχ, fun t ht ↦ ?_⟩
  rw [ht, ideleNormCircle_neg, inv_mul_cancel]
  exact finiteHeckeIdealSummatory_one_tendsto F

/-- The volume specified by (A.3.2.1) is the class-number residue. If the
absolute discriminant is strictly greater than one, the additional factor
in (B.6.1.7) gives a strictly smaller constant. -/
theorem finiteHeckeIdealSummatory_printed_constant_lt (h : 1 < |(discr F : ℝ)|) :
    (Real.sqrt |(discr F : ℝ)|)⁻¹ * dedekindZeta_residue F < dedekindZeta_residue F := by
  have hs : 1 < Real.sqrt |(discr F : ℝ)| := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt zero_le_one h
  have hi : (Real.sqrt |(discr F : ℝ)|)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
  simpa only [one_mul] using mul_lt_mul_of_pos_right hi (dedekindZeta_residue_pos F)

section IdealClassCancellation

open scoped Classical

private abbrev IdealClass := ClassGroup (𝓞 F)
private abbrev IdealsInClassUpTo (c : IdealClass F) (x : ℝ) :=
  {I : NonzeroIdeals F // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ x ∧ ClassGroup.mk0 I = c}

private def classFiberEquiv (c : IdealClass F) (x : ℝ) :
    {I : IdealsUpTo F x // ClassGroup.mk0 I.val = c} ≃ IdealsInClassUpTo F c x :=
  Equiv.subtypeSubtypeEquivSubtypeInter
    (fun I : NonzeroIdeals F ↦ Ideal.absNorm (I : Ideal (𝓞 F)) ≤ x)
    (fun I : NonzeroIdeals F ↦ ClassGroup.mk0 I = c)

private theorem classGroup_character_sum_zero (χ : IdealClass F →* Circle) (hχ : χ ≠ 1) :
    letI : Fintype (IdealClass F) := Fintype.ofFinite _
    ∑ c : IdealClass F, (χ c : ℂ) = 0 := by
  letI : Fintype (IdealClass F) := Fintype.ofFinite _
  obtain ⟨c₀, hc₀⟩ : ∃ c, χ c ≠ 1 := by
    by_contra! h
    apply hχ
    ext c
    exact congrArg (fun u : Circle ↦ (u : ℂ)) (h c)
  let A := ∑ c : IdealClass F, (χ c : ℂ)
  have h : (χ c₀ : ℂ) * A = A := by
    rw [Finset.mul_sum]
    simp_rw [← Circle.coe_mul, ← map_mul]
    exact Equiv.sum_comp (Equiv.mulLeft c₀) (fun c ↦ (χ c : ℂ))
  have hz : ((χ c₀ : ℂ) - 1) * A = 0 := by rw [sub_mul, one_mul, h, sub_self]
  refine (mul_eq_zero.mp hz).resolve_left ?_
  intro he
  apply hc₀
  exact Circle.coe_injective (sub_eq_zero.mp he)

private theorem heckeSummatory_eq_idealClassSum
    (χ : PontryaginDual (IdeleClass F)) (ψ : IdealClass F →* Circle)
    (hχψ : ∀ I : NonzeroIdeals F, finiteHeckeIdealWeight F χ I.val = (ψ (ClassGroup.mk0 I) : ℂ))
    (x : ℝ) :
    letI : Fintype (IdealClass F) := Fintype.ofFinite _
    finiteHeckeIdealSummatory F χ x =
      ∑ c : IdealClass F, (ψ c : ℂ) * Nat.card (IdealsInClassUpTo F c x) := by
  letI : Fintype (IdealClass F) := Fintype.ofFinite _
  letI : Finite (IdealsUpTo F x) := idealsUpTo_finite F x
  letI : Fintype (IdealsUpTo F x) := Fintype.ofFinite _
  letI (c : IdealClass F) : Fintype {I : IdealsUpTo F x // ClassGroup.mk0 I.val = c} :=
    Fintype.ofFinite _
  letI (c : IdealClass F) : Fintype (IdealsInClassUpTo F c x) :=
    Fintype.ofEquiv _ (classFiberEquiv F c x)
  unfold finiteHeckeIdealSummatory
  rw [finsum_eq_sum_of_fintype]
  simp_rw [hχψ]
  let p (I : IdealsUpTo F x) := ClassGroup.mk0 I.val
  rw [← Equiv.sum_comp (Equiv.sigmaFiberEquiv p), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  change (∑ I : {I : IdealsUpTo F x // p I = c}, (ψ (p I.val) : ℂ)) = _
  trans ∑ _ : {I : IdealsUpTo F x // p I = c}, (ψ c : ℂ)
  · exact Finset.sum_congr rfl fun I _ ↦ congrArg (fun a ↦ (ψ a : ℂ)) I.property
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm (ψ c : ℂ),
    ← Nat.card_eq_fintype_card, Nat.card_congr (classFiberEquiv F c x)]

/-- The nontrivial-class-character case of Lemma B.6.1.2(2).
If the ideal weights are induced by a nontrivial ordinary class-group character,
all ideal classes have the same leading density and their leading terms cancel. -/
theorem finiteHeckeIdealSummatory_tendsto_zero_of_classCharacter
    (χ : PontryaginDual (IdeleClass F)) (ψ : IdealClass F →* Circle) (hψ : ψ ≠ 1)
    (hχψ : ∀ I : NonzeroIdeals F, finiteHeckeIdealWeight F χ I.val = (ψ (ClassGroup.mk0 I) : ℂ)) :
    Tendsto (fun x : ℝ ↦ finiteHeckeIdealSummatory F χ x / x) atTop (𝓝 0) := by
  letI : Fintype (IdealClass F) := Fintype.ofFinite _
  let k : ℝ := (2 ^ nrRealPlaces F * (2 * Real.pi) ^ nrComplexPlaces F * regulator F) /
    (torsionOrder F * Real.sqrt |discr F|)
  have hc (c : IdealClass F) : Tendsto
      (fun x : ℝ ↦ (ψ c : ℂ) * ((Nat.card (IdealsInClassUpTo F c x) : ℂ) / (x : ℂ)))
      atTop (𝓝 ((ψ c : ℂ) * (k : ℂ))) := by
    apply Tendsto.const_mul
    have hlim := (Complex.continuous_ofReal.tendsto k).comp
      (Ideal.tendsto_norm_le_and_mk_eq_div_atTop F c)
    refine hlim.congr fun x ↦ ?_
    change (((Nat.card (IdealsInClassUpTo F c x) : ℝ) / x : ℝ) : ℂ) = _
    rw [Complex.ofReal_div, Complex.ofReal_natCast]
  have hsum := tendsto_finsetSum (s := (Finset.univ : Finset (IdealClass F))) (fun c _ ↦ hc c)
  rw [← Finset.sum_mul, classGroup_character_sum_zero F ψ hψ, zero_mul] at hsum
  refine hsum.congr fun x ↦ ?_
  rw [heckeSummatory_eq_idealClassSum F χ ψ hχψ x, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  exact (mul_div_assoc _ _ _).symm

/-- The ideal-class map descends through the principal ideles. -/
def ideleClassToIdealClass : IdeleClass F →* IdealClass F :=
  QuotientGroup.lift (principalIdeles F) (ideleIdealClass F) (by
    rintro _ ⟨g, rfl⟩
    exact (ideleIdealClass_ker_iff F (principalIdele F g)).mpr ⟨g, 1, by simp⟩)

private theorem ideleClassToIdealClass_apply (g : Idele F) :
    ideleClassToIdealClass F (ideleClassMap F g) = ideleIdealClass F g := rfl

/-- A character of the ordinary ideal class group pulled back to idele classes. -/
def classGroupIdeleCharacter (ψ : IdealClass F →* Circle) : PontryaginDual (IdeleClass F) where
  toMonoidHom := ψ.comp (ideleClassToIdealClass F)
  continuous_toFun := by
    letI : TopologicalSpace (IdealClass F) := ⊥
    letI : DiscreteTopology (IdealClass F) := ⟨rfl⟩
    have h : Continuous (ideleClassToIdealClass F) := by
      apply (QuotientGroup.isQuotientMap_mk (principalIdeles F)).continuous_iff.mpr
      exact ideleIdealClass_continuous F
    exact (continuous_of_discreteTopology (f := ψ)).comp h

private theorem singleFiniteIdele_order (v w : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    ideleOrder F (singleFiniteIdele F v u) w =
      if w = v then -WithZero.log (Valued.v ((u : v.adicCompletion F))) else 0 := by
  classical
  by_cases h : w = v
  · subst w
    simp only [ite_true]
    change -WithZero.log (Valued.v (Function.update
      (fun w : HeightOneSpectrum (𝓞 F) ↦ (1 : w.adicCompletion F)) v u.val v)) = _
    rw [Function.update_self]
  · have he : (singleFiniteIdele F v u).val.2 w = 1 := by
      change Function.update (fun w : HeightOneSpectrum (𝓞 F) ↦ (1 : w.adicCompletion F)) v
        u.val w = 1
      rw [Function.update_of_ne h]
    simp [ideleOrder, h, he]

private def primeNonzeroIdeal (v : HeightOneSpectrum (𝓞 F)) : NonzeroIdeals F :=
  ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩

private theorem singleFiniteUniformizer_idealClass (v : HeightOneSpectrum (𝓞 F)) :
    ideleIdealClass F (singleFiniteIdele F v (chosenFiniteUniformizer F v)) =
      ClassGroup.mk0 (primeNonzeroIdeal F v) := by
  classical
  have hπ : -WithZero.log (Valued.v ((chosenFiniteUniformizer F v).val)) = 1 := by
    have hu : Valued.v (chosenFiniteUniformizer F v).val = WithZero.exp (-1 : ℤ) :=
      (chosenFiniteUniformizer_spec F v).trans
        (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
          (HeightOneSpectrum.valuedAdicCompletion_surjective F v)))
    rw [hu, WithZero.log_exp, neg_neg]
  have hfrac : ideleFractionalIdeal F (singleFiniteIdele F v (chosenFiniteUniformizer F v)) =
      FractionalIdeal.mk0 F (primeNonzeroIdeal F v) := by
    apply Units.ext
    change (∏ᶠ w : HeightOneSpectrum (𝓞 F), (w.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^
      ideleOrder F (singleFiniteIdele F v (chosenFiniteUniformizer F v)) w) =
      (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F)
    rw [finprod_eq_single _ v]
    · rw [singleFiniteIdele_order, ite_eq_left rfl, hπ, zpow_one]
    · intro w hw
      rw [singleFiniteIdele_order, ite_eq_right hw, zpow_zero]
  change ClassGroup.mk F _ = _
  rw [hfrac, ClassGroup.mk_mk0]

private theorem classGroupIdeleCharacter_unramified (ψ : IdealClass F →* Circle)
    (v : HeightOneSpectrum (𝓞 F)) : unramifiedFiniteCharacter F (classGroupIdeleCharacter F ψ) v := by
  intro u hu
  have hval := (finiteCompletion_norm_eq_one_iff F v u).mp hu
  have hdiv : singleFiniteIdele F v u ∈ (ideleDivisor F).ker := by
    change ideleDivisor F (singleFiniteIdele F v u) = 1
    apply Finsupp.ext
    intro w
    change ideleOrder F (singleFiniteIdele F v u) w = 0
    by_cases hw : w = v <;> simp [singleFiniteIdele_order, hw, hval]
  have hfrac := (ideleFractionalIdeal_ker_eq F).symm ▸ hdiv
  have hc : ideleIdealClass F (singleFiniteIdele F v u) = 1 := by
    change ClassGroup.mk F (ideleFractionalIdeal F (singleFiniteIdele F v u)) = 1
    rw [show ideleFractionalIdeal F (singleFiniteIdele F v u) = 1 from hfrac, map_one]
  change ψ (ideleClassToIdealClass F (ideleClassMap F (singleFiniteIdele F v u))) = 1
  rw [ideleClassToIdealClass_apply, hc, map_one]

/-- The unramified Hecke ideal weight agrees with the ordinary class-group character. -/
theorem finiteHeckeIdealWeight_classGroup (ψ : IdealClass F →* Circle) (I : NonzeroIdeals F) :
    finiteHeckeIdealWeight F (classGroupIdeleCharacter F ψ) I.val = (ψ (ClassGroup.mk0 I) : ℂ) := by
  classical
  have hI : I.val ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.property
  unfold finiteHeckeIdealWeight
  rw [ite_eq_right hI]
  let d (v : HeightOneSpectrum (𝓞 F)) := primeNonzeroIdeal F v ^
    Multiset.count v.asIdeal (normalizedFactors I.val)
  have hd (v : HeightOneSpectrum (𝓞 F)) : (d v).val = v.maxPowDividing I.val := by
    rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count v hI]
    rfl
  let i := (nonZeroDivisors (Ideal (𝓞 F))).subtype
  have hdf : HasFiniteMulSupport d := by
    apply (Ideal.hasFiniteMulSupport hI).subset
    intro v hv
    exact fun h ↦ hv (Subtype.ext (by simpa [hd] using h))
  have hP : (∏ᶠ v, d v) = I := by
    apply Subtype.ext
    change i (∏ᶠ v, d v) = I.val
    rw [map_finprod i hdf]
    exact (finprod_congr hd).trans (Ideal.finprod_heightOneSpectrum_factorization hI)
  let a : NonzeroIdeals F →* ℂ := Circle.coeHom.comp (ψ.comp ClassGroup.mk0)
  rw [← show a (∏ᶠ v, d v) = (ψ (ClassGroup.mk0 I) : ℂ) from congrArg a hP, map_finprod a hdf]
  apply finprod_congr
  intro v
  rw [heckeEulerCoefficient, ite_eq_left (classGroupIdeleCharacter_unramified F ψ v)]
  change (ψ (ideleClassToIdealClass F (ideleClassMap F
    (singleFiniteIdele F v (chosenFiniteUniformizer F v)))) : ℂ) ^ _ = a (d v)
  rw [ideleClassToIdealClass_apply, singleFiniteUniformizer_idealClass]
  symm
  exact map_pow a _ _

theorem classGroupIdeleCharacter_nontrivial_normOne
    (ψ : IdealClass F →* Circle) (hψ : ψ ≠ 1) :
    ∃ k : normOneIdeleClass F, classGroupIdeleCharacter F ψ k.val ≠ 1 := by
  by_contra! h
  apply hψ
  apply DFunLike.ext
  intro c
  obtain ⟨a, ha⟩ := ideleNormOne_idealClass_surjective F c
  let k : normOneIdeleClass F := ⟨ideleClassMap F a.val, a.property⟩
  have he := h k
  change ψ (ideleClassToIdealClass F (ideleClassMap F a.val)) = 1 at he
  rw [ideleClassToIdealClass_apply, show ideleIdealClass F a.val = c from ha] at he
  exact he

theorem classGroupIdeleCharacter_idealSummatory_tendsto_zero
    (ψ : IdealClass F →* Circle) (hψ : ψ ≠ 1) :
    Tendsto (fun x : ℝ ↦ finiteHeckeIdealSummatory F (classGroupIdeleCharacter F ψ) x / x)
      atTop (𝓝 0) :=
  finiteHeckeIdealSummatory_tendsto_zero_of_classCharacter F _ ψ hψ
    (finiteHeckeIdealWeight_classGroup F ψ)

end IdealClassCancellation

end
end Masullo
