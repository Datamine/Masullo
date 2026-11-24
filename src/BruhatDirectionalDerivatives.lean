import ElementaryDirectionalDerivatives
import StructuralPairs

open Filter Function Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

namespace LCAStructuralPair

abbrev StageQuotient (P : LCAStructuralPair G) :=
  P.upper.val ⧸ P.kernel.comap P.upper.val.subtype

/-- The quotient homomorphism written in a choice of elementary presentation. -/
def stageCoordinates (P : LCAStructuralPair G) (p : ElementaryLCAPresentation P.StageQuotient) :
    P.upper.val →ₜ* Multiplicative (ElementaryLCAModel p.realDim p.torusDim p.latticeRank p.finiteFactor) :=
  (⟨p.equiv.toMulEquiv.toMonoidHom, p.equiv.continuous⟩ : P.StageQuotient →ₜ* _).comp
    ⟨QuotientGroup.mk' (P.kernel.comap P.upper.val.subtype), QuotientGroup.continuous_mk⟩

/-- Any structural kernel fits in a structural upper subgroup containing the chosen point. -/
theorem exists_same_kernel_contains (P : LCAStructuralPair G) (x : G) :
    ∃ Q : LCAStructuralPair G, Q.kernel = P.kernel ∧ x ∈ Q.upper.val := by
  have hk : IsCompact (P.kernel : Set G) := by
    rw [← lcaDualAnnihilator_annihilator P.kernel P.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ P.annihilator_open
  obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains
    (isCompact_singleton.union hk : IsCompact ({x} ∪ (P.kernel : Set G)))
  exact ⟨⟨H, P.kernel, P.kernel_closed, P.annihilator_open,
    P.annihilator_compactlyGenerated, fun _ hx ↦ hH (Or.inr hx)⟩, rfl, hH (Or.inl rfl)⟩

omit [T2Space G] [LocallyCompactSpace G] in
/-- Connectedness of the real parameter forces a one-parameter subgroup into
every open subgroup containing the identity. -/
theorem oneParameter_mem_upper (P : LCAStructuralPair G) (c : Multiplicative ℝ →ₜ* G) (t : ℝ) :
    c (Multiplicative.ofAdd t) ∈ P.upper.val := by
  let u : ℝ → G := c ∘ Multiplicative.ofAdd
  have hu : Continuous u := c.continuous.comp continuous_ofAdd
  have hClopen : IsClopen (u ⁻¹' (P.upper.val : Set G)) :=
    ⟨(P.upper.val.isClosed_of_isOpen P.upper.property.1).preimage hu,
      P.upper.property.1.preimage hu⟩
  have hZero : 0 ∈ u ⁻¹' (P.upper.val : Set G) := by
    change c 1 ∈ P.upper.val
    rw [map_one]
    exact P.upper.val.one_mem
  have h := hClopen.eq_univ ⟨0, hZero⟩
  show t ∈ u ⁻¹' (P.upper.val : Set G)
  rw [h]
  exact mem_univ _

def restrictOneParameter (P : LCAStructuralPair G) (c : Multiplicative ℝ →ₜ* G) :
    Multiplicative ℝ →ₜ* P.upper.val :=
  ⟨c.toMonoidHom.codRestrict P.upper.val (fun t ↦ P.oneParameter_mem_upper c t.toAdd),
    c.continuous.subtype_mk _⟩

end LCAStructuralPair

/-- Definition D.1.5.3(1). A single good kernel fixes the function, and all
structural quotients with that kernel give the indicated differentiability.
The quotient regularity is tested in elementary coordinates on every fibre. -/
def IsBruhatContDiff (s : ℕ) (f : G → ℂ) : Prop :=
  ∃ P : LCAStructuralPair G, (∀ k : P.kernel, ∀ x, f (k.val * x) = f x) ∧
    ∀ (Q : LCAStructuralPair G), Q.kernel = P.kernel →
      ∀ p : ElementaryLCAPresentation Q.StageQuotient,
        ∃ h : ElementaryLCAModel p.realDim p.torusDim p.latticeRank p.finiteFactor → ℂ,
          (∀ x : Q.upper.val, h (Q.stageCoordinates p x).toAdd = f x.val) ∧
          ∀ a b, ContDiff ℝ s (fun u ↦ h (elementaryCover u a b))

/-- First-order Bruhat differentiation along the supplied one-parameter subgroup. -/
def bruhatOrbitDeriv (c : Multiplicative ℝ →ₜ* G) (f : G → ℂ) (x : G) : ℂ :=
  deriv (fun t : ℝ ↦ f (x * c (Multiplicative.ofAdd t))) 0

/-- Directional differentiation preserves support in an open structural upper
subgroup, since the orbit stays in the same coset. -/
theorem bruhatOrbitDeriv_support_subset (P : LCAStructuralPair G)
    (c : Multiplicative ℝ →ₜ* G) (f : G → ℂ) (hf : support f ⊆ P.upper.val) :
    support (bruhatOrbitDeriv c f) ⊆ P.upper.val := by
  intro x hx
  by_contra h
  have he : (fun t : ℝ ↦ f (x * c (Multiplicative.ofAdd t))) = fun _ ↦ 0 := by
    funext t
    by_contra hn
    have hm := hf (show x * c (Multiplicative.ofAdd t) ∈ support f from hn)
    have hmul := P.upper.val.mul_mem hm (P.upper.val.inv_mem (P.oneParameter_mem_upper c t))
    apply h
    change x ∈ P.upper.val
    simpa only [mul_inv_cancel_right] using hmul
  have hn : bruhatOrbitDeriv c f x ≠ 0 := hx
  apply hn
  simp [bruhatOrbitDeriv, he]

omit [T2Space G] [LocallyCompactSpace G] in
theorem bruhatOrbitDeriv_stage (c : Multiplicative ℝ →ₜ* G) (f : G → ℂ)
    (Q : LCAStructuralPair G) (p : ElementaryLCAPresentation Q.StageQuotient)
    (h : ElementaryLCAModel p.realDim p.torusDim p.latticeRank p.finiteFactor → ℂ)
    (hh : ∀ x : Q.upper.val, h (Q.stageCoordinates p x).toAdd = f x.val) (x : Q.upper.val) :
    bruhatOrbitDeriv c f x.val =
      elementaryOrbitDeriv ((Q.stageCoordinates p).comp (Q.restrictOneParameter c)) h
        (Q.stageCoordinates p x).toAdd := by
  unfold bruhatOrbitDeriv elementaryOrbitDeriv
  congr 1
  funext t
  let y := Q.restrictOneParameter c (Multiplicative.ofAdd t)
  have he := hh (x * y)
  rw [map_mul] at he
  exact he.symm

/-- The derivative is defined at every point and lowers quotient regularity by one
while keeping the same good kernel. -/
theorem bruhatOrbitDeriv_regular (c : Multiplicative ℝ →ₜ* G) (f : G → ℂ) {s : ℕ}
    (hf : IsBruhatContDiff (s + 1) f) :
    IsBruhatContDiff s (bruhatOrbitDeriv c f) ∧
      ∀ x, HasDerivAt (fun t : ℝ ↦ f (x * c (Multiplicative.ofAdd t)))
        (bruhatOrbitDeriv c f x) 0 := by
  obtain ⟨P, hInv, hStage⟩ := hf
  constructor
  · refine ⟨P, ?_, fun Q hQ p ↦ ?_⟩
    · intro k x
      unfold bruhatOrbitDeriv
      congr 1
      funext t
      rw [mul_assoc, hInv]
    · obtain ⟨h, hh, hReg⟩ := hStage Q hQ p
      let a := (Q.stageCoordinates p).comp (Q.restrictOneParameter c)
      exact ⟨elementaryOrbitDeriv a h, fun x ↦ (bruhatOrbitDeriv_stage c f Q p h hh x).symm,
        elementaryOrbitDeriv_contDiff a h hReg⟩
  · intro x
    obtain ⟨Q, hQ, hx⟩ := P.exists_same_kernel_contains x
    obtain ⟨p⟩ := Q.quotient_elementary
    obtain ⟨h, hh, hReg⟩ := hStage Q hQ p
    let x₀ : Q.upper.val := ⟨x, hx⟩
    let a := (Q.stageCoordinates p).comp (Q.restrictOneParameter c)
    have hSmooth d b := (hReg d b).differentiable
      (by exact_mod_cast Nat.succ_ne_zero s)
    have hd := elementaryOrbit_hasDerivAt a h hSmooth (Q.stageCoordinates p x₀).toAdd
    rw [← bruhatOrbitDeriv_stage c f Q p h hh x₀] at hd
    convert hd using 1
    funext t
    have he := hh (x₀ * Q.restrictOneParameter c (Multiplicative.ofAdd t))
    rw [map_mul] at he
    exact he.symm

/-- Fibrewise continuity on all quotients for the same kernel implies global
continuity, by covering the group by its open upper subgroups. -/
theorem IsBruhatContDiff.continuous {f : G → ℂ} (hf : IsBruhatContDiff 0 f) :
    Continuous f := by
  obtain ⟨P, _, hStage⟩ := hf
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  obtain ⟨Q, hQ, hx⟩ := P.exists_same_kernel_contains x
  obtain ⟨p⟩ := Q.quotient_elementary
  obtain ⟨h, hh, hReg⟩ := hStage Q hQ p
  have hc := elementary_continuous_of_fibres h (fun a b ↦ (hReg a b).continuous)
  have hsub : Continuous (fun y : Q.upper.val ↦ f y.val) := by
    have he : (fun y : Q.upper.val ↦ f y.val) =
        h ∘ (Multiplicative.toAdd ∘ Q.stageCoordinates p) := funext fun y ↦ (hh y).symm
    rw [he]
    exact hc.comp (continuous_toAdd.comp (Q.stageCoordinates p).continuous)
  have hon := continuousOn_iff_continuous_domRestrict.mpr hsub
  exact hon.continuousAt (Q.upper.property.1.mem_nhds hx)

/-- Lemma D.1.6.6. The first-order derivative is continuous on Bruhat C¹
functions, preserves smoothness at all orders, and satisfies the product rule. -/
theorem bruhatOrbitDeriv_properties (c : Multiplicative ℝ →ₜ* G) :
    (∀ f : G → ℂ, IsBruhatContDiff 1 f → Continuous (bruhatOrbitDeriv c f)) ∧
    (∀ f : G → ℂ, (∀ s, IsBruhatContDiff s f) → ∀ s, IsBruhatContDiff s (bruhatOrbitDeriv c f)) ∧
    ∀ f g : G → ℂ, IsBruhatContDiff 1 f → IsBruhatContDiff 1 g →
      bruhatOrbitDeriv c (f * g) = f * bruhatOrbitDeriv c g + g * bruhatOrbitDeriv c f := by
  refine ⟨fun f hf ↦ (bruhatOrbitDeriv_regular c f (s := 0) hf).1.continuous,
    fun f hf s ↦ (bruhatOrbitDeriv_regular c f (hf (s + 1))).1, ?_⟩
  intro f g hf hg
  funext x
  have hd := ((bruhatOrbitDeriv_regular c f (s := 0) hf).2 x).mul
    ((bruhatOrbitDeriv_regular c g (s := 0) hg).2 x)
  have hz : x * c (Multiplicative.ofAdd (0 : ℝ)) = x := by
    change x * c 1 = x
    rw [map_one, mul_one]
  simpa only [bruhatOrbitDeriv, Pi.mul_def, Pi.add_apply, hz, mul_comm, add_comm] using hd.deriv

namespace LCAStructuralPair

/-- Inclusions of both upper groups and kernels induce continuous maps of
the structural quotients. -/
def stageMap (Q P : LCAStructuralPair G)
    (hu : Q.upper.val ≤ P.upper.val) (hk : Q.kernel ≤ P.kernel) :
    Q.StageQuotient →ₜ* P.StageQuotient := by
  let l : Q.upper.val →ₜ* P.StageQuotient :=
    ⟨(QuotientGroup.mk' _).comp (Subgroup.inclusion hu),
      QuotientGroup.continuous_mk.comp (continuous_subtype_val.subtype_mk _)⟩
  have hker : Q.kernel.comap Q.upper.val.subtype ≤ l.toMonoidHom.ker := by
    intro x hx
    change QuotientGroup.mk (Subgroup.inclusion hu x) = (1 : P.StageQuotient)
    exact (QuotientGroup.eq_one_iff _).mpr (hk hx)
  exact ⟨QuotientGroup.lift _ l.toMonoidHom hker,
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr l.continuous⟩

@[simp] theorem stageMap_mk (Q P : LCAStructuralPair G)
    (hu : Q.upper.val ≤ P.upper.val) (hk : Q.kernel ≤ P.kernel) (x : Q.upper.val) :
    Q.stageMap P hu hk (QuotientGroup.mk x) =
      QuotientGroup.mk (Subgroup.inclusion hu x) := rfl

/-- The map of structural quotients in chosen elementary coordinates. -/
def stageCoordinateMap (Q P : LCAStructuralPair G)
    (hu : Q.upper.val ≤ P.upper.val) (hk : Q.kernel ≤ P.kernel)
    (p : ElementaryLCAPresentation Q.StageQuotient) (q : ElementaryLCAPresentation P.StageQuotient) :
    Multiplicative (ElementaryLCAModel p.realDim p.torusDim p.latticeRank p.finiteFactor) →ₜ*
      Multiplicative (ElementaryLCAModel q.realDim q.torusDim q.latticeRank q.finiteFactor) :=
  (⟨q.equiv.toMulEquiv.toMonoidHom, q.equiv.continuous⟩ : P.StageQuotient →ₜ* _).comp
    ((Q.stageMap P hu hk).comp ⟨p.equiv.symm.toMulEquiv.toMonoidHom, p.equiv.symm.continuous⟩)

@[simp] theorem stageCoordinateMap_stageCoordinates (Q P : LCAStructuralPair G)
    (hu : Q.upper.val ≤ P.upper.val) (hk : Q.kernel ≤ P.kernel)
    (p : ElementaryLCAPresentation Q.StageQuotient) (q : ElementaryLCAPresentation P.StageQuotient)
    (x : Q.upper.val) :
    Q.stageCoordinateMap P hu hk p q (Q.stageCoordinates p x) =
      P.stageCoordinates q (Subgroup.inclusion hu x) := by
  change q.equiv (Q.stageMap P hu hk (p.equiv.symm (p.equiv (QuotientGroup.mk x)))) =
    q.equiv (QuotientGroup.mk (Subgroup.inclusion hu x))
  rw [p.equiv.symm_apply_apply, stageMap_mk]


end LCAStructuralPair

private theorem bruhatContDiff_refineKernel {s : ℕ} {f : G → ℂ}
    (P : LCAStructuralPair G)
    (hStage : ∀ (Q : LCAStructuralPair G), Q.kernel = P.kernel →
      ∀ p : ElementaryLCAPresentation Q.StageQuotient,
        ∃ h : ElementaryLCAModel p.realDim p.torusDim p.latticeRank p.finiteFactor → ℂ,
          (∀ x : Q.upper.val, h (Q.stageCoordinates p x).toAdd = f x.val) ∧
          ∀ a b, ContDiff ℝ s (fun u ↦ h (elementaryCover u a b)))
    (Q : LCAStructuralPair G) (hk : Q.kernel ≤ P.kernel)
    (p : ElementaryLCAPresentation Q.StageQuotient) :
    ∃ h : ElementaryLCAModel p.realDim p.torusDim p.latticeRank p.finiteFactor → ℂ,
      (∀ x : Q.upper.val, h (Q.stageCoordinates p x).toAdd = f x.val) ∧
      ∀ a b, ContDiff ℝ s (fun u ↦ h (elementaryCover u a b)) := by
  letI := (openCompactlyGeneratedSubgroups_colimit (G := G)).1
  obtain ⟨J, hQJ, hPJ⟩ := exists_ge_ge Q.upper P.upper
  let R : LCAStructuralPair G :=
    ⟨J, P.kernel, P.kernel_closed, P.annihilator_open, P.annihilator_compactlyGenerated,
      P.kernel_le.trans hPJ⟩
  obtain ⟨q⟩ := R.quotient_elementary
  obtain ⟨h, hh, hc⟩ := hStage R rfl q
  let φ := Q.stageCoordinateMap R hQJ hk p q
  refine ⟨h ∘ φ.toMonoidHom.toAdditive, fun x ↦ ?_,
    elementaryContDiff_hom φ.toMonoidHom.toAdditive φ.continuous h hc⟩
  change h (φ (Q.stageCoordinates p x)).toAdd = f x.val
  dsimp only [φ]
  rw [Q.stageCoordinateMap_stageCoordinates]
  exact hh (Subgroup.inclusion hQJ x)

/-- Bruhat regularity of the same order is closed under addition. -/
theorem IsBruhatContDiff.add {s : ℕ} {f g : G → ℂ}
    (hf : IsBruhatContDiff s f) (hg : IsBruhatContDiff s g) :
    IsBruhatContDiff s (f + g) := by
  letI := (lcaStructuralPairs_filtered (G := G)).2
  obtain ⟨P, hi, hs⟩ := hf
  obtain ⟨Q, hj, ht⟩ := hg
  obtain ⟨R, hPR, hQR⟩ := exists_ge_ge P Q
  have hRP : R.kernel ≤ P.kernel := hPR.2
  have hRQ : R.kernel ≤ Q.kernel := hQR.2
  refine ⟨R, fun k x ↦ ?_, fun S hk p ↦ ?_⟩
  · exact congrArg₂ (· + ·) (hi ⟨k.val, hRP k.property⟩ x) (hj ⟨k.val, hRQ k.property⟩ x)
  · obtain ⟨u, hu, hu'⟩ := bruhatContDiff_refineKernel P hs S (hk ▸ hRP) p
    obtain ⟨v, hv, hv'⟩ := bruhatContDiff_refineKernel Q ht S (hk ▸ hRQ) p
    exact ⟨u + v, fun x ↦ congrArg₂ (· + ·) (hu x) (hv x), fun a b ↦ (hu' a b).add (hv' a b)⟩

/-- Scalar multiplication preserves the same quotient regularity. -/
theorem IsBruhatContDiff.smul {s : ℕ} {f : G → ℂ} (hf : IsBruhatContDiff s f) (c : ℂ) :
    IsBruhatContDiff s (c • f) := by
  obtain ⟨P, hi, hs⟩ := hf
  refine ⟨P, fun k x ↦ congrArg (c • ·) (hi k x), fun Q hk p ↦ ?_⟩
  obtain ⟨u, hu, hu'⟩ := hs Q hk p
  exact ⟨c • u, fun x ↦ congrArg (c • ·) (hu x), fun a b ↦ (hu' a b).const_smul c⟩

/-- Complex vector space of functions smooth to every finite order in the
sense of D.1.5.3. -/
def bruhatSmoothSubmodule : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ s, IsBruhatContDiff s f}
  zero_mem' := by
    intro s
    let ⟨P⟩ := (lcaStructuralPairs_filtered (G := G)).1
    exact ⟨P, fun _ _ ↦ rfl, fun _ _ _ ↦ ⟨0, fun _ ↦ rfl, fun _ _ ↦ contDiff_const⟩⟩
  add_mem' hf hg s := (hf s).add (hg s)
  smul_mem' c _ hf s := (hf s).smul c

/-- The first-order derivative is a complex-linear endomorphism of smooth
Bruhat functions. -/
def bruhatFirstOrder (c : Multiplicative ℝ →ₜ* G) : Module.End ℂ (bruhatSmoothSubmodule (G := G)) where
  toFun f := ⟨bruhatOrbitDeriv c f.val, fun s ↦ (bruhatOrbitDeriv_regular c f.val (f.property (s + 1))).1⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact (((bruhatOrbitDeriv_regular c f.val (s := 0) (f.property 1)).2 x).add
      ((bruhatOrbitDeriv_regular c g.val (s := 0) (g.property 1)).2 x)).deriv
  map_smul' d f := by
    apply Subtype.ext
    funext x
    exact (((bruhatOrbitDeriv_regular c f.val (s := 0) (f.property 1)).2 x).const_smul d).deriv


/-- An elementary character restricted to the covering vector group has a real
linear phase. -/
theorem elementaryCharacter_phase {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (χ : PontryaginDual (Multiplicative (ElementaryLCAModel m n r F))) :
    ∃ L : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ,
      ∀ x, χ (Multiplicative.ofAdd (elementaryCoverHom x)) = Circle.exp (L x) := by
  let A := ElementaryLCAModel m n r F
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let q : X →+ A := elementaryCoverHom
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hE (a b : AddCircle (1 : ℝ)) : e (a + b) = e a * e b := by
    simp only [e, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_add]
  let c : X →+ AddCircle (1 : ℝ) :=
    { toFun := fun x ↦ e.symm (χ (Multiplicative.ofAdd (q x)))
      map_zero' := by
        apply e.injective
        rw [e.apply_symm_apply]
        change χ (Multiplicative.ofAdd (q 0)) = e 0
        rw [map_zero, show Multiplicative.ofAdd (0 : A) = 1 from rfl, map_one]
        simp [e, AddCircle.homeomorphCircle_apply]
      map_add' := fun x y ↦ by
        apply e.injective
        rw [hE, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
        change χ (Multiplicative.ofAdd (q (x + y))) =
          χ (Multiplicative.ofAdd (q x)) * χ (Multiplicative.ofAdd (q y))
        rw [map_add]
        exact map_mul χ _ _ }
  have hc : Continuous c :=
    e.symm.continuous.comp (χ.continuous.comp (continuous_ofAdd.comp elementaryCoverHom_continuous))
  obtain ⟨L, hL, hLift⟩ := exists_addCircle_addMonoidHom_lift c hc
  refine ⟨(2 * Real.pi) • (L.toRealLinearMap hL).toContinuousLinearMap, fun x ↦ ?_⟩
  change χ (Multiplicative.ofAdd (q x)) = Circle.exp (2 * Real.pi * L x)
  have h := congrArg e (hLift x)
  change e (L x : AddCircle (1 : ℝ)) = e (e.symm (χ (Multiplicative.ofAdd (q x)))) at h
  rw [e.apply_symm_apply, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
    div_one] at h
  exact h.symm

theorem elementaryCharacter_smooth {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (χ : PontryaginDual (Multiplicative (ElementaryLCAModel m n r F))) :
    ∀ a b, ContDiff ℝ ∞ (fun x ↦ (χ (Multiplicative.ofAdd (elementaryCover x a b)) : ℂ)) := by
  obtain ⟨L, hL⟩ := elementaryCharacter_phase χ
  intro a b
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  have he : (fun x : X ↦ (χ (Multiplicative.ofAdd (elementaryCover x a b)) : ℂ)) =
      fun x ↦ (χ (Multiplicative.ofAdd (elementaryCover (0 : X) a b)) : ℂ) *
        Complex.exp ((L x : ℂ) * Complex.I) := by
    funext x
    have h := elementaryCover_add (0 : X) x a b
    rw [zero_add] at h
    rw [h, show Multiplicative.ofAdd (elementaryCover (0 : X) a b + elementaryCoverHom x) =
      Multiplicative.ofAdd (elementaryCover (0 : X) a b) *
        Multiplicative.ofAdd (elementaryCoverHom x) from rfl,
      map_mul, Circle.coe_mul, hL, Circle.coe_exp]
  rw [he]
  exact contDiff_const.mul (((Complex.ofRealCLM.contDiff.comp L.contDiff).mul contDiff_const).cexp)

/-- Continuous unitary characters are smooth Bruhat functions. A good kernel
contained in the character kernel gives smooth elementary quotient profiles. -/
theorem pontryaginDual_mem_bruhatSmooth (χ : PontryaginDual G) :
    (fun x ↦ (χ x : ℂ)) ∈ bruhatSmoothSubmodule (G := G) := by
  obtain ⟨H, hχ⟩ := (openCompactlyGeneratedSubgroups_colimit (G := PontryaginDual G)).2.1 χ
  obtain ⟨J, hJ⟩ := exists_openCompactlyGeneratedSubgroup_contains
    (isCompact_lcaDualAnnihilator_of_isOpen H.val H.property.1)
  let P := LCAStructuralPair.ofDual J H hJ
  have hK (k : P.kernel) : χ k.val = 1 :=
    (mem_lcaDualAnnihilator_iff H.val k.val).mp k.property ⟨χ, hχ⟩
  intro s
  refine ⟨P, fun k x ↦ ?_, fun Q hQ p ↦ ?_⟩
  · change (χ (k.val * x) : ℂ) = (χ x : ℂ)
    rw [map_mul, hK, one_mul]
  · let χQ : Q.upper.val →* Circle := χ.toMonoidHom.comp Q.upper.val.subtype
    have hker : Q.kernel.comap Q.upper.val.subtype ≤ χQ.ker := by
      intro x hx
      have hx' : (x : G) ∈ Q.kernel := hx
      rw [hQ] at hx'
      exact hK ⟨x.val, hx'⟩
    let χ₀ : Q.StageQuotient →ₜ* Circle :=
      ⟨QuotientGroup.lift _ χQ hker,
        (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
          (χ.continuous.comp continuous_subtype_val)⟩
    let χ₁ : PontryaginDual (Multiplicative (ElementaryLCAModel p.realDim p.torusDim p.latticeRank
        p.finiteFactor)) :=
      χ₀.comp ⟨p.equiv.symm.toMulEquiv.toMonoidHom, p.equiv.symm.continuous⟩
    refine ⟨fun x ↦ (χ₁ (Multiplicative.ofAdd x) : ℂ), fun x ↦ ?_,
      fun a b ↦ (elementaryCharacter_smooth χ₁ a b).of_le (by
        exact_mod_cast (le_top : (s : ℕ∞) ≤ ⊤))⟩
    change (χ₀ (p.equiv.symm (p.equiv (QuotientGroup.mk x))) : ℂ) = χ x.val
    rw [p.equiv.symm_apply_apply]
    rfl


/-- Scalar multiplication on real one-parameter subgroups is reparametrization. -/
def realParameterScale (b : ℝ) : Multiplicative ℝ →ₜ* Multiplicative ℝ :=
  ⟨(b • LinearMap.id (R := ℝ) (M := ℝ)).toAddMonoidHom.toMultiplicative,
    continuous_const_mul b⟩

theorem bruhatFirstOrder_scale (b : ℝ) (c : Multiplicative ℝ →ₜ* G) :
    bruhatFirstOrder (c.comp (realParameterScale b)) = b • bruhatFirstOrder c := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  have h := (bruhatOrbitDeriv_regular c f.val (s := 0) (f.property 1)).2 x
  have hz : b * (0 : ℝ) = 0 := mul_zero _
  have hscaled : HasDerivAt (fun t : ℝ ↦ f.val (x * c (Multiplicative.ofAdd (b * t))))
      (b • bruhatOrbitDeriv c f.val x) 0 := by
    have hh : HasDerivAt (fun t : ℝ ↦ f.val (x * c (Multiplicative.ofAdd t)))
        (bruhatOrbitDeriv c f.val x) (b * 0) := hz.symm ▸ h
    simpa only [Function.comp_def, mul_one] using
      hh.scomp (0 : ℝ) ((hasDerivAt_id' (0 : ℝ)).const_mul b)
  exact hscaled.deriv

/-- Differentiation of the product one-parameter subgroup gives the sum
of the two first-order endomorphisms. -/
theorem bruhatFirstOrder_mul (c d : Multiplicative ℝ →ₜ* G) :
    bruhatFirstOrder (c * d) = bruhatFirstOrder c + bruhatFirstOrder d := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  obtain ⟨P, _, hP⟩ := f.property 1
  obtain ⟨Q, hQ, hx⟩ := P.exists_same_kernel_contains x
  obtain ⟨p⟩ := Q.quotient_elementary
  obtain ⟨h, hh, hs⟩ := hP Q hQ p
  let x₀ : Q.upper.val := ⟨x, hx⟩
  let q := Q.stageCoordinates p
  let a := q.comp (Q.restrictOneParameter c)
  let b := q.comp (Q.restrictOneParameter d)
  have hab : q.comp (Q.restrictOneParameter (c * d)) = a * b := by
    apply ContinuousMonoidHom.ext
    intro t
    change q (Q.restrictOneParameter c t * Q.restrictOneParameter d t) = q _ * q _
    exact map_mul q _ _
  change bruhatOrbitDeriv (c * d) f.val x =
    bruhatOrbitDeriv c f.val x + bruhatOrbitDeriv d f.val x
  rw [bruhatOrbitDeriv_stage (c * d) f.val Q p h hh x₀,
    bruhatOrbitDeriv_stage c f.val Q p h hh x₀, bruhatOrbitDeriv_stage d f.val Q p h hh x₀, hab]
  obtain ⟨v, hv⟩ := elementaryOneParameter_lift a
  obtain ⟨w, hw⟩ := elementaryOneParameter_lift b
  have hp t : ((a * b) (Multiplicative.ofAdd t)).toAdd = elementaryCoverHom (t • (v + w)) := by
    change (a (Multiplicative.ofAdd t)).toAdd + (b (Multiplicative.ofAdd t)).toAdd = _
    rw [hv, hw, smul_add, map_add]
  let e := (q x₀).toAdd
  obtain ⟨z, hz⟩ := elementaryCover_surjective e.2.2.1 e.2.2.2 e.1 e.2.1
  change elementaryCover (e.1, z) e.2.2.1 e.2.2.2 = e at hz
  change elementaryOrbitDeriv (a * b) h e = elementaryOrbitDeriv a h e + elementaryOrbitDeriv b h e
  rw [← hz]
  have hDiff := ((hs e.2.2.1 e.2.2.2).differentiable (by norm_num)).differentiableAt
    (x := (e.1, z))
  rw [elementaryOrbitDeriv_cover _ _ hp _ _ _ _ hDiff,
    elementaryOrbitDeriv_cover _ _ hv _ _ _ _ hDiff,
    elementaryOrbitDeriv_cover _ _ hw _ _ _ _ hDiff, map_add]


/-- First-order differentiation commutes with translation as an identity of functions. -/
theorem bruhatOrbitDeriv_translate (c : Multiplicative ℝ →ₜ* G) (g : G) (f : G → ℂ) :
    bruhatOrbitDeriv c (fun x ↦ f (g * x)) = fun x ↦ bruhatOrbitDeriv c f (g * x) := by
  funext x
  simp only [bruhatOrbitDeriv, mul_assoc]

private theorem elementaryOrbitDeriv_comm {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (c d : Multiplicative ℝ →ₜ* Multiplicative (ElementaryLCAModel m n r F))
    (h : ElementaryLCAModel m n r F → ℂ)
    (hs : ∀ a b, ContDiff ℝ 2 (fun x ↦ h (elementaryCover x a b))) :
    elementaryOrbitDeriv c (elementaryOrbitDeriv d h) =
      elementaryOrbitDeriv d (elementaryOrbitDeriv c h) := by
  funext e
  obtain ⟨v, hv⟩ := elementaryOneParameter_lift c
  obtain ⟨w, hw⟩ := elementaryOneParameter_lift d
  obtain ⟨z, hz⟩ := elementaryCover_surjective e.2.2.1 e.2.2.2 e.1 e.2.1
  change elementaryCover (e.1, z) e.2.2.1 e.2.2.2 = e at hz
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let x : X := (e.1, z)
  let a := e.2.2.1
  let b := e.2.2.2
  let p : X → ℂ := fun y ↦ h (elementaryCover y a b)
  have hp : ContDiff ℝ 2 p := hs a b
  have hDiff := hp.differentiable (by norm_num)
  have hSecond := (hp.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hDeriv (c₁ c₂ : Multiplicative ℝ →ₜ* Multiplicative (ElementaryLCAModel m n r F))
      (v₁ v₂ : X)
      (h₁ : ∀ t : ℝ, (c₁ (Multiplicative.ofAdd t)).toAdd = elementaryCoverHom (t • v₁))
      (h₂ : ∀ t : ℝ, (c₂ (Multiplicative.ofAdd t)).toAdd = elementaryCoverHom (t • v₂)) :
      elementaryOrbitDeriv c₁ (elementaryOrbitDeriv c₂ h) (elementaryCover x a b) =
        fderiv ℝ (fderiv ℝ p) x v₁ v₂ := by
    have he : (fun y ↦ elementaryOrbitDeriv c₂ h (elementaryCover y a b)) =
        fun y ↦ fderiv ℝ p y v₂ := funext fun y ↦
      elementaryOrbitDeriv_cover c₂ v₂ h₂ h a b y hDiff.differentiableAt
    let ev := ContinuousLinearMap.apply ℝ ℂ v₂
    have hev := (ev.hasFDerivAt.comp x (hSecond x).hasFDerivAt)
    rw [elementaryOrbitDeriv_cover _ _ h₁ _ _ _ _ (by rw [he]; exact hev.differentiableAt), he]
    exact congrArg (fun L : X →L[ℝ] ℂ ↦ L v₁) hev.fderiv
  rw [← hz]
  change elementaryOrbitDeriv c (elementaryOrbitDeriv d h) (elementaryCover x a b) =
    elementaryOrbitDeriv d (elementaryOrbitDeriv c h) (elementaryCover x a b)
  rw [hDeriv c d v w hv hw, hDeriv d c w v hw hv]
  exact (hp.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq _ _

/-- The commutation clause in Lemma D.1.6.7 on the actual smooth function space. -/
theorem bruhatFirstOrder_comm (c d : Multiplicative ℝ →ₜ* G) :
    bruhatFirstOrder c * bruhatFirstOrder d = bruhatFirstOrder d * bruhatFirstOrder c := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  obtain ⟨P, _, hP⟩ := f.property 2
  obtain ⟨Q, hQ, hx⟩ := P.exists_same_kernel_contains x
  obtain ⟨p⟩ := Q.quotient_elementary
  obtain ⟨h, hh, hs⟩ := hP Q hQ p
  let x₀ : Q.upper.val := ⟨x, hx⟩
  let q := Q.stageCoordinates p
  let c₀ := q.comp (Q.restrictOneParameter c)
  let d₀ := q.comp (Q.restrictOneParameter d)
  change bruhatOrbitDeriv c (bruhatOrbitDeriv d f.val) x =
    bruhatOrbitDeriv d (bruhatOrbitDeriv c f.val) x
  rw [bruhatOrbitDeriv_stage c _ Q p (elementaryOrbitDeriv d₀ h)
      (fun y ↦ (bruhatOrbitDeriv_stage d f.val Q p h hh y).symm) x₀,
    bruhatOrbitDeriv_stage d _ Q p (elementaryOrbitDeriv c₀ h)
      (fun y ↦ (bruhatOrbitDeriv_stage c f.val Q p h hh y).symm) x₀]
  exact congrFun (elementaryOrbitDeriv_comm c₀ d₀ h hs) (q x₀).toAdd


private theorem elementaryContDiff_leftTranslate {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    {s : WithTop ℕ∞} (f : ElementaryLCAModel m n r F → ℂ)
    (hf : ∀ a b, ContDiff ℝ s (fun u ↦ f (elementaryCover u a b)))
    (g : ElementaryLCAModel m n r F) :
    ∀ a b, ContDiff ℝ s (fun u ↦ f (g + elementaryCover u a b)) := by
  obtain ⟨z, hz⟩ := elementaryCover_surjective g.2.2.1 g.2.2.2 g.1 g.2.1
  change elementaryCover (g.1, z) g.2.2.1 g.2.2.2 = g at hz
  intro a b
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let v : X := (g.1, z)
  have he : (fun u : X ↦ f (g + elementaryCover u a b)) =
      fun u ↦ f (elementaryCover (v + u) (g.2.2.1 + a) (g.2.2.2 + b)) := by
    funext u
    apply congrArg f
    conv_lhs => rw [← hz]
    exact Prod.ext rfl (Prod.ext (funext fun i ↦ (AddCircle.coe_add 1 (v.2 i) (u.2 i)).symm) rfl)
  rw [he]
  exact (hf _ _).comp (contDiff_const.add contDiff_id)

/-- The same good kernel witnesses the regularity of every left translate. -/
theorem IsBruhatContDiff.translate {s : ℕ} {f : G → ℂ}
    (hf : IsBruhatContDiff s f) (g : G) : IsBruhatContDiff s (fun x ↦ f (g * x)) := by
  obtain ⟨P, hi, hStage⟩ := hf
  obtain ⟨P', hp', hg'⟩ := P.exists_same_kernel_contains g
  letI := (openCompactlyGeneratedSubgroups_colimit (G := G)).1
  refine ⟨P, fun k x ↦ ?_, fun Q hQ p ↦ ?_⟩
  · change f (g * (k.val * x)) = f (g * x)
    rw [← mul_assoc, mul_comm g k.val, mul_assoc, hi]
  · obtain ⟨J, hQJ, hPJ⟩ := exists_ge_ge Q.upper P'.upper
    let R : LCAStructuralPair G :=
      ⟨J, Q.kernel, Q.kernel_closed, Q.annihilator_open, Q.annihilator_compactlyGenerated,
        Q.kernel_le.trans hQJ⟩
    obtain ⟨q⟩ := R.quotient_elementary
    obtain ⟨h, hh, hs⟩ := hStage R hQ q
    let g₀ : R.upper.val := ⟨g, hPJ hg'⟩
    let v := (R.stageCoordinates q g₀).toAdd
    let φ := Q.stageCoordinateMap R hQJ (le_refl Q.kernel) p q
    let u : ElementaryLCAModel p.realDim p.torusDim p.latticeRank p.finiteFactor →+
        ElementaryLCAModel q.realDim q.torusDim q.latticeRank q.finiteFactor :=
      φ.toMonoidHom.toAdditive
    refine ⟨fun y ↦ h (v + u y), fun x ↦ ?_, ?_⟩
    · change h (v + (φ (Q.stageCoordinates p x)).toAdd) = f (g * x.val)
      dsimp only [φ, v]
      rw [Q.stageCoordinateMap_stageCoordinates]
      have he := hh (g₀ * Subgroup.inclusion hQJ x)
      rw [map_mul] at he
      exact he
    · exact elementaryContDiff_hom u φ.continuous (fun y ↦ h (v + y))
        (elementaryContDiff_leftTranslate h hs v)

/-- Left translation acts on smooth Bruhat functions. -/
def bruhatSmoothTranslate (g : G) : Module.End ℂ (bruhatSmoothSubmodule (G := G)) where
  toFun f := ⟨fun x ↦ f.val (g * x), fun s ↦ (f.property s).translate g⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Translation covariance as an equality of endomorphisms on smooth functions. -/
theorem bruhatFirstOrder_translate_comm (c : Multiplicative ℝ →ₜ* G) (g : G) :
    bruhatFirstOrder c * bruhatSmoothTranslate g = bruhatSmoothTranslate g * bruhatFirstOrder c := by
  apply LinearMap.ext
  intro f
  exact Subtype.ext (bruhatOrbitDeriv_translate c g f.val)


end

end Masullo
