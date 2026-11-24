import ElementarySchwartz

open Function Set Topology
open scoped BigOperators ContDiff ENNReal NNReal

namespace Masullo

noncomputable section

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
  [Finite F]

local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
local notation "A" => ElementaryLCAModel m n r F

omit [Finite F] in
/-- Every real one-parameter subgroup on an elementary group has a fixed
velocity on the covering vector space. -/
theorem elementaryOneParameter_lift (c : Multiplicative ℝ →ₜ* Multiplicative A) :
    ∃ v : X, ∀ t : ℝ,
      Multiplicative.toAdd (c (Multiplicative.ofAdd t)) = elementaryCoverHom (t • v) := by
  let c₀ : ℝ →+ A := c.toMonoidHom.toAdditive
  have hc₀ : Continuous c₀ := c.continuous
  let cR : ℝ →+ EuclideanSpace ℝ (Fin m) := (AddMonoidHom.fst _ _).comp c₀
  let cT : ℝ →+ (Fin n → AddCircle (1 : ℝ)) :=
    (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp c₀)
  choose l hl hlift using fun i : Fin n ↦ exists_addCircle_addMonoidHom_lift
    ((Pi.evalAddMonoidHom _ i).comp cT) ((continuous_apply i).comp hc₀.snd.fst)
  have hd (t : ℝ) : (c₀ t).2.2 = 0 := by
    have h := TotallyDisconnectedSpace.eq_of_continuous _ hc₀.snd.snd t 0
    rwa [map_zero] at h
  refine ⟨(cR 1, WithLp.toLp 2 fun i ↦ l i 1), fun t ↦ ?_⟩
  refine Prod.ext ?_ (Prod.ext (funext fun i ↦ ?_) (hd t))
  · change cR t = t • cR 1
    have h := (cR.toRealLinearMap hc₀.fst).map_smul t (1 : ℝ)
    rw [smul_eq_mul, mul_one] at h
    exact h
  · change (cT t) i = ((t * l i 1 : ℝ) : AddCircle (1 : ℝ))
    have hLift : ((l i t : ℝ) : AddCircle (1 : ℝ)) = cT t i := hlift i t
    rw [← hLift]
    congr 1
    have h := ((l i).toRealLinearMap (hl i)).map_smul t (1 : ℝ)
    rw [smul_eq_mul, mul_one] at h
    exact h

/-- Conversely every covering velocity determines a continuous real one-parameter subgroup. -/
def elementaryOneParameter (v : X) : Multiplicative ℝ →ₜ* Multiplicative A where
  toFun t := Multiplicative.ofAdd (elementaryCoverHom (t.toAdd • v))
  map_one' := by change Multiplicative.ofAdd (elementaryCoverHom (0 • v)) = _; simp
  map_mul' t s := by
    change Multiplicative.ofAdd (elementaryCoverHom ((t.toAdd + s.toAdd) • v)) = _
    rw [add_smul, map_add]
    rfl
  continuous_toFun := elementaryCoverHom_continuous.comp
    (continuous_toAdd.smul continuous_const)

/-- The first-order Bruhat derivative is the derivative along the real orbit. -/
def elementaryOrbitDeriv (c : Multiplicative ℝ →ₜ* Multiplicative A)
    (f : A → ℂ) (g : A) : ℂ :=
  deriv (fun t : ℝ ↦ f (g + (c (Multiplicative.ofAdd t)).toAdd)) 0

/-- Differentiation along an orbit is directional differentiation on the smooth lift. -/
theorem elementaryOrbitDeriv_cover (c : Multiplicative ℝ →ₜ* Multiplicative A) (v : X)
    (hv : ∀ t : ℝ, (c (Multiplicative.ofAdd t)).toAdd = elementaryCoverHom (t • v))
    (f : A → ℂ) (a : Fin r → ℤ) (b : F) (x : X)
    (hf : DifferentiableAt ℝ (fun u ↦ f (elementaryCover u a b)) x) :
    elementaryOrbitDeriv c f (elementaryCover x a b) =
      fderiv ℝ (fun u ↦ f (elementaryCover u a b)) x v := by
  let p : X → ℂ := fun u ↦ f (elementaryCover u a b)
  have hLine : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa only [one_smul] using ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add x
  have hAt : HasFDerivAt p (fderiv ℝ p x) (x + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using hf.hasFDerivAt
  have hd := hAt.comp_hasDerivAt (0 : ℝ) hLine
  have he : (fun t : ℝ ↦ f (elementaryCover x a b + (c (Multiplicative.ofAdd t)).toAdd)) =
      fun t ↦ p (x + t • v) := by
    funext t
    rw [hv, ← elementaryCover_add]
  simpa only [elementaryOrbitDeriv, he, zero_smul, add_zero, p, Function.comp_def] using hd.deriv

/-- A word in the first-order operators, in the order of composition. -/
def elementaryOrbitWord : List (Multiplicative ℝ →ₜ* Multiplicative A) → (A → ℂ) → A → ℂ
  | [], f => f
  | c :: cs, f => elementaryOrbitDeriv c (elementaryOrbitWord cs f)

theorem elementaryOrbitWord_tuple {k : ℕ} (c : Fin k → Multiplicative ℝ →ₜ* Multiplicative A)
    (v : Fin k → X)
    (hv : ∀ i t, (c i (Multiplicative.ofAdd t)).toAdd = elementaryCoverHom (t • v i))
    (f : A → ℂ) (a : Fin r → ℤ) (b : F)
    (hf : ContDiff ℝ ∞ (fun u ↦ f (elementaryCover u a b))) (x : X) :
    elementaryOrbitWord (List.ofFn c) f (elementaryCover x a b) =
      iteratedFDeriv ℝ k (fun u ↦ f (elementaryCover u a b)) x v := by
  induction k generalizing x with
  | zero =>
    rw [List.ofFn_zero, elementaryOrbitWord, iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [List.ofFn_succ, elementaryOrbitWord]
    have hword : (fun w ↦ elementaryOrbitWord (List.ofFn (fun i => c i.succ)) f
          (elementaryCover w a b)) =
        fun w ↦ iteratedFDeriv ℝ k (fun u ↦ f (elementaryCover u a b)) w (Fin.tail v) :=
      funext (ih (Fin.tail c) (Fin.tail v) (fun i t ↦ hv i.succ t))
    have hd : Differentiable ℝ (iteratedFDeriv ℝ k (fun u ↦ f (elementaryCover u a b))) :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top k)
    have hd' : Differentiable ℝ (fun w ↦
        iteratedFDeriv ℝ k (fun u ↦ f (elementaryCover u a b)) w (Fin.tail v)) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ X) ℂ (Fin.tail v)).differentiable.comp hd
    rw [elementaryOrbitDeriv_cover _ _ (hv 0) _ _ _ _ (by rw [hword]; exact hd'.differentiableAt),
      hword, hd.differentiableAt.iteratedFDeriv_succ_apply_left']

/-- The action of any word is the corresponding iterated Fréchet derivative
evaluated on its fixed lifted velocities. -/
theorem elementaryOrbitWord_cover (cs : List (Multiplicative ℝ →ₜ* Multiplicative A))
    (f : A → ℂ) (a : Fin r → ℤ) (b : F)
    (hf : ContDiff ℝ ∞ (fun u ↦ f (elementaryCover u a b))) :
    ∃ v : Fin cs.length → X, ∀ x,
      elementaryOrbitWord cs f (elementaryCover x a b) =
        iteratedFDeriv ℝ cs.length (fun u ↦ f (elementaryCover u a b)) x v := by
  choose v hv using fun i : Fin cs.length ↦ elementaryOneParameter_lift (cs.get i)
  refine ⟨v, fun x ↦ ?_⟩
  simpa only [List.ofFn_get] using elementaryOrbitWord_tuple cs.get v hv f a b hf x


omit [AddCommGroup F] [Finite F] in
/-- The joint covering map is an open quotient map. -/
theorem elementaryCover_openQuotientMap :
    IsOpenQuotientMap (fun p : X × ((Fin r → ℤ) × F) ↦ elementaryCover p.1 p.2.1 p.2.2) := by
  let q : ℝ → AddCircle (1 : ℝ) := (↑)
  have hq : IsOpenQuotientMap q := ⟨QuotientAddGroup.mk_surjective,
    AddCircle.continuous_mk' _, QuotientAddGroup.isOpenMap_coe⟩
  have hT : IsOpenQuotientMap (fun t : EuclideanSpace ℝ (Fin n) ↦ fun i ↦ q (t i)) :=
    (IsOpenQuotientMap.piMap (fun _ : Fin n ↦ hq)).comp
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  have h := (((show IsOpenQuotientMap (id : EuclideanSpace ℝ (Fin m) → _) from .id).prodMap hT).prodMap
    (show IsOpenQuotientMap (id : ((Fin r → ℤ) × F) → _) from .id))
  exact (Homeomorph.prodAssoc _ _ _).isOpenQuotientMap.comp h

omit [AddCommGroup F] [Finite F] in
/-- Continuity can be checked on the individual covering fibres. -/
theorem elementary_continuous_of_fibres {Y : Type*} [TopologicalSpace Y] (f : A → Y)
    (hf : ∀ a b, Continuous (fun u ↦ f (elementaryCover u a b))) :
    Continuous f := by
  apply (elementaryCover_openQuotientMap (m := m) (n := n) (r := r) (F := F)).continuous_comp_iff.mp
  exact continuous_prod_of_discrete_right.mpr fun z ↦ hf z.1 z.2

/-- A fibrewise differentiable elementary function has a derivative on every
orbit, with value given by its first-order Bruhat derivative. -/
theorem elementaryOrbit_hasDerivAt (c : Multiplicative ℝ →ₜ* Multiplicative A)
    (f : A → ℂ) (hf : ∀ a b, Differentiable ℝ (fun u ↦ f (elementaryCover u a b))) (g : A) :
    HasDerivAt (fun t : ℝ ↦ f (g + (c (Multiplicative.ofAdd t)).toAdd))
      (elementaryOrbitDeriv c f g) 0 := by
  obtain ⟨u, hu⟩ := elementaryCover_surjective g.2.2.1 g.2.2.2 g.1 g.2.1
  obtain ⟨v, hv⟩ := elementaryOneParameter_lift c
  have he : (fun t : ℝ ↦ f (g + (c (Multiplicative.ofAdd t)).toAdd)) =
      fun t ↦ f (elementaryCover ((g.1, u) + t • v) g.2.2.1 g.2.2.2) := by
    funext t
    change elementaryCover (g.1, u) g.2.2.1 g.2.2.2 = g at hu
    rw [hv, elementaryCover_add, hu]
  have hLine : Differentiable ℝ (fun t : ℝ ↦ (g.1, u) + t • v) :=
    fun t ↦ (((hasDerivAt_id' t).smul_const v).const_add (g.1, u)).differentiableAt
  have hd : DifferentiableAt ℝ
      (fun t : ℝ ↦ f (g + (c (Multiplicative.ofAdd t)).toAdd)) 0 := by
    rw [he]
    exact ((hf g.2.2.1 g.2.2.2).comp hLine).differentiableAt
  exact hd.hasDerivAt

/-- One derivative lowers fibrewise differentiability by at most one. -/
theorem elementaryOrbitDeriv_contDiff (c : Multiplicative ℝ →ₜ* Multiplicative A)
    (f : A → ℂ) {s : ℕ} (hf : ∀ a b, ContDiff ℝ (s + 1 : ℕ) (fun u ↦ f (elementaryCover u a b))) :
    ∀ a b, ContDiff ℝ s (fun u ↦ elementaryOrbitDeriv c f (elementaryCover u a b)) := by
  obtain ⟨v, hv⟩ := elementaryOneParameter_lift c
  intro a b
  have hd : Differentiable ℝ (fun u ↦ f (elementaryCover u a b)) :=
    (hf a b).differentiable (by exact_mod_cast Nat.succ_ne_zero s)
  have he : (fun u ↦ elementaryOrbitDeriv c f (elementaryCover u a b)) =
      fun u ↦ fderiv ℝ (fun w ↦ f (elementaryCover w a b)) u v :=
    funext fun u ↦ elementaryOrbitDeriv_cover c v hv f a b u hd.differentiableAt
  rw [he]
  exact (ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp
    ((hf a b).fderiv_right (by simp))


end

end Masullo
