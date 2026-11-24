import PeriodicMixedSchwartzTopology
import PeriodicSecondSchwartzCurrying

open Filter Function Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {K : AddSubgroup X} {L : AddSubgroup Y}

/-- The product cutoff for two compact factors. -/
def periodicLocalizationProd (v : PeriodicLocalization K) (w : PeriodicLocalization L) :
    PeriodicLocalization (K.prod L) where
  weight := fun z => v.weight z.1 * w.weight z.2
  smooth := (v.smooth.comp contDiff_fst).mul (w.smooth.comp contDiff_snd)
  compact := by
    have hV : IsCompact (tsupport v.weight) := v.compact
    have hW : IsCompact (tsupport w.weight) := w.compact
    apply (hV.prod hW).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (isClosed_closure.prod isClosed_closure)
    intro z hz
    have h : v.weight z.1 * w.weight z.2 ≠ 0 := hz
    exact ⟨subset_closure (left_ne_zero_of_mul h), subset_closure (right_ne_zero_of_mul h)⟩
  cover := by
    intro z
    obtain ⟨k, hk⟩ := v.cover z.1
    obtain ⟨l, hl⟩ := w.cover z.2
    exact ⟨⟨(k.val, l.val), ⟨k.property, l.property⟩⟩, mul_ne_zero hk hl⟩

/-- The two independent localization equations imply the product equation. -/
theorem bothPeriodicSchwartz_isLocalizedProduct (v : PeriodicLocalization K)
    (w : PeriodicLocalization L) (f : bothPeriodicSchwartz v w) :
    IsLocalizedPeriodic (periodicLocalizationProd v w) f.val.val := by
  rintro ⟨x,y⟩ ⟨⟨k,l⟩, ⟨hk,hl⟩⟩
  let g : 𝓢(X × Y, ℂ) := f.val.val
  have hx : v.weight (x+k) * g (x,y) = v.weight x * g (x+k,y) :=
    f.property y x ⟨k,hk⟩
  have hy : w.weight (y+l) * g (x+k,y) = w.weight y * g (x+k,y+l) :=
    f.val.property (x+k) y ⟨l,hl⟩
  change (v.weight (x+k) * w.weight (y+l)) * g (x,y) =
    (v.weight x * w.weight y) * g (x+k,y+l)
  calc
    _ = w.weight (y+l) * (v.weight (x+k) * g (x,y)) := by ring
    _ = v.weight x * (w.weight (y+l) * g (x+k,y)) := by rw [hx]; ring
    _ = _ := by rw [hy]; ring

/-- The cutoff model recovers actual smooth functions with both periodicities. -/
theorem bothPeriodicSchwartz_exists_periodic (v : PeriodicLocalization K)
    (w : PeriodicLocalization L) (f : bothPeriodicSchwartz v w) :
    ∃ u : X × Y → ℂ, ContDiff ℝ ∞ u ∧
      (∀ x y (k : K), u (x+k.val,y) = u (x,y)) ∧
      (∀ x y (l : L), u (x,y+l.val) = u (x,y)) ∧
      ∀ x y, f.val.val (x,y) = (v.weight x * w.weight y) • u (x,y) := by
  obtain ⟨u, hu, hp, hf⟩ := (isLocalizedPeriodic_iff_exists_periodic
    (periodicLocalizationProd v w) f.val.val).mp (bothPeriodicSchwartz_isLocalizedProduct v w f)
  refine ⟨u, hu, ?_, ?_, fun x y => hf (x,y)⟩
  · intro x y k
    simpa only [Prod.mk_add_mk, add_zero] using
      hp (x,y) ⟨(k.val,0), ⟨k.property,L.zero_mem⟩⟩
  · intro x y l
    simpa only [Prod.mk_add_mk, add_zero] using
      hp (x,y) ⟨(0,l.val), ⟨K.zero_mem,l.property⟩⟩

/-- Conversely every smooth function periodic in both variables produces a
test in the joint cutoff model. -/
theorem exists_bothPeriodicSchwartz_of_periodic (v : PeriodicLocalization K)
    (w : PeriodicLocalization L) (u : X × Y → ℂ) (hu : ContDiff ℝ ∞ u)
    (hx : ∀ x y (k : K), u (x+k.val,y) = u (x,y))
    (hy : ∀ x y (l : L), u (x,y+l.val) = u (x,y)) :
    ∃ f : bothPeriodicSchwartz v w,
      ∀ x y, f.val.val (x,y) = (v.weight x * w.weight y) • u (x,y) := by
  let g := periodicLocalization_schwartz (periodicLocalizationProd v w) u hu
  have h2 : ∀ x, schwartzSlice x g ∈ scalarPeriodicSchwartz w := by
    intro x y l
    change w.weight (y+l.val) * ((v.weight x * w.weight y) * u (x,y)) =
      w.weight y * ((v.weight x * w.weight (y+l.val)) * u (x,y+l.val))
    rw [hy]
    ring
  have h1 : (⟨g,h2⟩ : schwartzWithSlicesIn (X := X) (scalarPeriodicSchwartz w)) ∈ bothPeriodicSchwartz v w := by
    intro y x k
    change v.weight (x+k.val) * ((v.weight x * w.weight y) * u (x,y)) =
      v.weight x * ((v.weight (x+k.val) * w.weight y) * u (x+k.val,y))
    rw [hx]
    ring
  exact ⟨⟨⟨g,h2⟩,h1⟩,fun _ _ => rfl⟩


/-- On a product of tori the derivatives on the whole cover are controlled
by the zero-weight seminorm of the doubly localized test. -/
theorem euclideanTorus_bothPeriodic_derivative_le (a b n : ℕ)
    (u : EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin b) → ℂ)
    (hx : ∀ x y (k : euclideanIntegerLattice a), u (x+k.val,y) = u (x,y))
    (hy : ∀ x y (l : euclideanIntegerLattice b), u (x,y+l.val) = u (x,y))
    (f : bothPeriodicSchwartz (euclideanTorusLocalization a) (euclideanTorusLocalization b))
    (hf : ∀ x y, f.val.val (x,y) =
      ((euclideanTorusLocalization a).weight x * (euclideanTorusLocalization b).weight y) • u (x,y))
    (z : EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin b)) :
    ‖iteratedFDeriv ℝ n u z‖ ≤ SchwartzMap.seminorm ℂ 0 n f.val.val := by
  let v := euclideanTorusLocalization a
  let w := euclideanTorusLocalization b
  let P := (euclideanIntegerLattice a).prod (euclideanIntegerLattice b)
  apply norm_iteratedFDeriv_le_of_localizedPeriodic (periodicLocalizationProd v w) u
    (f := f.val.val) (n := n) (x := z)
  · rintro ⟨x,y⟩ ⟨⟨k,l⟩,hk,hl⟩
    change u (x+k,y+l) = u (x,y)
    exact (hx x (y+l) ⟨k,hk⟩).trans (hy x y ⟨l,hl⟩)
  · rintro ⟨x,y⟩
    exact hf x y
  · rintro ⟨x,y⟩
    obtain ⟨k,hk⟩ := euclideanTorusLocalization_eventually_one a x
    obtain ⟨l,hl⟩ := euclideanTorusLocalization_eventually_one b y
    let j : P := ⟨(k.val,l.val),k.property,l.property⟩
    refine ⟨j, ?_⟩
    have h₁ : Tendsto (Prod.fst : EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin b) →
      EuclideanSpace ℝ (Fin a)) (𝓝 (x+k.val,y+l.val)) (𝓝 (x+k.val)) :=
      continuous_fst.continuousAt.tendsto
    have h₂ : Tendsto (Prod.snd : EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin b) →
      EuclideanSpace ℝ (Fin b)) (𝓝 (x+k.val,y+l.val)) (𝓝 (y+l.val)) :=
      continuous_snd.continuousAt.tendsto
    change ∀ᶠ p in 𝓝 (x+k.val,y+l.val), v.weight p.1 * w.weight p.2 = 1
    filter_upwards [h₁.eventually hk, h₂.eventually hl] with p hv hw
    rw [hv, hw, mul_one]

/-- Uniform derivative bounds on the torus control each full Schwartz
seminorm after multiplying by both cutoffs. -/
theorem bothPeriodicSchwartz_seminorm_le (v : PeriodicLocalization K)
    (w : PeriodicLocalization L) (u : X × Y → ℂ) (hu : ContDiff ℝ ∞ u)
    (f : bothPeriodicSchwartz v w)
    (hf : ∀ x y, f.val.val (x,y) = (v.weight x * w.weight y) • u (x,y))
    (k n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ m ≤ n, ∀ z, ‖iteratedFDeriv ℝ m u z‖ ≤ M) :
    SchwartzMap.seminorm ℂ k n f.val.val ≤
      (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        SchwartzMap.seminorm ℂ k i
          ((periodicLocalizationProd v w).compact.toSchwartzMap (periodicLocalizationProd v w).smooth)) * M := by
  let c := periodicLocalizationProd v w
  have he : f.val.val = periodicLocalization_schwartz c u hu := SchwartzMap.ext (fun z => hf z.1 z.2)
  rw [he]
  exact periodicLocalization_seminorm_le c k n u hu hM hbound


/-- The linear isometry that exchanges the two variables preserves every joint Schwartz seminorm. -/
theorem schwartzSeminorm_prodComm (f : 𝓢(X × Y, ℂ)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (LinearIsometryEquiv.prodComm ℝ Y X).toContinuousLinearEquiv f) =
      SchwartzMap.seminorm ℂ k n f := by
  let e := LinearIsometryEquiv.prodComm ℝ Y X
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.toContinuousLinearEquiv f
  have h (z : Y × X) :
      ‖z‖ ^ k * ‖iteratedFDeriv ℝ n g z‖ =
        ‖e z‖ ^ k * ‖iteratedFDeriv ℝ n f (e z)‖ := by
    change ‖z‖ ^ k * ‖iteratedFDeriv ℝ n ((f : X × Y → ℂ) ∘ e) z‖ = _
    rw [e.norm_iteratedFDeriv_comp_right _ _ _, e.norm_map]
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound ℂ k n g (apply_nonneg _ _)
    intro z
    rw [h]
    exact SchwartzMap.le_seminorm ℂ k n f (e z)
  · apply SchwartzMap.seminorm_le_bound ℂ k n f (apply_nonneg _ _)
    intro z
    simpa only [e.apply_symm_apply] using (h (e.symm z)).symm.le.trans
      (SchwartzMap.le_seminorm ℂ k n g (e.symm z))

/-- Swapping the variables transports second-variable localization to first-variable localization. -/
private def secondPeriodic_to_first (w : PeriodicLocalization L)
    (f : schwartzWithSlicesIn (X := X) (scalarPeriodicSchwartz w)) :
    firstPeriodicSchwartz (Y := X) w := by
  let e := (LinearIsometryEquiv.prodComm ℝ Y X).toContinuousLinearEquiv
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f.val
  refine ⟨g, ?_⟩
  intro x y l
  exact f.property x y l

/-- The second-variable cutoff model recovers a smooth function on the
unlocalized mixed cover. -/
theorem secondPeriodicSchwartz_exists_periodic (w : PeriodicLocalization L)
    (f : schwartzWithSlicesIn (X := X) (scalarPeriodicSchwartz w)) :
    ∃ u : X × Y → ℂ, ContDiff ℝ ∞ u ∧
      (∀ x y (l : L), u (x,y+l.val) = u (x,y)) ∧
      ∀ x y, f.val (x,y) = w.weight y • u (x,y) := by
  obtain ⟨v, hv, hp, hf⟩ := firstPeriodicSchwartz_exists_periodic w (secondPeriodic_to_first w f)
  let e := LinearIsometryEquiv.prodComm ℝ X Y
  refine ⟨v ∘ e, hv.comp e.toContinuousLinearEquiv.contDiff, ?_, ?_⟩
  · intro x y l
    exact hp y x l
  · intro x y
    exact hf y x

/-- The seminorm bound for a torus in the second variable is the first-variable bound
transported by the isometry of the two product norms. -/
theorem euclideanTorus_secondPeriodic_derivative_le {b : ℕ}
    (u : X × EuclideanSpace ℝ (Fin b) → ℂ)
    (hp : ∀ x y (l : euclideanIntegerLattice b), u (x,y+l.val) = u (x,y))
    (f : 𝓢(X × EuclideanSpace ℝ (Fin b), ℂ))
    (hf : ∀ x y, f (x,y) = (euclideanTorusLocalization b).weight y • u (x,y))
    (k n : ℕ) (x : X) (y : EuclideanSpace ℝ (Fin b)) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n u (x,y)‖ ≤ SchwartzMap.seminorm ℂ k n f := by
  let e := LinearIsometryEquiv.prodComm ℝ (EuclideanSpace ℝ (Fin b)) X
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.toContinuousLinearEquiv f
  have h := euclideanTorus_firstPeriodic_derivative_le (u ∘ e)
    (fun a c l => hp c a l) g (fun a c => hf c a) k n y x
  rw [e.norm_iteratedFDeriv_comp_right _ _ _, schwartzSeminorm_prodComm f k n] at h
  exact h

/-- Joint rapid derivative bounds in the noncompact first variable give a
Schwartz test in the second-variable localization model. -/
theorem exists_secondPeriodicSchwartz_of_weighted_bounds (w : PeriodicLocalization L)
    (u : X × Y → ℂ) (hu : ContDiff ℝ ∞ u)
    (hp : ∀ x y (l : L), u (x,y+l.val) = u (x,y))
    (hdec : ∀ k n : ℕ, ∃ M : ℝ, ∀ z, ‖z.1‖ ^ k * ‖iteratedFDeriv ℝ n u z‖ ≤ M) :
    ∃ f : schwartzWithSlicesIn (X := X) (scalarPeriodicSchwartz w),
      ∀ x y, f.val (x,y) = w.weight y • u (x,y) := by
  let e := LinearIsometryEquiv.prodComm ℝ Y X
  obtain ⟨f, hf⟩ := exists_firstPeriodicSchwartz_of_weighted_bounds w (u ∘ e)
    (hu.comp e.toContinuousLinearEquiv.contDiff) (fun y x l => hp x y l) (by
      intro k n
      obtain ⟨M,hM⟩ := hdec k n
      refine ⟨M, fun z => ?_⟩
      rw [e.norm_iteratedFDeriv_comp_right _ _ _]
      exact hM (e z))
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm.toContinuousLinearEquiv f.val
  refine ⟨⟨g, ?_⟩, fun x y => hf y x⟩
  intro x y l
  exact f.property x y l


/-- Every localized Schwartz seminorm is controlled by finitely many
joint derivative bounds with weights in the noncompact first variable. -/
theorem secondPeriodicSchwartz_seminorm_le (w : PeriodicLocalization L)
    (u : X × Y → ℂ) (hu : ContDiff ℝ ∞ u) (f : 𝓢(X × Y, ℂ))
    (hf : ∀ x y, f (x,y) = w.weight y • u (x,y)) (k n : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (h₀ : ∀ i ≤ n, ∀ z, ‖iteratedFDeriv ℝ i u z‖ ≤ M)
    (hk : ∀ i ≤ n, ∀ z, ‖z.1‖ ^ k * ‖iteratedFDeriv ℝ i u z‖ ≤ M) :
    SchwartzMap.seminorm ℂ k n f ≤
      (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        (SchwartzMap.seminorm ℂ k i (w.compact.toSchwartzMap w.smooth) +
         SchwartzMap.seminorm ℂ 0 i (w.compact.toSchwartzMap w.smooth))) * M := by
  let e := LinearIsometryEquiv.prodComm ℝ Y X
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.toContinuousLinearEquiv f
  have h : SchwartzMap.seminorm ℂ k n g = SchwartzMap.seminorm ℂ k n f :=
    schwartzSeminorm_prodComm f k n
  rw [← h]
  apply firstPeriodicSchwartz_seminorm_le w (u ∘ e) (hu.comp e.toContinuousLinearEquiv.contDiff)
    g (fun y x => hf x y) k n hM
  · intro i hi z
    rw [e.norm_iteratedFDeriv_comp_right _ _ _]
    exact h₀ i hi (e z)
  · intro i hi z
    rw [e.norm_iteratedFDeriv_comp_right _ _ _]
    exact hk i hi (e z)


end
end Masullo
