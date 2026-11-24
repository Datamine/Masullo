import BruhatSupportedPeriodization

open Function Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 8

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)

include hm in
set_option backward.isDefEq.respectTransparency false in
/-- A compact logarithmic cutoff lifts every quotient-stage test
continuously to the prescribed compact-support subspace of a compatible
source stage. -/
theorem exists_bruhatCompactTests_cutoff_pullback (P : WholeBruhatStage G) (N : Subgroup G)
    [T2Space (G ⧸ N)] [LocallyCompactSpace (G ⧸ N)]
    (Q : WholeBruhatStage (G ⧸ N)) (hP : P.val.1.kernel ≤ N)
    (a b : ℝ) (c : ℝ → ℂ) (hc : ContDiff ℝ ∞ c) (hs : support c ⊆ Icc a b) :
    let C := (fun x ↦ (m x).toAdd) ⁻¹' Icc a b
    ∃ S : Q.val.Space →L[ℂ] P.val.compactTests C,
      ∀ (g : Q.val.Space) (x : G),
        P.val.realize (S g).val x = c (m x).toAdd * Q.val.realize g (QuotientGroup.mk x) := by
  dsimp only
  let q : G →ₜ* G ⧸ N := ⟨QuotientGroup.mk' N, QuotientGroup.continuous_mk⟩
  have hPQ : P.val.1.kernel ≤ Q.val.1.kernel.comap q.toMonoidHom := by
    intro x hx
    change q x ∈ Q.val.1.kernel
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).2 (hP hx)]
    exact Q.val.1.kernel.one_mem
  let ψ := P.coordinateMap Q q hPQ
  let φ := ψ.toMonoidHom.toAdditive
  let l := P.logCoordinate m
  let U (f : Q.val.Space) : P.val.Space := ⟨_, elementarySchwartz_logCutoff_pullback_mem l
    (P.logCoordinate_isProperMap m hm) c hc (Icc a b) isCompact_Icc hs φ ψ.continuous f⟩
  let L : Q.val.Space →ₗ[ℂ] P.val.Space :=
    { toFun := U
      map_add' := fun f g ↦ Subtype.ext (funext fun x ↦ mul_add _ _ _)
      map_smul' := fun z f ↦ Subtype.ext (funext fun x ↦ mul_left_comm _ _ _) }
  have hval (g : Q.val.Space) (x : G) :
      P.val.realize (L g) x = c (m x).toAdd * Q.val.realize g (QuotientGroup.mk x) := by
    have hco := congrArg Multiplicative.toAdd (P.coordinateMap_coordinates Q q hPQ x)
    calc
      P.val.realize (L g) x = c (l (P.coordinates x).toAdd) * g.val (ψ (P.coordinates x)).toAdd :=
        P.realize_eq_coordinates (L g) x
      _ = c (m x).toAdd * g.val (Q.coordinates (q x)).toAdd :=
        congrArg₂ (fun t y ↦ c t * g.val y) (P.logCoordinate_coordinates m x) hco
      _ = _ := congrArg (c (m x).toAdd * ·) (Q.realize_eq_coordinates g (q x)).symm
  let A : Q.val.Space →L[ℂ] P.val.Space :=
    ⟨L, bruhatStage_continuous_of_evaluation _ _ L fun x ↦
      (continuous_const.mul (Q.val.continuous_realize_eval (q x))).congr (fun g ↦ (hval g x).symm)⟩
  have hA (g : Q.val.Space) :
      A g ∈ P.val.compactTests ((fun x ↦ (m x).toAdd) ⁻¹' Icc a b) := by
    intro x hx
    change P.val.realize (L g) x = 0
    have hz : c (m x).toAdd = 0 := notMem_support.mp fun h ↦ hx (hs h)
    rw [hval, hz, zero_mul]
  exact ⟨A.codRestrict _ hA, hval⟩

variable (γ : G) (hγ : 0 < (m γ).toAdd)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
private theorem cutoff_log_translate (j : ℤ) (x : G) :
    (m (γ ^ j * x)).toAdd = (m x).toAdd + (m γ).toAdd * (j : ℝ) := by
  simp only [map_mul, map_zpow, toAdd_mul, toAdd_zpow, zsmul_eq_mul]
  ring

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- The logarithmic cutoff identity gives a section whenever periodization
and cutoff pullback have their pointwise formulas on quotient tests. -/
theorem cyclicCutoff_rightInverse_of_values {U V : Type*}
    (N : Subgroup G) (hγN : Subgroup.zpowers γ ≤ N)
    (p : U → G → ℂ) (q : V → (G ⧸ N) → ℂ) (hq : Injective q)
    (c : ℝ → ℂ)
    (hc : ∀ f : ℝ → ℂ, Periodic f (m γ).toAdd →
      integerPeriodization (m γ).toAdd (fun x ↦ c x * f x) = f)
    (A : U → V) (R : V → U)
    (hA : ∀ f x, q (A f) (QuotientGroup.mk x) = ∑' j : ℤ, p f (γ ^ j * x))
    (hR : ∀ v x, p (R v) x = c (m x).toAdd * q v (QuotientGroup.mk x)) :
    RightInverse R A := by
  intro v
  apply hq
  funext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hqx (j : ℤ) : (QuotientGroup.mk (γ ^ j * x) : G ⧸ N) = QuotientGroup.mk x := by
    rw [QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).2 (hγN (Subgroup.zpow_mem_zpowers γ j)), one_mul]
  calc
    _ = ∑' j : ℤ, p (R v) (γ ^ j * x) := hA (R v) x
    _ = ∑' j : ℤ, c ((m x).toAdd + (m γ).toAdd * (j : ℝ)) * q v (QuotientGroup.mk x) :=
      tsum_congr fun j ↦ (hR v (γ ^ j * x)).trans
        (congrArg₂ (· * ·) (congrArg c (cutoff_log_translate m γ j x)) (congrArg (q v) (hqx j)))
    _ = _ := congrFun (hc (fun _ ↦ q v (QuotientGroup.mk x)) (fun _ ↦ rfl)) (m x).toAdd

include hγ in
/-- Pointwise stage realizations of cyclic orbit sums assemble into a
continuous linear map between the same two stages. -/
theorem exists_bruhatStage_periodization_map (P : WholeBruhatStage G) (N : Subgroup G)
    [T2Space (G ⧸ N)] [LocallyCompactSpace (G ⧸ N)] (Q : WholeBruhatStage (G ⧸ N))
    (hper : ∀ f : P.val.Space, ∃ g : Q.val.Space,
      ∀ x : G, Q.val.realize g (QuotientGroup.mk x) =
        bruhatSchwartz_cyclicOrbitSum m γ hγ x (P.val.inclusion f)) :
    ∃ L : P.val.Space →L[ℂ] Q.val.Space, ∀ f x,
      Q.val.realize (L f) (QuotientGroup.mk x) = ∑' j : ℤ, P.val.realize f (γ ^ j * x) := by
  let q : G → G ⧸ N := QuotientGroup.mk
  have hq : Surjective q := QuotientGroup.mk_surjective
  let F (x : G) : P.val.Space →L[ℂ] ℂ :=
    (bruhatSchwartz_cyclicOrbitSum m γ hγ x).comp P.val.inclusionCLM
  have hM : ∃ L : P.val.Space →L[ℂ] Q.val.Space, ∀ f x,
      Q.val.realize (L f) (q x) = F x f :=
    bruhatStage_exists_clm_of_evaluation P.val Q.val q hq F hper
  obtain ⟨L, hL⟩ := hM
  exact ⟨L, fun f x ↦ (hL f x).trans
    (bruhatSchwartz_cyclicOrbitSum_apply m γ hγ x (P.val.inclusion f))⟩

end

end Masullo
