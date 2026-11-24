import ProjectiveOperatorTensors
import GlobalSpectralQuotientTrace

open Filter Function InnerProductSpace MeasureTheory NumberField Set Topology
open scoped CompactlySupported InnerProductSpace NumberField TensorProduct

namespace Masullo

noncomputable section

/-- The rectangle includes each allowed derivative order in a character and
zero slot. Slots for absent zeros can have multiplicity zero. -/
def spectralTensorRectangle (d : ℕ → ℕ → ℕ) (b : ℕ × ℕ) :
    Finset (Σ k : ℕ, Σ j : ℕ, Fin (d k j)) :=
  (Finset.range (b.1 + 1)).sigma fun _ =>
    (Finset.range (b.2 + 1)).sigma fun _ => Finset.univ

theorem spectralTensorRectangle_cofinal (d : ℕ → ℕ → ℕ) :
    Tendsto (spectralTensorRectangle d) atTop atTop := by
  apply tendsto_atTop.mpr
  intro S
  let b : ℕ × ℕ := (S.sup fun i => i.1, S.sup fun i => i.2.1)
  filter_upwards [eventually_ge_atTop b] with c hc i hi
  have hk : i.1 ≤ c.1 := (Finset.le_sup (f := fun i => i.1) hi).trans hc.1
  have hj : i.2.1 ≤ c.2 := (Finset.le_sup (f := fun i => i.2.1) hi).trans hc.2
  simp [spectralTensorRectangle, Nat.lt_succ_of_le hk, Nat.lt_succ_of_le hj]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem norm_hilbertTensorOperator_tmul_le (f : StrongDual ℂ H) (v : H) :
    ‖hilbertTensorOperator (f ⊗ₜ[ℂ] v)‖ ≤ ‖f‖ * ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)
  rw [hilbertTensorOperator_tmul, norm_smul, mul_right_comm]
  exact mul_le_mul_of_nonneg_right (f.le_opNorm x) (norm_nonneg v)

private theorem quotient_rankOne_sum {ι : Type*} [DecidableEq ι] (C : H →L[ℂ] H)
    (v : ι → H) (f : ι → StrongDual ℂ H)
    (hb : ∀ i j, f i (v j) = if i = j then 1 else 0)
    (hsep : ∀ x y, (∀ i, f i x = f i y) → x = y)
    (hs : Summable (fun i => ‖(f i).comp C‖ * ‖v i‖)) :
    (∑' i, hilbertTensorOperator (((f i).comp C) ⊗ₜ[ℂ] v i)) = C := by
  classical
  let A i := hilbertTensorOperator (((f i).comp C) ⊗ₜ[ℂ] v i)
  have hA : Summable A := hs.of_norm_bounded (fun i => by
    change ‖hilbertTensorOperator (((f i).comp C) ⊗ₜ[ℂ] v i)‖ ≤ _
    exact norm_hilbertTensorOperator_tmul_le _ _)
  apply ContinuousLinearMap.ext
  intro x
  apply hsep
  intro j
  let ℓ : (H →L[ℂ] H) →L[ℂ] ℂ := (f j).comp (ContinuousLinearMap.apply ℂ H x)
  change ℓ (∑' i, A i) = _
  rw [ℓ.map_tsum hA, tsum_eq_single j]
  · change f j (f j (C x) • v j) = f j (C x)
    rw [map_smul, hb]
    simp
  · intro i hij
    change f j (f i (C x) • v i) = 0
    simp [hb, Ne.symm hij]

/-- The same rank-one estimate gives the absolutely convergent diagonal
sum for the quotient operator. This is independent of the exhaustion. -/
theorem biorthogonal_rankOne_trace {ι : Type*} [DecidableEq ι] (Q : H →L[ℂ] H)
    (v : ι → H) (f : ι → StrongDual ℂ H)
    (hb : ∀ i j, f i (v j) = if i = j then 1 else 0)
    (hsep : ∀ x y, (∀ i, f i x = f i y) → x = y)
    (hs : Summable (fun i => ‖(f i).comp Q‖ * ‖v i‖)) :
    ∃ R : RankOneSeries ι H, R.operator = Q ∧
      Summable (fun i => ‖f i (Q (v i))‖) ∧ R.trace = ∑' i, f i (Q (v i)) := by
  let u (i : ι) := (InnerProductSpace.toDual ℂ H).symm ((f i).comp Q)
  have hu (i : ι) (x : H) : ⟪u i, x⟫_ℂ = f i (Q x) :=
    InnerProductSpace.toDual_symm_apply
  have hs' : Summable (fun i => ‖v i‖ * ‖u i‖) := by
    simpa only [u, LinearIsometryEquiv.norm_map, mul_comm] using hs
  let R : RankOneSeries ι H := ⟨v, u, hs'⟩
  have hterm (i : ι) :
      rankOne ℂ (v i) (u i) = hilbertTensorOperator (((f i).comp Q) ⊗ₜ[ℂ] v i) := by
    ext x : 1
    rw [rankOne_apply, hilbertTensorOperator_tmul, hu]
    rfl
  have hR : R.operator = Q := by
    change (∑' i, rankOne ℂ (v i) (u i)) = Q
    simp only [hterm]
    exact quotient_rankOne_sum Q v f hb hsep hs
  refine ⟨R, hR, ?_, ?_⟩
  · simpa only [R, hu] using R.trace_summable
  · exact tsum_congr (fun i => hu i (v i))

/-- Regroup the trace of a compatible biorthogonal expansion when each
finite block has a constant diagonal. -/
theorem biorthogonal_rankOne_trace_by_multiplicity {Λ : Type*} [Countable Λ] [DecidableEq Λ]
    (d : Λ → ℕ) (Q : H →L[ℂ] H)
    (v : (Σ k : Λ, Fin (d k)) → H) (f : (Σ k : Λ, Fin (d k)) → StrongDual ℂ H)
    (c : Λ → ℂ) (hd : ∀ i, f i (Q (v i)) = c i.1)
    (hb : ∀ i j, f i (v j) = if i = j then 1 else 0)
    (hsep : ∀ x y, (∀ i, f i x = f i y) → x = y)
    (hsumm : Summable (fun i => ‖(f i).comp Q‖ * ‖v i‖)) :
    ∃ T : TraceClass H, T.toOperator = Q ∧
      Summable (fun k => ‖(d k : ℂ) * c k‖) ∧ T.traceValue = ∑' k, (d k : ℂ) * c k := by
  obtain ⟨R, hR, hnorm, htrace⟩ := biorthogonal_rankOne_trace Q v f hb hsep hsumm
  obtain ⟨S, hS⟩ := R.exists_nat_index
  have hC : Summable (fun i : Σ k : Λ, Fin (d k) => ‖c i.1‖) := by simpa only [hd] using hnorm
  have hCnorm : Summable (fun k => ‖(d k : ℂ) * c k‖) := by
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      norm_mul, Complex.norm_natCast] using hC.sigma
  refine ⟨TraceClass.ofSeries S, hS.trans hR, hCnorm, ?_⟩
  rw [TraceClass.traceValue_ofSeries, RankOneSeries.trace_eq_of_operator_eq hS, htrace]
  simp only [hd]
  rw [hC.of_norm.tsum_sigma]
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Corrected projective expansion for both the quotient and the ambient
spectral projection after convolution. The summable bound is on the specified
biorthogonal family. Every cofinal finite exhaustion gives the same result. -/
theorem spectralProjection_projective_expansion
    {ι β : Type*} [DecidableEq ι] (stages : β → Finset ι) (l : Filter β) (hcofinal : Tendsto stages l atTop)
    (N : Submodule ℂ H) [IsClosed (N : Set H)] (A : H →L[ℂ] H)
    (Q : (H ⧸ N) →L[ℂ] (H ⧸ N)) (hq : N.mkQL.comp A = Q.comp N.mkQL)
    (v : ι → (H ⧸ N)) (f : ι → StrongDual ℂ (H ⧸ N))
    (hb : ∀ i j, f i (v j) = if i = j then 1 else 0)
    (hsep : ∀ x y, (∀ i, f i x = f i y) → x = y)
    (hs : Summable (fun i => ‖(f i).comp Q‖ * ‖v i‖)) :
    ∃ j : (H ⧸ N) →ₗᵢ[ℂ] H,
      (∀ x, j (N.mkQL x) = Nᗮ.starProjection x) ∧
      (∀ x, N.mkQL (j x) = x) ∧
      HilbertProjectiveTensorExpansion stages l (fun i => (f i).comp Q) v Q ∧
      HilbertProjectiveTensorExpansion stages l
        (fun i => ((f i).comp Q).comp N.mkQL) (fun i => j (v i))
        (Nᗮ.starProjection.comp A) := by
  obtain ⟨_, _, e, he, hproj, _⟩ := hilbert_quotient_projection N
  let j := Nᗮ.subtypeₗᵢ.comp e.toLinearIsometry
  let Qterm (i : ι) := hilbertTensorOperator (((f i).comp Q) ⊗ₜ[ℂ] v i)
  have hQ : (∑' i, Qterm i) = Q := quotient_rankOne_sum Q v f hb hsep hs
  have hexp := hilbertProjectiveTensorExpansion_of_summable stages l hcofinal
    (fun i => (f i).comp Q) v hs
  change HilbertProjectiveTensorExpansion stages l (fun i => (f i).comp Q) v
    (∑' i, Qterm i) at hexp
  rw [hQ] at hexp
  have hsum : Summable (fun i => ‖((f i).comp Q).comp N.mkQL‖ * ‖j (v i)‖) := by
    apply (hs.mul_right ‖N.mkQL‖).of_nonneg_of_le (fun _ => by positivity)
    intro i
    rw [j.norm_map, mul_right_comm]
    exact mul_le_mul_of_nonneg_right (((f i).comp Q).opNorm_comp_le _) (norm_nonneg _)
  have hQsum : Summable Qterm := hs.of_norm_bounded fun i => by
    change ‖hilbertTensorOperator (((f i).comp Q) ⊗ₜ[ℂ] v i)‖ ≤ _
    exact norm_hilbertTensorOperator_tmul_le _ _
  let AmbientTerm (i : ι) := hilbertTensorOperator
    ((((f i).comp Q).comp N.mkQL) ⊗ₜ[ℂ] j (v i))
  have hAmbient : (∑' i, AmbientTerm i) = Nᗮ.starProjection.comp A := by
    let L : ((H ⧸ N) →L[ℂ] (H ⧸ N)) →L[ℂ] (H →L[ℂ] H) :=
      (ContinuousLinearMap.compL ℂ H (H ⧸ N) H j.toContinuousLinearMap).comp
        ((ContinuousLinearMap.compL ℂ H (H ⧸ N) (H ⧸ N)).flip N.mkQL)
    have hL (i : ι) : L (Qterm i) = AmbientTerm i := by
      apply ContinuousLinearMap.ext
      intro x
      change j (f i (Q (N.mkQL x)) • v i) = f i (Q (N.mkQL x)) • j (v i)
      rw [map_smul]
    simp_rw [← hL, ← L.map_tsum hQsum, hQ]
    apply ContinuousLinearMap.ext
    intro x
    change j (Q (N.mkQL x)) = Nᗮ.starProjection (A x)
    have hqx : N.mkQL (A x) = Q (N.mkQL x) := DFunLike.congr_fun hq x
    rw [← hqx]
    exact hproj (A x)
  refine ⟨j, hproj, he, hexp, ?_⟩
  have hh := hilbertProjectiveTensorExpansion_of_summable stages l hcofinal
    (fun i => ((f i).comp Q).comp N.mkQL) (fun i => j (v i)) hsum
  change HilbertProjectiveTensorExpansion stages l _ _ (∑' i, AmbientTerm i) at hh
  exact hAmbient ▸ hh

/-- The two orders of projection and convolution agree exactly when
convolution sends the spectral complement back into itself. -/
theorem spectralProjection_order_eq_iff
    (N : Submodule ℂ H) [IsClosed (N : Set H)] (A : H →L[ℂ] H)
    (Q : (H ⧸ N) →L[ℂ] (H ⧸ N)) (hq : N.mkQL.comp A = Q.comp N.mkQL) :
    A.comp Nᗮ.starProjection = Nᗮ.starProjection.comp A ↔
      N.starProjection.comp (A.comp Nᗮ.starProjection) = 0 := by
  obtain ⟨hqP, _, e, _, he, _⟩ := hilbert_quotient_projection N
  have hqP' (x : H) : N.mkQL x = N.mkQL (Nᗮ.starProjection x) := DFunLike.congr_fun hqP x
  have hqA (x : H) : N.mkQL (A x) = Q (N.mkQL x) := DFunLike.congr_fun hq x
  have hPAP (x : H) : Nᗮ.starProjection (A (Nᗮ.starProjection x)) = Nᗮ.starProjection (A x) := by
    rw [← he (A (Nᗮ.starProjection x)), ← he (A x), hqA, hqA, ← hqP']
  have hsplit (x : H) :
      N.starProjection (A (Nᗮ.starProjection x)) + Nᗮ.starProjection (A x) =
        A (Nᗮ.starProjection x) := by
    rw [← hPAP, N.starProjection_add_starProjection_orthogonal]
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    have h' : A (Nᗮ.starProjection x) = Nᗮ.starProjection (A x) := DFunLike.congr_fun h x
    have ht := (hsplit x).trans h'
    exact add_right_cancel (ht.trans (zero_add _).symm)
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    have h' : N.starProjection (A (Nᗮ.starProjection x)) = 0 := DFunLike.congr_fun h x
    have ht := hsplit x
    rw [h', zero_add] at ht
    exact ht.symm


end Hilbert

section Global

variable (F : Type*) [Field F] [NumberField F]

local instance : MeasurableSpace (IdeleClass F) := borel _

variable (μ : Measure (IdeleClass F)) [μ.IsHaarMeasure]

local instance spectralThetaClosed (a l r s : ℝ) (hs : 0 ≤ s) :
    IsClosed (globalThetaSobolevCompletion F μ a l r s hs : Set (Lp ℂ 2 μ)) :=
  globalThetaSobolevCompletion_isClosed F μ a l r s hs

/-- Corrected Theorems 10.4.3.1 and 10.4.3.5. The same statement applies to
the line and the compact strip. It gives the orthogonal lift of each quotient
vector, both projective tensor limits over the paper's rectangles, and the
operator represented by the ambient limit. The specified biorthogonal
data and their absolute rank-one estimate are analytic inputs. -/
theorem globalSpectral_projective_expansion (a l r s : ℝ) (hs : 0 ≤ s)
    (φ : C_c(IdeleClass F, ℂ)) (d : ℕ → ℕ → ℕ) :
    let I := Σ k : ℕ, Σ j : ℕ, Fin (d k j)
    let N := globalThetaSobolevCompletion F μ a l r s hs
    let A := globalHardySobolevConvolution F μ l r s hs φ
    let Q := globalSpectralConvolution F μ a l r s hs φ
    ∀ (v : I → (Lp ℂ 2 μ ⧸ N)) (f : I → StrongDual ℂ (Lp ℂ 2 μ ⧸ N)),
      (∀ i j, f i (v j) = if i = j then 1 else 0) →
      (∀ x y, (∀ i, f i x = f i y) → x = y) →
      Summable (fun i => ‖(f i).comp Q‖ * ‖v i‖) →
      ∃ j : (Lp ℂ 2 μ ⧸ N) →ₗᵢ[ℂ] Lp ℂ 2 μ,
        (∀ x, j (N.mkQL x) = Nᗮ.starProjection x) ∧
        (∀ x, N.mkQL (j x) = x) ∧
        HilbertProjectiveTensorExpansion (spectralTensorRectangle d) atTop
          (fun i => (f i).comp Q) v Q ∧
        HilbertProjectiveTensorExpansion (spectralTensorRectangle d) atTop
          (fun i => ((f i).comp Q).comp N.mkQL) (fun i => j (v i))
          (Nᗮ.starProjection.comp A) ∧
        (A.comp Nᗮ.starProjection = Nᗮ.starProjection.comp A ↔
          N.starProjection.comp (A.comp Nᗮ.starProjection) = 0) := by
  intro I N A Q v f hb hsep hsum
  letI : IsClosed (N : Set (Lp ℂ 2 μ)) := spectralThetaClosed F μ a l r s hs
  have hq : N.mkQL.comp A = Q.comp N.mkQL := rfl
  obtain ⟨j, hj, hleft, hQ, hA⟩ := spectralProjection_projective_expansion
    (spectralTensorRectangle d) atTop (spectralTensorRectangle_cofinal d)
    N A Q hq v f hb hsep hsum
  exact ⟨j, hj, hleft, hQ, hA, spectralProjection_order_eq_iff N A Q hq⟩

end Global

end

end Masullo
