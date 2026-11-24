import SUnitRank
import Mathlib.Data.Nat.PrimeFin

open Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField RestrictedProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

theorem finitePlaces_infinite : Infinite (Place F) := by
  let p (q : Nat.Primes) : Ideal ℤ := Ideal.span {(q.val : ℤ)}
  have hp0 (q : Nat.Primes) : p q ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast q.property.ne_zero)
  have hp (q : Nat.Primes) : (p q).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast q.property.ne_zero : (q.val : ℤ) ≠ 0)).mpr
      (Nat.prime_iff_prime_int.mp q.property)).isMaximal_of_ne_bot (hp0 q)
  have h (q : Nat.Primes) : ∃ P : Ideal (𝓞 F), P.IsMaximal ∧ P.LiesOver (p q) := by
    letI := hp q
    exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral (p q)
  choose P hP hOver using h
  let w (q : Nat.Primes) : Place F :=
    ⟨P q, (hP q).isPrime, fun e => hp0 q ((hOver q).over.trans
      (e ▸ Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 F)) (algebraMap ℤ (𝓞 F)).injective_int))⟩
  refine Infinite.of_injective w fun q r he => ?_
  have he' : p q = p r := (hOver q).over.trans
    ((congrArg (fun v : Place F => v.asIdeal.under ℤ) he).trans (hOver r).over.symm)
  have he'' := Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp he')
  exact Subtype.ext (by simpa using he'')

def sNormOneBlock (S : Finset (Place F)) : Subgroup (Idele F) :=
  sIdeleBlock F S ⊓ (ideleNorm F).ker

/-- Every global norm-one idele can be moved into a sufficiently large
S-block by a global principal idele. -/
theorem sNormOneBlock_eventually_global :
    ∃ S : Finset (Place F), ∀ T : Finset (Place F), S ⊆ T →
      ∀ a ∈ (ideleNorm F).ker, ∃ t : Fˣ, ∃ b ∈ sNormOneBlock F T,
        a = principalIdele F t * b := by
  obtain ⟨S, hS⟩ := sIdeleClass_eventually_surjective F
  refine ⟨S, fun T hST a ha => ?_⟩
  obtain ⟨c, hc⟩ := hS T hST (ideleClassMap F a)
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective c
  change ideleClassMap F b.val = ideleClassMap F a at hc
  have hp : a / b.val ∈ principalIdeles F := (QuotientGroup.eq_iff_div_mem).mp hc.symm
  obtain ⟨t, ht⟩ := hp
  have ha' : a = principalIdele F t * b.val := by rw [ht, div_mul_cancel]
  have hb : b.val ∈ sNormOneBlock F T := by
    refine ⟨b.property, ?_⟩
    have h := congrArg (ideleNorm F) ha'
    rw [map_mul, ideleNorm_principal, one_mul] at h
    exact h.symm.trans ha
  exact ⟨t, b.val, hb, ha'⟩

/-- The S-unit saturation of a subset of the S-block remains in the S-block. -/
theorem sUnits_saturation_stays_local (S : Finset (Place F)) {E : Set (Idele F)}
    (hE : E ⊆ sIdeleBlock F S) (u : (sIntegerRing F S)ˣ) {b : Idele F} (hb : b ∈ E) :
    principalIdele F (sUnitToField F S u) * b ∈ sIdeleBlock F S :=
  (sIdeleBlock F S).mul_mem ((sPrincipal F S u).property) (hE hb)

/-- An omitted finite place witnesses that the norm-one S-block is proper. -/
theorem sNormOneBlock_omitted_place (S : Finset (Place F)) (v : Place F) (hv : v ∉ S) :
    ∃ a : Idele F, ideleNorm F a = 1 ∧ a ∉ sIdeleBlock F S := by
  let d : Place F →₀ ℤ := Finsupp.single v 1
  obtain ⟨b, hb⟩ := ideleDivisor_surjective F (Multiplicative.ofAdd d)
  have hbv : ideleOrder F b v = 1 :=
    (congrArg (fun x : Multiplicative (Place F →₀ ℤ) => x.toAdd v) hb).trans
      (Finsupp.single_eq_same)
  let t := Multiplicative.ofAdd (Real.log (ideleNorm F b))
  let z := ideleExpSection F t
  have hz : ideleNorm F z = ideleNorm F b :=
    (ideleNorm_expSection F t).trans (Real.exp_log (ideleNorm_pos F b))
  have hzv : ideleOrder F z v = 0 := by
    apply (ideleOrder_eq_zero_iff F z v).mpr
    change Valued.v ((ideleExpSection F t).val.2 v) = 1
    rw [(ideleExpSection_components F t).2]
    exact map_one _
  refine ⟨b / z, ?_, ?_⟩
  · rw [map_div, hz, div_self (ideleNorm_pos F b).ne']
  · intro h
    have he := (sIdeleBlock_mem_iff F S _).mp h v hv
    have hc : ideleOrder F ((b / z) * z) v = 0 := by rw [ideleOrder_mul, he, hzv, zero_add]
    rw [div_mul_cancel, hbv] at hc
    exact one_ne_zero hc

theorem sNormOneDomain_sUnits_do_not_cover (S : Finset (Place F)) {E : Set (Idele F)}
    (hE : E ⊆ sIdeleBlock F S) :
    ∃ a ∈ (ideleNorm F).ker, ∀ u : (sIntegerRing F S)ˣ, ∀ e ∈ E,
      a ≠ principalIdele F (sUnitToField F S u) * e := by
  letI := finitePlaces_infinite (F := F)
  obtain ⟨v, hv⟩ := Finset.exists_notMem S
  obtain ⟨a, ha, hnot⟩ := sNormOneBlock_omitted_place F S v hv
  exact ⟨a, ha, fun u e he eq => hnot (eq ▸ sUnits_saturation_stays_local F S hE u he)⟩

/-- The corrected global covering uses global principal translations.
When an S-local covering set is given, the same set works globally for
every sufficiently large S. -/
theorem sNormOneDomain_eventually_global :
    ∃ S : Finset (Place F), ∀ T : Finset (Place F), S ⊆ T →
      ∀ E : Set (Idele F), (∀ b ∈ sNormOneBlock F T,
        ∃ u : (sIntegerRing F T)ˣ, ∃ e ∈ E, b = principalIdele F (sUnitToField F T u) * e) →
      ∀ a ∈ (ideleNorm F).ker, ∃ t : Fˣ, ∃ e ∈ E, a = principalIdele F t * e := by
  obtain ⟨S, hS⟩ := sNormOneBlock_eventually_global F
  refine ⟨S, fun T hST E hE a ha => ?_⟩
  obtain ⟨t, b, hb, ha'⟩ := hS T hST a ha
  obtain ⟨u, e, he, hb'⟩ := hE b hb
  refine ⟨t * sUnitToField F T u, e, he, ?_⟩
  rw [ha', hb', map_mul, mul_assoc]

/-- A set of global norm-one class representatives can be chosen in every
sufficiently large S-block. On that block the same set is an S-unit transversal. -/
theorem sNormOneDomain_eventual_transversal :
    ∃ S : Finset (Place F), ∀ T : Finset (Place F), S ⊆ T →
      ∃ E : Set (Idele F), E ⊆ sNormOneBlock F T ∧
        (∀ a ∈ (ideleNorm F).ker, ∃! b, b ∈ E ∧ ideleClassMap F b = ideleClassMap F a) ∧
        (∀ a ∈ sNormOneBlock F T, ∃ b ∈ E, ∃ u : (sIntegerRing F T)ˣ,
          a = principalIdele F (sUnitToField F T u) * b) := by
  obtain ⟨S, hS⟩ := sNormOneBlock_eventually_global F
  refine ⟨S, ?_⟩
  intro T hT
  let q := ideleClassMap F
  let B := sNormOneBlock F T
  have h (x : Set.range (fun b : B => q b.val)) : ∃ b : B, q b.val = x.val := x.property
  choose rep hrep using h
  let E : Set (Idele F) := Set.range fun x => (rep x).val
  have hEB : E ⊆ B := by rintro _ ⟨x, rfl⟩; exact (rep x).property
  have hq : ∀ a ∈ (ideleNorm F).ker, ∃! b, b ∈ E ∧ q b = q a := by
    intro a ha
    obtain ⟨t, b, hb, he⟩ := hS T hT a ha
    have htb : q (principalIdele F t) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨t, rfl⟩
    have hba : q b = q a :=
      calc
        q b = q (principalIdele F t) * q b := by rw [htb]; exact (one_mul (q b)).symm
        _ = q (principalIdele F t * b) := (map_mul q _ _).symm
        _ = q a := congrArg q he.symm
    let x : Set.range (fun b : B => q b.val) := ⟨q a, ⟨⟨b, hb⟩, hba⟩⟩
    refine ⟨(rep x).val, ⟨⟨x, rfl⟩, hrep x⟩, ?_⟩
    rintro _ ⟨⟨y, rfl⟩, hy⟩
    exact congrArg (fun z => (rep z).val) (Subtype.ext ((hrep y).symm.trans hy))
  refine ⟨E, hEB, hq, ?_⟩
  intro a ha
  obtain ⟨b, ⟨hb, hba⟩, _⟩ := hq a ha.2
  have hab : a / b ∈ sIdeleBlock F T := (sIdeleBlock F T).div_mem ha.1 (hEB hb).1
  obtain ⟨t, ht⟩ := (QuotientGroup.eq_iff_div_mem).mp hba.symm
  obtain ⟨u, hu⟩ := (principalIdele_mem_sBlock F T t).mp (ht.symm ▸ hab)
  exact ⟨b, hb, u, by rw [hu, ht, div_mul_cancel]⟩

/-- The localized ideal-class map vanishes on the S-block. -/
theorem sLocalizedIdeleClassMap_block (S : Finset (Place F)) (a : sIdeleBlock F S) :
    sLocalizedIdeleClassMap F S (ideleClassMap F a.val) = 1 := by
  have h : ideleClassMap F a.val ∈ (sIdeleClassInclusion F S).range :=
    ⟨QuotientGroup.mk a, rfl⟩
  rw [← sLocalizedIdeleClassMap_ker] at h
  exact h

theorem sLocalizedIdeleClassMap_block_not_surjective (S : Finset (Place F))
    [Nontrivial (SPicardGroup F S)] :
    ¬ Surjective (fun a : sIdeleBlock F S => sLocalizedIdeleClassMap F S (ideleClassMap F a.val)) := by
  intro h
  obtain ⟨c, hc⟩ := exists_ne (1 : SPicardGroup F S)
  obtain ⟨a, ha⟩ := h c
  exact hc (ha.symm.trans (sLocalizedIdeleClassMap_block F S a))

end

end Masullo
