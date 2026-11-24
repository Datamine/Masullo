import FiniteIdeleTamagawa
import SLocalZetaProduct

open IsDedekindDomain MeasureTheory NumberField Topology
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev LocalField (v : Place F) := v.adicCompletion F

variable [∀ v : Place F, MeasurableSpace (LocalField F v)]
  [∀ v : Place F, BorelSpace (LocalField F v)]
  [∀ v : Place F, MeasurableSpace (LocalField F v)ˣ]
  [∀ v : Place F, BorelSpace (LocalField F v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

local instance (S : Finset (Place F)) : MeasurableSpace (SAdeles F S)ˣ := borel _
local instance (S : Finset (Place F)) : MeasurableSpace (SIdeleQuotient F S) := borel _

/-- Formula (A.3.4.2) on the actual units of the S-adelic ring, with
the prescribed archimedean and discriminant-normalized finite factors. -/
def sLocalMultiplicativeTamagawa (S : Finset (Place F)) : Measure (SAdeles F S)ˣ :=
  sLocalZetaProductMeasure F S (fun v => finitePlaceMultiplicativeTamagawa F v.val)
    (archimedeanMultiplicativeHaar F)

theorem sLocalMultiplicativeTamagawa_isHaar (S : Finset (Place F)) :
    (sLocalMultiplicativeTamagawa F S).IsHaarMeasure := by
  letI (v : S) : (finitePlaceMultiplicativeTamagawa F v.val).IsHaarMeasure :=
    finitePlaceMultiplicativeTamagawa_isHaar F v.val
  letI (v : S) : LocallyCompactSpace (LocalField F v.val)ˣ := by
    letI := finitePlace_locallyCompact F v.val
    exact IsOpenUnits.isOpenEmbedding_unitsVal.locallyCompactSpace
  letI (v : S) : SecondCountableTopology (LocalField F v.val)ˣ := by
    letI := finitePlace_secondCountable F v.val
    exact IsOpenUnits.isOpenEmbedding_unitsVal.isEmbedding.secondCountableTopology
  exact sLocalZetaProductMeasure_isHaar F S
    (fun v => finitePlaceMultiplicativeTamagawa F v.val) (archimedeanMultiplicativeHaar F)

/-- The selected-place product and counting on S-units induce a split Weil
quotient measure, with Lebesgue measure in the logarithmic coordinate. -/
theorem sLocalMultiplicativeTamagawa_exists_weil (S : Finset (Place F)) :
    ∃ ν : Measure (SLocalThetaNormOne F S), ν.IsHaarMeasure ∧
      IsWeilQuotientMeasure (sUnitImage F S) (sLocalMultiplicativeTamagawa F S)
        Measure.count (sLocalClassHaar F S ν) := by
  letI := sLocalMultiplicativeTamagawa_isHaar F S
  exact sLocalClassHaar_exists_weil F S _

end
end Masullo
