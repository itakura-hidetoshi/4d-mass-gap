import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The Euclidean four-dimensional spacetime carrier used for the continuum
Yang--Mills gauge-field model. -/
abbrev EuclideanSpacetimeR4 : Type := Fin 4 → ℝ

/-- R4 gauge-field model carrier attached to a completed Euclidean Yang--Mills
construction spine.

This structure is construction-only.  It records the continuous spacetime carrier
`Fin 4 → ℝ`, the gauge group and gauge-field configuration carrier already
present in the Euclidean measure package, and the construction-side proofs that
make the carrier a continuum four-dimensional Yang--Mills gauge-field model. -/
structure EuclideanYangMillsR4GaugeFieldModel
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S) where
  spacetime : Type
  spacetime_eq_r4 : spacetime = EuclideanSpacetimeR4
  gaugeGroup : Type
  gaugeGroup_eq_measurePackage : gaugeGroup = S.measurePackage.gaugeGroup
  gaugeFieldConfiguration : Type
  gaugeFieldConfiguration_eq_measurePackage :
    gaugeFieldConfiguration = S.measurePackage.configurationSpace
  fieldAlgebra : Type
  fieldAlgebra_eq_measurePackage : fieldAlgebra = S.measurePackage.fieldAlgebra
  schwingerFunctions : ℕ → Type
  schwingerFunctions_eq_measurePackage :
    schwingerFunctions = S.measurePackage.schwingerFunctions
  continuumMeasureConstructed :
    S.continuumFourDimensionalYangMillsMeasureConstructed
  gaugeGroupCompact : S.measurePackage.gaugeGroupCompact
  gaugeGroupNontrivial : S.measurePackage.gaugeGroupNontrivial
  gaugeInvariantSchwingerFunctionsConstructed :
    S.gaugeInvariantSchwingerFunctionsConstructed
  euclideanInvariant : S.measurePackage.euclideanInvariant
  reflectionPositive : S.measurePackage.reflectionPositive

namespace EuclideanYangMillsR4GaugeFieldModel

/-- Build the R4 gauge-field model carrier from a construction-only closure. -/
def ofConstructionClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S) :
    EuclideanYangMillsR4GaugeFieldModel S K :=
  { spacetime := EuclideanSpacetimeR4
    spacetime_eq_r4 := rfl
    gaugeGroup := S.measurePackage.gaugeGroup
    gaugeGroup_eq_measurePackage := rfl
    gaugeFieldConfiguration := S.measurePackage.configurationSpace
    gaugeFieldConfiguration_eq_measurePackage := rfl
    fieldAlgebra := S.measurePackage.fieldAlgebra
    fieldAlgebra_eq_measurePackage := rfl
    schwingerFunctions := S.measurePackage.schwingerFunctions
    schwingerFunctions_eq_measurePackage := rfl
    continuumMeasureConstructed :=
      EuclideanYangMillsCompleteConstructionClosure.continuumMeasureConstructed K
    gaugeGroupCompact := K.gaugeGroupStructure.1
    gaugeGroupNontrivial := K.gaugeGroupStructure.2
    gaugeInvariantSchwingerFunctionsConstructed :=
      EuclideanYangMillsCompleteConstructionClosure.gaugeInvariantSchwingerFunctionsConstructed K
    euclideanInvariant := K.measureStructure.2.1
    reflectionPositive := K.measureStructure.1 }

/-- The model uses continuous Euclidean R4 as its spacetime carrier. -/
theorem spacetimeR4
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    (M : EuclideanYangMillsR4GaugeFieldModel S K) :
    M.spacetime = EuclideanSpacetimeR4 :=
  M.spacetime_eq_r4

/-- The gauge-field configuration carrier is the Euclidean measure package carrier. -/
theorem gaugeFieldConfiguration_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    (M : EuclideanYangMillsR4GaugeFieldModel S K) :
    M.gaugeFieldConfiguration = S.measurePackage.configurationSpace :=
  M.gaugeFieldConfiguration_eq_measurePackage

/-- The model carries a constructed continuum four-dimensional Yang--Mills measure. -/
theorem continuumMeasure
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    (M : EuclideanYangMillsR4GaugeFieldModel S K) :
    S.continuumFourDimensionalYangMillsMeasureConstructed :=
  M.continuumMeasureConstructed

/-- The R4 model retains the compact nontrivial gauge group proofs. -/
theorem compactNontrivialGaugeGroup
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    (M : EuclideanYangMillsR4GaugeFieldModel S K) :
    S.measurePackage.gaugeGroupCompact ∧
      S.measurePackage.gaugeGroupNontrivial :=
  ⟨M.gaugeGroupCompact, M.gaugeGroupNontrivial⟩

end EuclideanYangMillsR4GaugeFieldModel

end

end MathlibAnalytic
end MGAP4D
