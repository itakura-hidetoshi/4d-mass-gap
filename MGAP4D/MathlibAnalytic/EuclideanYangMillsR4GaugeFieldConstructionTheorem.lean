import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4GaugeFieldModel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4GaugeFieldModel

/-- R4 gauge-field construction outputs bundled together. -/
def constructionOutputs
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    (M : EuclideanYangMillsR4GaugeFieldModel S K) : Prop :=
  M.spacetime = EuclideanSpacetimeR4 ∧
    M.gaugeGroup = S.measurePackage.gaugeGroup ∧
      M.gaugeFieldConfiguration = S.measurePackage.configurationSpace ∧
        S.continuumFourDimensionalYangMillsMeasureConstructed ∧
          S.measurePackage.gaugeGroupCompact ∧
            S.measurePackage.gaugeGroupNontrivial ∧
              S.gaugeInvariantSchwingerFunctionsConstructed

/-- The R4 gauge-field model proves its construction outputs. -/
theorem constructionOutputs_holds
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    (M : EuclideanYangMillsR4GaugeFieldModel S K) :
    M.constructionOutputs :=
  ⟨M.spacetime_eq_r4,
    M.gaugeGroup_eq_measurePackage,
    M.gaugeFieldConfiguration_eq_measurePackage,
    M.continuumMeasureConstructed,
    M.gaugeGroupCompact,
    M.gaugeGroupNontrivial,
    M.gaugeInvariantSchwingerFunctionsConstructed⟩

/-- The construction closure itself induces an R4 gauge-field model. -/
theorem nonempty_ofConstructionClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S) :
    Nonempty (EuclideanYangMillsR4GaugeFieldModel S K) :=
  ⟨ofConstructionClosure S K⟩

/-- The construction spine itself induces an R4 gauge-field model after taking its
construction-only closure. -/
theorem nonempty_ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    Nonempty
      (EuclideanYangMillsR4GaugeFieldModel S
        (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)) :=
  ⟨ofConstructionClosure S
    (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)⟩

/-- The construction spine itself proves the bundled R4 gauge-field construction
outputs. -/
theorem constructionOutputs_ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (ofConstructionClosure S
      (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)).constructionOutputs :=
  constructionOutputs_holds
    (ofConstructionClosure S
      (EuclideanYangMillsCompleteConstructionClosure.ofSpine S))

end EuclideanYangMillsR4GaugeFieldModel

end

end MathlibAnalytic
end MGAP4D
