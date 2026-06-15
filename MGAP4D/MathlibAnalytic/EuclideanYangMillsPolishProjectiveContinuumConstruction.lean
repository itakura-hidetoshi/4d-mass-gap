import MGAP4D.MathlibAnalytic.EuclideanYangMillsPolishKolmogorovExtension
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveContinuumMeasure

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

structure EuclideanYangMillsPolishContinuumAnalyticData
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    [∀ x, TopologicalSpace (F.fieldValue x)]
    [∀ x, BorelSpace (F.fieldValue x)]
    [∀ x, PolishSpace (F.fieldValue x)] where
  gaugeGroup : Type
  [gaugeGroupGroup : Group gaugeGroup]
  [gaugeGroupTopology : TopologicalSpace gaugeGroup]
  [gaugeGroupCompact : CompactSpace gaugeGroup]
  [gaugeGroupNontrivial : Nontrivial gaugeGroup]
  [gaugeAction : MulAction gaugeGroup F.Configuration]
  gaugeActionMeasurable :
    ∀ g : gaugeGroup, Measurable (fun A : F.Configuration => g • A)
  gaugeInvariant :
    ∀ g : gaugeGroup,
      (euclideanYangMillsPolishKolmogorovMeasure F).map
          (fun A : F.Configuration => g • A) =
        euclideanYangMillsPolishKolmogorovMeasure F
  fieldAlgebra : Type
  schwingerFunctions : ℕ → Type
  reflectionPositive : Prop
  reflectionPositive_proof : reflectionPositive
  euclideanInvariant : Prop
  euclideanInvariant_proof : euclideanInvariant
  symmetric : Prop
  symmetric_proof : symmetric
  clusterProperty : Prop
  clusterProperty_proof : clusterProperty
  regularity : Prop
  regularity_proof : regularity

attribute [instance]
  EuclideanYangMillsPolishContinuumAnalyticData.gaugeGroupGroup
  EuclideanYangMillsPolishContinuumAnalyticData.gaugeGroupTopology
  EuclideanYangMillsPolishContinuumAnalyticData.gaugeGroupCompact
  EuclideanYangMillsPolishContinuumAnalyticData.gaugeGroupNontrivial
  EuclideanYangMillsPolishContinuumAnalyticData.gaugeAction

noncomputable def
    EuclideanYangMillsPolishContinuumAnalyticData.toContinuumConstruction
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    [∀ x, TopologicalSpace (F.fieldValue x)]
    [∀ x, BorelSpace (F.fieldValue x)]
    [∀ x, PolishSpace (F.fieldValue x)]
    (D : EuclideanYangMillsPolishContinuumAnalyticData F) :
    EuclideanYangMillsProjectiveContinuumMeasureConstruction F :=
  { limit :=
      { continuumMeasure := euclideanYangMillsPolishKolmogorovMeasure F
        projectiveLimit :=
          euclidean_yang_mills_polish_kolmogorov_isProjectiveLimit (F := F) }
    gaugeGroup := D.gaugeGroup
    gaugeGroupGroup := D.gaugeGroupGroup
    gaugeGroupTopology := D.gaugeGroupTopology
    gaugeGroupCompact := D.gaugeGroupCompact
    gaugeGroupNontrivial := D.gaugeGroupNontrivial
    gaugeAction := D.gaugeAction
    gaugeActionMeasurable := D.gaugeActionMeasurable
    gaugeInvariant := D.gaugeInvariant
    fieldAlgebra := D.fieldAlgebra
    schwingerFunctions := D.schwingerFunctions
    reflectionPositive := D.reflectionPositive
    reflectionPositive_proof := D.reflectionPositive_proof
    euclideanInvariant := D.euclideanInvariant
    euclideanInvariant_proof := D.euclideanInvariant_proof
    symmetric := D.symmetric
    symmetric_proof := D.symmetric_proof
    clusterProperty := D.clusterProperty
    clusterProperty_proof := D.clusterProperty_proof
    regularity := D.regularity
    regularity_proof := D.regularity_proof }

theorem
    EuclideanYangMillsPolishContinuumAnalyticData.projectiveLimit
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    [∀ x, TopologicalSpace (F.fieldValue x)]
    [∀ x, BorelSpace (F.fieldValue x)]
    [∀ x, PolishSpace (F.fieldValue x)]
    (D : EuclideanYangMillsPolishContinuumAnalyticData F) :
    IsProjectiveLimit
      D.toContinuumConstruction.limit.continuumMeasure
      F.finiteMarginal :=
  D.toContinuumConstruction.limit.projectiveLimit

end

end MathlibAnalytic
end MGAP4D
