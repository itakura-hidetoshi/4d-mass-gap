import MGAP4D.MathlibAnalytic.EuclideanYangMillsPolishKolmogorovExtension
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveContinuumMeasure

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Analytic and gauge-theoretic data attached to the canonical Polish
Kolmogorov projective-limit measure.

The measure itself is no longer an external input: it is fixed to
`euclideanYangMillsPolishKolmogorovMeasure F`.  This structure contains only the
remaining gauge action and OS analytic properties needed to promote that measure
to the repository's continuum Yang--Mills construction interface. -/
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
    ∀ g, Measurable (fun A : F.Configuration => g • A)
  gaugeInvariant :
    ∀ g,
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

/-- Promote the canonical Polish Kolmogorov measure and the remaining analytic
data to a complete projective continuum-measure construction. -/
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
          euclidean_yang_mills_polish_kolmogorov_isProjectiveLimit }
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

/-- The continuum carrier of the promoted construction is definitionally the
canonical Polish Kolmogorov extension. -/
theorem
    EuclideanYangMillsPolishContinuumAnalyticData.continuumMeasure_eq_kolmogorov
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    [∀ x, TopologicalSpace (F.fieldValue x)]
    [∀ x, BorelSpace (F.fieldValue x)]
    [∀ x, PolishSpace (F.fieldValue x)]
    (D : EuclideanYangMillsPolishContinuumAnalyticData F) :
    D.toContinuumConstruction.limit.continuumMeasure =
      euclideanYangMillsPolishKolmogorovMeasure F := by
  rfl

/-- The promoted construction has the expected projective-limit law. -/
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

/-- The promoted construction is a probability measure. -/
theorem
    EuclideanYangMillsPolishContinuumAnalyticData.continuumProbability
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    [∀ x, TopologicalSpace (F.fieldValue x)]
    [∀ x, BorelSpace (F.fieldValue x)]
    [∀ x, PolishSpace (F.fieldValue x)]
    (D : EuclideanYangMillsPolishContinuumAnalyticData F) :
    IsProbabilityMeasure
      D.toContinuumConstruction.limit.continuumMeasure :=
  euclidean_yang_mills_projective_limit_probability
    D.toContinuumConstruction.limit

/-- Construct the full audit-visible continuum certificate without taking a
projective-limit measure as an external argument. -/
noncomputable def
    EuclideanYangMillsPolishContinuumAnalyticData.toContinuumCertificate
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    [∀ x, TopologicalSpace (F.fieldValue x)]
    [∀ x, BorelSpace (F.fieldValue x)]
    [∀ x, PolishSpace (F.fieldValue x)]
    (D : EuclideanYangMillsPolishContinuumAnalyticData F) :
    EuclideanYangMillsProjectiveContinuumMeasureCertificate
      D.toContinuumConstruction :=
  euclideanYangMillsProjectiveContinuumMeasureCertificate
    D.toContinuumConstruction

/-- The resulting Euclidean Yang--Mills measure package satisfies the existing
OS/Wightman readiness interface. -/
theorem
    EuclideanYangMillsPolishContinuumAnalyticData.measurePackageReady
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    [∀ x, TopologicalSpace (F.fieldValue x)]
    [∀ x, BorelSpace (F.fieldValue x)]
    [∀ x, PolishSpace (F.fieldValue x)]
    (D : EuclideanYangMillsPolishContinuumAnalyticData F) :
    D.toContinuumConstruction.toMeasurePackage.ready :=
  D.toContinuumCertificate.measurePackageReady

end

end MathlibAnalytic
end MGAP4D
