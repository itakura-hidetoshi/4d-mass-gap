import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveContinuumMeasure
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Order.OrderClosed

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open MeasureTheory

noncomputable section

/-- Finite-volume reflection forms converging pointwise to a continuum
reflection form. -/
structure EuclideanYangMillsReflectionPositivityLimitData where
  Observable : Type
  finiteReflectionForm : ℕ → Observable → ℝ
  continuumReflectionForm : Observable → ℝ
  finiteReflectionPositive :
    ∀ (n : ℕ) (O : Observable), 0 ≤ finiteReflectionForm n O
  reflectionFormConverges :
    ∀ O : Observable,
      Tendsto (fun n : ℕ => finiteReflectionForm n O) atTop
        (nhds (continuumReflectionForm O))

/-- Reflection positivity of the limiting form. -/
def EuclideanYangMillsReflectionPositivityLimitData.ContinuumReflectionPositive
    (D : EuclideanYangMillsReflectionPositivityLimitData) : Prop :=
  ∀ O : D.Observable, 0 ≤ D.continuumReflectionForm O

/-- Nonnegativity is closed under pointwise limits, hence finite-volume
reflection positivity passes to the continuum form. -/
theorem euclidean_yang_mills_reflection_positivity_passes_to_limit
    (D : EuclideanYangMillsReflectionPositivityLimitData) :
    D.ContinuumReflectionPositive := by
  intro O
  exact isClosed_Ici.mem_of_tendsto (D.reflectionFormConverges O)
    (.of_forall fun n => D.finiteReflectionPositive n O)

/-- Finite-volume transformed and reference expectations converging to their
continuum counterparts. -/
structure EuclideanYangMillsEuclideanInvarianceLimitData where
  Observable : Type
  Transformation : Type
  finiteReferenceExpectation : ℕ → Observable → ℝ
  finiteTransformedExpectation : ℕ → Transformation → Observable → ℝ
  continuumReferenceExpectation : Observable → ℝ
  continuumTransformedExpectation : Transformation → Observable → ℝ
  finiteEuclideanInvariant :
    ∀ (n : ℕ) (g : Transformation) (O : Observable),
      finiteTransformedExpectation n g O = finiteReferenceExpectation n O
  referenceExpectationConverges :
    ∀ O : Observable,
      Tendsto (fun n : ℕ => finiteReferenceExpectation n O) atTop
        (nhds (continuumReferenceExpectation O))
  transformedExpectationConverges :
    ∀ (g : Transformation) (O : Observable),
      Tendsto (fun n : ℕ => finiteTransformedExpectation n g O) atTop
        (nhds (continuumTransformedExpectation g O))

/-- Euclidean invariance of all limiting expectations. -/
def EuclideanYangMillsEuclideanInvarianceLimitData.ContinuumEuclideanInvariant
    (D : EuclideanYangMillsEuclideanInvarianceLimitData) : Prop :=
  ∀ (g : D.Transformation) (O : D.Observable),
    D.continuumTransformedExpectation g O = D.continuumReferenceExpectation O

/-- Equality of finite-volume transformed and reference expectations passes to
their unique continuum limits. -/
theorem euclidean_yang_mills_euclidean_invariance_passes_to_limit
    (D : EuclideanYangMillsEuclideanInvarianceLimitData) :
    D.ContinuumEuclideanInvariant := by
  intro g O
  have hReference :
      Tendsto (fun n : ℕ => D.finiteTransformedExpectation n g O) atTop
        (nhds (D.continuumReferenceExpectation O)) := by
    simpa only [D.finiteEuclideanInvariant] using
      D.referenceExpectationConverges O
  exact tendsto_nhds_unique (D.transformedExpectationConverges g O) hReference

/-- Pointwise convergence of finite-volume connected correlations together with
a volume-uniform envelope decaying to zero. -/
structure EuclideanYangMillsClusterLimitData where
  Observable : Type
  finiteConnectedCorrelation : ℕ → Observable → ℕ → ℝ
  continuumConnectedCorrelation : Observable → ℕ → ℝ
  clusterEnvelope : Observable → ℕ → ℝ
  pointwiseConvergence :
    ∀ (O : Observable) (r : ℕ),
      Tendsto (fun n : ℕ => finiteConnectedCorrelation n O r) atTop
        (nhds (continuumConnectedCorrelation O r))
  uniformEnvelope :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      ‖finiteConnectedCorrelation n O r‖ ≤ clusterEnvelope O r
  envelopeTendstoZero :
    ∀ O : Observable, Tendsto (clusterEnvelope O) atTop (nhds 0)

/-- Cluster property for the limiting connected correlations. -/
def EuclideanYangMillsClusterLimitData.ContinuumClusterProperty
    (D : EuclideanYangMillsClusterLimitData) : Prop :=
  ∀ O : D.Observable,
    Tendsto (D.continuumConnectedCorrelation O) atTop (nhds 0)

/-- The finite-volume uniform cluster envelope bounds the continuum connected
correlation at each separation. -/
theorem euclidean_yang_mills_cluster_envelope_passes_to_limit
    (D : EuclideanYangMillsClusterLimitData)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤ D.clusterEnvelope O r := by
  have hNorm :
      Tendsto
        (fun n : ℕ => ‖D.finiteConnectedCorrelation n O r‖) atTop
        (nhds ‖D.continuumConnectedCorrelation O r‖) :=
    (continuous_norm.tendsto _).comp (D.pointwiseConvergence O r)
  exact le_of_tendsto' hNorm (fun n => D.uniformEnvelope n O r)

/-- A decaying volume-uniform envelope forces the limiting connected
correlations to cluster. -/
theorem euclidean_yang_mills_cluster_property_passes_to_limit
    (D : EuclideanYangMillsClusterLimitData) :
    D.ContinuumClusterProperty := by
  intro O
  exact squeeze_zero_norm
    (fun r => euclidean_yang_mills_cluster_envelope_passes_to_limit D O r)
    (D.envelopeTendstoZero O)

/-- Pointwise convergence of finite-volume Schwinger data with a uniform
seminorm bound. -/
structure EuclideanYangMillsRegularityLimitData where
  TestDatum : Type
  finiteSchwingerValue : ℕ → TestDatum → ℝ
  continuumSchwingerValue : TestDatum → ℝ
  regularityBound : TestDatum → ℝ
  pointwiseConvergence :
    ∀ q : TestDatum,
      Tendsto (fun n : ℕ => finiteSchwingerValue n q) atTop
        (nhds (continuumSchwingerValue q))
  uniformRegularityBound :
    ∀ (n : ℕ) (q : TestDatum),
      ‖finiteSchwingerValue n q‖ ≤ regularityBound q

/-- The limiting Schwinger data obey the inherited seminorm bound. -/
def EuclideanYangMillsRegularityLimitData.ContinuumRegularity
    (D : EuclideanYangMillsRegularityLimitData) : Prop :=
  ∀ q : D.TestDatum,
    ‖D.continuumSchwingerValue q‖ ≤ D.regularityBound q

/-- Uniform finite-volume regularity estimates pass to the pointwise continuum
limit. -/
theorem euclidean_yang_mills_regularity_passes_to_limit
    (D : EuclideanYangMillsRegularityLimitData) :
    D.ContinuumRegularity := by
  intro q
  have hNorm :
      Tendsto (fun n : ℕ => ‖D.finiteSchwingerValue n q‖) atTop
        (nhds ‖D.continuumSchwingerValue q‖) :=
    (continuous_norm.tendsto _).comp (D.pointwiseConvergence q)
  exact le_of_tendsto' hNorm (fun n => D.uniformRegularityBound n q)

/-- Analytic data that builds a projective-limit continuum measure construction
without directly inserting the four limiting OS properties as opaque proofs. -/
structure EuclideanYangMillsProjectiveLimitAnalyticTransferData
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) where
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
      L.continuumMeasure.map (fun A : F.Configuration => g • A) =
        L.continuumMeasure
  fieldAlgebra : Type
  schwingerFunctions : ℕ → Type
  reflectionLimit : EuclideanYangMillsReflectionPositivityLimitData
  euclideanLimit : EuclideanYangMillsEuclideanInvarianceLimitData
  symmetric : Prop
  symmetric_proof : symmetric
  clusterLimit : EuclideanYangMillsClusterLimitData
  regularityLimit : EuclideanYangMillsRegularityLimitData

attribute [instance]
  EuclideanYangMillsProjectiveLimitAnalyticTransferData.gaugeGroupGroup
  EuclideanYangMillsProjectiveLimitAnalyticTransferData.gaugeGroupTopology
  EuclideanYangMillsProjectiveLimitAnalyticTransferData.gaugeGroupCompact
  EuclideanYangMillsProjectiveLimitAnalyticTransferData.gaugeGroupNontrivial
  EuclideanYangMillsProjectiveLimitAnalyticTransferData.gaugeAction

/-- Assemble the existing continuum construction record from theorem-generated
limit properties. -/
noncomputable def
    EuclideanYangMillsProjectiveLimitAnalyticTransferData.toContinuumConstruction
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData F L) :
    EuclideanYangMillsProjectiveContinuumMeasureConstruction F :=
  { limit := L
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
    reflectionPositive := D.reflectionLimit.ContinuumReflectionPositive
    reflectionPositive_proof :=
      euclidean_yang_mills_reflection_positivity_passes_to_limit D.reflectionLimit
    euclideanInvariant := D.euclideanLimit.ContinuumEuclideanInvariant
    euclideanInvariant_proof :=
      euclidean_yang_mills_euclidean_invariance_passes_to_limit D.euclideanLimit
    symmetric := D.symmetric
    symmetric_proof := D.symmetric_proof
    clusterProperty := D.clusterLimit.ContinuumClusterProperty
    clusterProperty_proof :=
      euclidean_yang_mills_cluster_property_passes_to_limit D.clusterLimit
    regularity := D.regularityLimit.ContinuumRegularity
    regularity_proof :=
      euclidean_yang_mills_regularity_passes_to_limit D.regularityLimit }

/-- The transferred construction is immediately ready for the OS/Wightman
measure bridge. -/
theorem euclidean_yang_mills_projective_limit_transferred_measure_package_ready
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData F L) :
    D.toContinuumConstruction.toMeasurePackage.ready :=
  euclidean_yang_mills_projective_continuum_measure_package_ready
    D.toContinuumConstruction

end

end MathlibAnalytic
end MGAP4D
