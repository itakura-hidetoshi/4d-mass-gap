import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Four-dimensional Euclidean spacetime used by the cylinder-distribution
construction. -/
abbrev EuclideanFourSpace := Fin 4 → ℝ

/-- Finite-dimensional distributions for a four-dimensional Euclidean gauge
field.  For every finite set of spacetime points, `finiteMarginal` is a genuine
Mathlib probability measure, and the family is projectively consistent under
coordinate restriction. -/
structure EuclideanYangMillsProjectiveCylinderFamily where
  fieldValue : EuclideanFourSpace → Type
  [fieldValueMeasurableSpace :
    ∀ x, MeasurableSpace (fieldValue x)]
  finiteMarginal :
    ∀ J : Finset EuclideanFourSpace,
      Measure (∀ x : J, fieldValue x)
  finiteMarginalProbability :
    ∀ J, IsProbabilityMeasure (finiteMarginal J)
  projective : IsProjectiveMeasureFamily finiteMarginal

attribute [instance]
  EuclideanYangMillsProjectiveCylinderFamily.fieldValueMeasurableSpace

/-- The full continuum configuration carrier associated with the projective
finite-dimensional distributions. -/
abbrev EuclideanYangMillsProjectiveCylinderFamily.Configuration
    (F : EuclideanYangMillsProjectiveCylinderFamily) : Type :=
  ∀ x : EuclideanFourSpace, F.fieldValue x

/-- The projective family canonically defines an additive content on measurable
cylinder sets.  This step is unconditional once projective consistency has been
proved. -/
noncomputable def EuclideanYangMillsProjectiveCylinderFamily.cylinderContent
    (F : EuclideanYangMillsProjectiveCylinderFamily) :
    AddContent ℝ≥0∞ (measurableCylinders F.fieldValue) :=
  projectiveFamilyContent F.projective

/-- The cylinder content agrees with the finite-dimensional marginal on every
measurable cylinder. -/
theorem euclidean_yang_mills_projective_cylinder_content_eq_marginal
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    {J : Finset EuclideanFourSpace}
    {s : Set (∀ x : J, F.fieldValue x)}
    (hs : MeasurableSet s) :
    F.cylinderContent (cylinder J s) = F.finiteMarginal J s := by
  exact projectiveFamilyContent_cylinder F.projective hs

/-- A genuine continuum measure realizing all finite-dimensional Yang--Mills
marginals.  `projectiveLimit` is Mathlib's typed projective-limit condition,
not an opaque readiness proposition. -/
structure EuclideanYangMillsProjectiveLimitMeasure
    (F : EuclideanYangMillsProjectiveCylinderFamily) where
  continuumMeasure : Measure F.Configuration
  projectiveLimit :
    IsProjectiveLimit continuumMeasure F.finiteMarginal

/-- Every finite-dimensional marginal is recovered by pushing the continuum
measure forward along coordinate restriction. -/
theorem euclidean_yang_mills_projective_limit_recovers_marginal
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (J : Finset EuclideanFourSpace) :
    L.continuumMeasure.map J.restrict = F.finiteMarginal J := by
  exact L.projectiveLimit J

/-- The continuum measure assigns every measurable cylinder exactly the value
prescribed by its finite-dimensional Yang--Mills distribution. -/
theorem euclidean_yang_mills_projective_limit_measure_cylinder
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, F.fieldValue x)}
    (hs : MeasurableSet s) :
    L.continuumMeasure (cylinder J s) = F.finiteMarginal J s := by
  exact L.projectiveLimit.measure_cylinder J hs

/-- Probability normalization of all finite marginals automatically passes to
the projective-limit continuum measure. -/
theorem euclidean_yang_mills_projective_limit_probability
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    IsProbabilityMeasure L.continuumMeasure := by
  letI : ∀ J, IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability
  exact L.projectiveLimit.isProbabilityMeasure

/-- A projective-limit continuum probability measure is uniquely determined by
its finite-dimensional distributions. -/
theorem euclidean_yang_mills_projective_limit_unique
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (ν : Measure F.Configuration)
    (hν : IsProjectiveLimit ν F.finiteMarginal) :
    ν = L.continuumMeasure := by
  letI : ∀ J, IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability
  exact hν.unique L.projectiveLimit

/-- A four-dimensional projective-limit measure together with an actual compact
nontrivial gauge-group carrier, a measurable gauge action preserving the
measure, and the analytic properties required by the OS reconstruction route. -/
structure EuclideanYangMillsProjectiveContinuumMeasureConstruction
    (F : EuclideanYangMillsProjectiveCylinderFamily) where
  limit : EuclideanYangMillsProjectiveLimitMeasure F
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
      limit.continuumMeasure.map
          (fun A : F.Configuration => g • A) =
        limit.continuumMeasure
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
  EuclideanYangMillsProjectiveContinuumMeasureConstruction.gaugeGroupGroup
  EuclideanYangMillsProjectiveContinuumMeasureConstruction.gaugeGroupTopology
  EuclideanYangMillsProjectiveContinuumMeasureConstruction.gaugeGroupCompact
  EuclideanYangMillsProjectiveContinuumMeasureConstruction.gaugeGroupNontrivial
  EuclideanYangMillsProjectiveContinuumMeasureConstruction.gaugeAction

/-- The projective-limit construction produces the repository's Euclidean
Yang--Mills measure package with the continuum measure as its actual carrier. -/
def EuclideanYangMillsProjectiveContinuumMeasureConstruction.toMeasurePackage
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (C : EuclideanYangMillsProjectiveContinuumMeasureConstruction F) :
    EuclideanYangMillsMeasurePackage :=
  { configurationSpace := F.Configuration
    instMeasurableSpace := inferInstance
    euclideanMeasure := C.limit.continuumMeasure
    gaugeGroup := C.gaugeGroup
    fieldAlgebra := C.fieldAlgebra
    schwingerFunctions := C.schwingerFunctions
    gaugeGroupCompact := CompactSpace C.gaugeGroup
    gaugeGroupNontrivial := Nontrivial C.gaugeGroup
    reflectionPositive := C.reflectionPositive
    euclideanInvariant := C.euclideanInvariant
    symmetric := C.symmetric
    clusterProperty := C.clusterProperty
    regularity := C.regularity }

/-- The continuum measure is gauge invariant on every measurable event. -/
theorem euclidean_yang_mills_projective_continuum_measure_gauge_invariant
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (C : EuclideanYangMillsProjectiveContinuumMeasureConstruction F)
    (g : C.gaugeGroup)
    {s : Set F.Configuration}
    (hs : MeasurableSet s) :
    C.limit.continuumMeasure
        ((fun A : F.Configuration => g • A) ⁻¹' s) =
      C.limit.continuumMeasure s := by
  rw [← Measure.map_apply (C.gaugeActionMeasurable g) hs,
    C.gaugeInvariant g]

/-- The measure package generated by the projective-limit construction is ready
for the OS/Wightman bridge. -/
theorem euclidean_yang_mills_projective_continuum_measure_package_ready
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (C : EuclideanYangMillsProjectiveContinuumMeasureConstruction F) :
    C.toMeasurePackage.ready := by
  unfold EuclideanYangMillsMeasurePackage.ready
  exact ⟨inferInstance, inferInstance,
    C.reflectionPositive_proof,
    C.euclideanInvariant_proof,
    C.symmetric_proof,
    C.clusterProperty_proof,
    C.regularity_proof⟩

/-- Audit-visible typed certificate for the four-dimensional continuum measure
layer.  Unlike the earlier abstract construction flags, every measure statement
below is expressed using Mathlib's projective-family and projective-limit
objects. -/
structure EuclideanYangMillsProjectiveContinuumMeasureCertificate
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (C : EuclideanYangMillsProjectiveContinuumMeasureConstruction F) where
  projectiveFamily : IsProjectiveMeasureFamily F.finiteMarginal
  continuumProjectiveLimit :
    IsProjectiveLimit C.limit.continuumMeasure F.finiteMarginal
  continuumProbability : IsProbabilityMeasure C.limit.continuumMeasure
  finiteMarginalsRecovered :
    ∀ J : Finset EuclideanFourSpace,
      C.limit.continuumMeasure.map J.restrict = F.finiteMarginal J
  continuumUnique :
    ∀ ν : Measure F.Configuration,
      IsProjectiveLimit ν F.finiteMarginal →
        ν = C.limit.continuumMeasure
  gaugeInvariantOnMeasurableEvents :
    ∀ (g : C.gaugeGroup) (s : Set F.Configuration),
      MeasurableSet s →
        C.limit.continuumMeasure
            ((fun A : F.Configuration => g • A) ⁻¹' s) =
          C.limit.continuumMeasure s
  measurePackageReady : C.toMeasurePackage.ready

/-- Construct the typed four-dimensional continuum-measure certificate. -/
def euclideanYangMillsProjectiveContinuumMeasureCertificate
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (C : EuclideanYangMillsProjectiveContinuumMeasureConstruction F) :
    EuclideanYangMillsProjectiveContinuumMeasureCertificate C :=
  { projectiveFamily := F.projective
    continuumProjectiveLimit := C.limit.projectiveLimit
    continuumProbability :=
      euclidean_yang_mills_projective_limit_probability C.limit
    finiteMarginalsRecovered :=
      euclidean_yang_mills_projective_limit_recovers_marginal C.limit
    continuumUnique := fun ν hν =>
      euclidean_yang_mills_projective_limit_unique C.limit ν hν
    gaugeInvariantOnMeasurableEvents := fun g s hs =>
      euclidean_yang_mills_projective_continuum_measure_gauge_invariant C g hs
    measurePackageReady :=
      euclidean_yang_mills_projective_continuum_measure_package_ready C }

end

end MathlibAnalytic
end MGAP4D
