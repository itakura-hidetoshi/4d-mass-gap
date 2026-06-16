import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceVacuumOrthogonalDerivedInvarianceOSLimitAssembly
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumPoincareTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Complete continuum OS assembly whose finite-volume mass gap is generated
from a vacuum-centered Poincare inequality for the Wilson Dirichlet form. -/
structure FiniteWilsonOSAutomaticVacuumPoincareAnalyticLimitConstructionData
    (W : FiniteWilsonOSAutomaticApproximationFamily)
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
  symmetric : Prop
  symmetric_proof : symmetric
  reflectionLimit : FiniteWilsonOSAutomaticReflectionLimitData W
  euclideanLimit : FiniteWilsonOSAutomaticEuclideanLimitData W
  clusterPoincare :
    FiniteWilsonOSAutomaticExactGapVacuumPoincareTransferOrbitContractionData W
  regularityLimit : FiniteWilsonOSAutomaticRegularityLimitData W

attribute [instance]
  FiniteWilsonOSAutomaticVacuumPoincareAnalyticLimitConstructionData.gaugeGroupGroup
  FiniteWilsonOSAutomaticVacuumPoincareAnalyticLimitConstructionData.gaugeGroupTopology
  FiniteWilsonOSAutomaticVacuumPoincareAnalyticLimitConstructionData.gaugeGroupCompact
  FiniteWilsonOSAutomaticVacuumPoincareAnalyticLimitConstructionData.gaugeGroupNontrivial
  FiniteWilsonOSAutomaticVacuumPoincareAnalyticLimitConstructionData.gaugeAction

/-- Enter the established vacuum-orthogonal continuum assembly after deriving
coercivity from the Wilson Poincare inequality. -/
noncomputable def
    FiniteWilsonOSAutomaticVacuumPoincareAnalyticLimitConstructionData.toVacuumOrthogonalDerivedInvarianceAnalyticData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticVacuumPoincareAnalyticLimitConstructionData W F L) :
    FiniteWilsonOSAutomaticVacuumOrthogonalDerivedInvarianceAnalyticLimitConstructionData W F L :=
  { gaugeGroup := D.gaugeGroup
    gaugeGroupGroup := D.gaugeGroupGroup
    gaugeGroupTopology := D.gaugeGroupTopology
    gaugeGroupCompact := D.gaugeGroupCompact
    gaugeGroupNontrivial := D.gaugeGroupNontrivial
    gaugeAction := D.gaugeAction
    gaugeActionMeasurable := D.gaugeActionMeasurable
    gaugeInvariant := D.gaugeInvariant
    fieldAlgebra := D.fieldAlgebra
    schwingerFunctions := D.schwingerFunctions
    symmetric := D.symmetric
    symmetric_proof := D.symmetric_proof
    reflectionLimit := D.reflectionLimit
    euclideanLimit := D.euclideanLimit
    clusterVacuumDerived := D.clusterPoincare.toDerivedInvarianceData
    regularityLimit := D.regularityLimit }

/-- Reflection positivity, Euclidean invariance, Poincare-generated clustering,
and regularity hold simultaneously. -/
theorem finite_wilson_os_vacuum_poincare_four_limit_properties
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticVacuumPoincareAnalyticLimitConstructionData W F L) :
    D.toVacuumOrthogonalDerivedInvarianceAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toVacuumOrthogonalDerivedInvarianceAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toVacuumOrthogonalDerivedInvarianceAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toVacuumOrthogonalDerivedInvarianceAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_vacuum_orthogonal_derived_invariance_four_limit_properties
    D.toVacuumOrthogonalDerivedInvarianceAnalyticData

/-- The continuum connected correlation inherits the exact-gap estimate from
the vacuum-centered Wilson Poincare inequality. -/
theorem finite_wilson_os_vacuum_poincare_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticVacuumPoincareAnalyticLimitConstructionData W F L)
    (O : D.clusterPoincare.Observable) (r : ℕ) :
    ‖D.clusterPoincare.continuumConnectedCorrelation O r‖ ≤
      D.clusterPoincare.decayAmplitude O *
        exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_vacuum_poincare_continuum_bound
    D.clusterPoincare O r

/-- The vacuum-Poincare continuum package is OS/Wightman-ready. -/
theorem finite_wilson_os_vacuum_poincare_measure_package_ready
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticVacuumPoincareAnalyticLimitConstructionData W F L) :
    D.toVacuumOrthogonalDerivedInvarianceAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.toProjectiveLimitTransferData.toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_os_vacuum_orthogonal_derived_invariance_measure_package_ready
    D.toVacuumOrthogonalDerivedInvarianceAnalyticData

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

abbrev FiniteWilsonGibbsSingleSourceVacuumPoincareOSLimitData :=
  FiniteWilsonOSAutomaticVacuumPoincareAnalyticLimitConstructionData W
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.projectiveLimitMeasure

/-- The explicit common-source continuum law is OS/Wightman-ready when the
finite gap is generated from the Wilson Poincare inequality. -/
theorem finite_wilson_single_source_vacuum_poincare_os_limit_ready
    (D : FiniteWilsonGibbsSingleSourceVacuumPoincareOSLimitData R) :
    (R.explicitOSContinuumConstruction
      (R.automaticOSLimitTransferData
        D.toVacuumOrthogonalDerivedInvarianceAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_vacuum_orthogonal_derived_invariance_os_limit_ready
    R D.toVacuumOrthogonalDerivedInvarianceAnalyticData

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

/-- All four continuum construction routes are OS/Wightman-ready under the
vacuum-centered Poincare inequality. -/
theorem finite_wilson_single_source_vacuum_poincare_four_routes_ready
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceVacuumPoincareOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toVacuumOrthogonalDerivedInvarianceAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toVacuumOrthogonalDerivedInvarianceAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toVacuumOrthogonalDerivedInvarianceAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toVacuumOrthogonalDerivedInvarianceAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_vacuum_orthogonal_derived_invariance_four_routes_ready
    R S D.toVacuumOrthogonalDerivedInvarianceAnalyticData

/-- All four Poincare-driven routes use exactly the explicit `globalObserve`
pushforward continuum law. -/
theorem finite_wilson_single_source_vacuum_poincare_four_route_measures_eq_explicit
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceVacuumPoincareOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toVacuumOrthogonalDerivedInvarianceAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure = R.continuumMeasure ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toVacuumOrthogonalDerivedInvarianceAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure = R.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toVacuumOrthogonalDerivedInvarianceAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure = R.continuumMeasure ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toVacuumOrthogonalDerivedInvarianceAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure = R.continuumMeasure :=
  finite_wilson_single_source_vacuum_orthogonal_derived_invariance_four_route_measures_eq_explicit
    R S D.toVacuumOrthogonalDerivedInvarianceAnalyticData

end

end MathlibAnalytic
end MGAP4D
