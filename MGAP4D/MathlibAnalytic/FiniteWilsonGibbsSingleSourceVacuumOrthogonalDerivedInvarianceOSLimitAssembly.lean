import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceCoerciveTransferOrbitOSLimitAssembly
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalDerivedInvarianceTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Complete continuum OS assembly whose finite-volume mass gap is imposed only
on the vacuum-orthogonal sector, while invariance of that sector is generated
from Hamiltonian symmetry and zero vacuum energy. -/
structure FiniteWilsonOSAutomaticVacuumOrthogonalDerivedInvarianceAnalyticLimitConstructionData
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
  clusterVacuumDerived :
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalDerivedInvarianceTransferOrbitContractionData W
  regularityLimit : FiniteWilsonOSAutomaticRegularityLimitData W

attribute [instance]
  FiniteWilsonOSAutomaticVacuumOrthogonalDerivedInvarianceAnalyticLimitConstructionData.gaugeGroupGroup
  FiniteWilsonOSAutomaticVacuumOrthogonalDerivedInvarianceAnalyticLimitConstructionData.gaugeGroupTopology
  FiniteWilsonOSAutomaticVacuumOrthogonalDerivedInvarianceAnalyticLimitConstructionData.gaugeGroupCompact
  FiniteWilsonOSAutomaticVacuumOrthogonalDerivedInvarianceAnalyticLimitConstructionData.gaugeGroupNontrivial
  FiniteWilsonOSAutomaticVacuumOrthogonalDerivedInvarianceAnalyticLimitConstructionData.gaugeAction

/-- Enter the established coercive continuum assembly after restricting to the
physical excitation sector and generating its invariance. -/
noncomputable def
    FiniteWilsonOSAutomaticVacuumOrthogonalDerivedInvarianceAnalyticLimitConstructionData.toCoerciveTransferOrbitAnalyticData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticVacuumOrthogonalDerivedInvarianceAnalyticLimitConstructionData W F L) :
    FiniteWilsonOSAutomaticCoerciveTransferOrbitAnalyticLimitConstructionData W F L :=
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
    clusterCoercive :=
      D.clusterVacuumDerived.toVacuumOrthogonalData.toCoerciveTransferOrbitData
    regularityLimit := D.regularityLimit }

/-- Reflection positivity, Euclidean invariance, exact-gap clustering on the
non-vacuum sector, and regularity hold simultaneously. -/
theorem finite_wilson_os_vacuum_orthogonal_derived_invariance_four_limit_properties
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticVacuumOrthogonalDerivedInvarianceAnalyticLimitConstructionData W F L) :
    D.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_coercive_transfer_orbit_four_limit_properties
    D.toCoerciveTransferOrbitAnalyticData

/-- The continuum connected correlation inherits the physical excitation-sector
exact-gap estimate. -/
theorem finite_wilson_os_vacuum_orthogonal_derived_invariance_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticVacuumOrthogonalDerivedInvarianceAnalyticLimitConstructionData W F L)
    (O : D.clusterVacuumDerived.Observable) (r : ℕ) :
    ‖D.clusterVacuumDerived.continuumConnectedCorrelation O r‖ ≤
      D.clusterVacuumDerived.decayAmplitude O *
        exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_vacuum_orthogonal_derived_invariance_continuum_bound
    D.clusterVacuumDerived O r

/-- The vacuum-orthogonal derived-invariance continuum package is
OS/Wightman-ready. -/
theorem finite_wilson_os_vacuum_orthogonal_derived_invariance_measure_package_ready
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticVacuumOrthogonalDerivedInvarianceAnalyticLimitConstructionData W F L) :
    D.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.toProjectiveLimitTransferData.toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_os_coercive_transfer_orbit_continuum_measure_package_ready
    D.toCoerciveTransferOrbitAnalyticData

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

abbrev FiniteWilsonGibbsSingleSourceVacuumOrthogonalDerivedInvarianceOSLimitData :=
  FiniteWilsonOSAutomaticVacuumOrthogonalDerivedInvarianceAnalyticLimitConstructionData W
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.projectiveLimitMeasure

/-- The explicit common-source continuum law is OS/Wightman-ready with the gap
placed on the generated physical excitation sector. -/
theorem finite_wilson_single_source_vacuum_orthogonal_derived_invariance_os_limit_ready
    (D : FiniteWilsonGibbsSingleSourceVacuumOrthogonalDerivedInvarianceOSLimitData R) :
    (R.explicitOSContinuumConstruction
      (R.automaticOSLimitTransferData
        D.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_coercive_transfer_orbit_os_limit_ready
    R D.toCoerciveTransferOrbitAnalyticData

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

/-- All four continuum routes are OS/Wightman-ready with theorem-generated
vacuum-sector invariance. -/
theorem finite_wilson_single_source_vacuum_orthogonal_derived_invariance_four_routes_ready
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceVacuumOrthogonalDerivedInvarianceOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_coercive_transfer_orbit_four_routes_ready
    R S D.toCoerciveTransferOrbitAnalyticData

/-- All four routes use the explicit `globalObserve` pushforward law. -/
theorem finite_wilson_single_source_vacuum_orthogonal_derived_invariance_four_route_measures_eq_explicit
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceVacuumOrthogonalDerivedInvarianceOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure :=
  finite_wilson_single_source_coercive_transfer_orbit_four_route_measures_eq_explicit
    R S D.toCoerciveTransferOrbitAnalyticData

end

end MathlibAnalytic
end MGAP4D
