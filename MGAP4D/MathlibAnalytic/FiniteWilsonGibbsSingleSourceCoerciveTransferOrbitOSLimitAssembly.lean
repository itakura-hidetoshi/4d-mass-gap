import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceConstructedTransferOrbitOSLimitAssembly
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Complete continuum OS assembly whose finite-volume Hamiltonian spectral gap
is generated from a basis-free coercive estimate. -/
structure FiniteWilsonOSAutomaticCoerciveTransferOrbitAnalyticLimitConstructionData
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
  clusterCoercive :
    FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData W
  regularityLimit : FiniteWilsonOSAutomaticRegularityLimitData W

attribute [instance]
  FiniteWilsonOSAutomaticCoerciveTransferOrbitAnalyticLimitConstructionData.gaugeGroupGroup
  FiniteWilsonOSAutomaticCoerciveTransferOrbitAnalyticLimitConstructionData.gaugeGroupTopology
  FiniteWilsonOSAutomaticCoerciveTransferOrbitAnalyticLimitConstructionData.gaugeGroupCompact
  FiniteWilsonOSAutomaticCoerciveTransferOrbitAnalyticLimitConstructionData.gaugeGroupNontrivial
  FiniteWilsonOSAutomaticCoerciveTransferOrbitAnalyticLimitConstructionData.gaugeAction

/-- Enter the constructed-transfer-orbit assembly only after deriving the
Hamiltonian eigenvalue lower bound from coercivity. -/
noncomputable def
    FiniteWilsonOSAutomaticCoerciveTransferOrbitAnalyticLimitConstructionData.toConstructedTransferOrbitAnalyticData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticCoerciveTransferOrbitAnalyticLimitConstructionData W F L) :
    FiniteWilsonOSAutomaticConstructedTransferOrbitAnalyticLimitConstructionData W F L :=
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
    clusterOrbit := D.clusterCoercive.toConstructedTransferOrbitData
    regularityLimit := D.regularityLimit }

/-- Reflection positivity, Euclidean invariance, exact-gap clustering derived
from coercivity, and regularity hold simultaneously. -/
theorem finite_wilson_os_coercive_transfer_orbit_four_limit_properties
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticCoerciveTransferOrbitAnalyticLimitConstructionData W F L) :
    D.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_constructed_transfer_orbit_four_limit_properties
    D.toConstructedTransferOrbitAnalyticData

/-- The continuum connected correlation inherits the public exact-gap estimate
from the finite-volume coercive Hamiltonian inequality. -/
theorem finite_wilson_os_coercive_transfer_orbit_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticCoerciveTransferOrbitAnalyticLimitConstructionData W F L)
    (O : D.clusterCoercive.Observable) (r : ℕ) :
    ‖D.clusterCoercive.continuumConnectedCorrelation O r‖ ≤
      D.clusterCoercive.decayAmplitude O *
        exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_coercive_hamiltonian_continuum_bound
    D.clusterCoercive O r

/-- The coercive-Hamiltonian continuum measure package is OS/Wightman-ready. -/
theorem finite_wilson_os_coercive_transfer_orbit_continuum_measure_package_ready
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticCoerciveTransferOrbitAnalyticLimitConstructionData W F L) :
    D.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.toProjectiveLimitTransferData.toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_os_constructed_transfer_orbit_continuum_measure_package_ready
    D.toConstructedTransferOrbitAnalyticData

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Coercive-Hamiltonian analytic data for the explicit common-source Wilson
continuum law. -/
abbrev FiniteWilsonGibbsSingleSourceCoerciveTransferOrbitOSLimitData :=
  FiniteWilsonOSAutomaticCoerciveTransferOrbitAnalyticLimitConstructionData W
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.projectiveLimitMeasure

/-- The explicit common-source continuum law is OS/Wightman-ready when the
finite Hamiltonian gap is obtained from coercivity. -/
theorem finite_wilson_single_source_coercive_transfer_orbit_os_limit_ready
    (D : FiniteWilsonGibbsSingleSourceCoerciveTransferOrbitOSLimitData R) :
    (R.explicitOSContinuumConstruction
      (R.automaticOSLimitTransferData
        D.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_constructed_transfer_orbit_os_limit_ready
    R D.toConstructedTransferOrbitAnalyticData

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

/-- All four continuum routes are OS/Wightman-ready with the Hamiltonian gap
derived from coercivity. -/
theorem finite_wilson_single_source_coercive_transfer_orbit_four_routes_ready
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceCoerciveTransferOrbitOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_constructed_transfer_orbit_four_routes_ready
    R S D.toConstructedTransferOrbitAnalyticData

/-- All four coercive-Hamiltonian routes use exactly the explicit
`globalObserve` pushforward continuum law. -/
theorem finite_wilson_single_source_coercive_transfer_orbit_four_route_measures_eq_explicit
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceCoerciveTransferOrbitOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure :=
  finite_wilson_single_source_constructed_transfer_orbit_four_route_measures_eq_explicit
    R S D.toConstructedTransferOrbitAnalyticData

end

end MathlibAnalytic
end MGAP4D
