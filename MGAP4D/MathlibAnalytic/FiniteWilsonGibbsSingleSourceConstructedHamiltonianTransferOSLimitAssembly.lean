import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceHamiltonianEigenactionOSLimitAssembly
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedHamiltonianTransferContraction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The automatic finite-Wilson continuum package in which the finite-volume
transfer operator is canonically constructed as `diag (exp (-Eᵢ))` in the
mathlib-generated eigenbasis of a symmetric Hamiltonian. -/
structure FiniteWilsonOSAutomaticConstructedHamiltonianTransferAnalyticLimitConstructionData
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
  clusterConstructed :
    FiniteWilsonOSAutomaticExactGapConstructedHamiltonianTransferContractionData W
  regularityLimit : FiniteWilsonOSAutomaticRegularityLimitData W

attribute [instance]
  FiniteWilsonOSAutomaticConstructedHamiltonianTransferAnalyticLimitConstructionData.gaugeGroupGroup
  FiniteWilsonOSAutomaticConstructedHamiltonianTransferAnalyticLimitConstructionData.gaugeGroupTopology
  FiniteWilsonOSAutomaticConstructedHamiltonianTransferAnalyticLimitConstructionData.gaugeGroupCompact
  FiniteWilsonOSAutomaticConstructedHamiltonianTransferAnalyticLimitConstructionData.gaugeGroupNontrivial
  FiniteWilsonOSAutomaticConstructedHamiltonianTransferAnalyticLimitConstructionData.gaugeAction

/-- Enter the Hamiltonian-eigenaction assembly only after constructing the
transfer operator and proving its symmetry and eigenaction. -/
noncomputable def
    FiniteWilsonOSAutomaticConstructedHamiltonianTransferAnalyticLimitConstructionData.toHamiltonianEigenactionAnalyticData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticConstructedHamiltonianTransferAnalyticLimitConstructionData W F L) :
    FiniteWilsonOSAutomaticHamiltonianEigenactionAnalyticLimitConstructionData W F L :=
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
    clusterEigenaction := D.clusterConstructed.toHamiltonianEigenactionData
    regularityLimit := D.regularityLimit }

/-- Reflection positivity, Euclidean invariance, exact-gap clustering from the
constructed Hamiltonian transfer operator, and regularity hold simultaneously. -/
theorem finite_wilson_os_constructed_hamiltonian_transfer_four_limit_properties
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticConstructedHamiltonianTransferAnalyticLimitConstructionData W F L) :
    D.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_hamiltonian_eigenaction_four_limit_properties
    D.toHamiltonianEigenactionAnalyticData

/-- The continuum connected correlation inherits the exact-gap estimate from
the canonically constructed finite-volume transfer operator. -/
theorem finite_wilson_os_constructed_hamiltonian_transfer_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticConstructedHamiltonianTransferAnalyticLimitConstructionData W F L)
    (O : D.clusterConstructed.Observable) (r : ℕ) :
    ‖D.clusterConstructed.continuumConnectedCorrelation O r‖ ≤
      D.clusterConstructed.decayAmplitude O *
        exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_constructed_hamiltonian_transfer_continuum_bound
    D.clusterConstructed O r

/-- The constructed-Hamiltonian-transfer continuum measure package is
OS/Wightman-ready. -/
theorem finite_wilson_os_constructed_hamiltonian_transfer_continuum_measure_package_ready
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticConstructedHamiltonianTransferAnalyticLimitConstructionData W F L) :
    D.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.toProjectiveLimitTransferData.toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_os_hamiltonian_eigenaction_continuum_measure_package_ready
    D.toHamiltonianEigenactionAnalyticData

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Constructed-Hamiltonian-transfer analytic data for the explicit
common-source Wilson continuum law. -/
abbrev FiniteWilsonGibbsSingleSourceConstructedHamiltonianTransferOSLimitData :=
  FiniteWilsonOSAutomaticConstructedHamiltonianTransferAnalyticLimitConstructionData W
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.projectiveLimitMeasure

/-- The explicit common-source continuum law is OS/Wightman-ready when its
finite-volume transfer operator is constructed from the Hamiltonian spectrum. -/
theorem finite_wilson_single_source_constructed_hamiltonian_transfer_os_limit_ready
    (D : FiniteWilsonGibbsSingleSourceConstructedHamiltonianTransferOSLimitData R) :
    (R.explicitOSContinuumConstruction
      (R.automaticOSLimitTransferData
        D.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_hamiltonian_eigenaction_os_limit_ready
    R D.toHamiltonianEigenactionAnalyticData

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

/-- All four continuum routes are OS/Wightman-ready with clustering generated
from the canonically constructed Hamiltonian transfer operator. -/
theorem finite_wilson_single_source_constructed_hamiltonian_transfer_four_routes_ready
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceConstructedHamiltonianTransferOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_hamiltonian_eigenaction_four_routes_ready
    R S D.toHamiltonianEigenactionAnalyticData

/-- All four constructed-Hamiltonian-transfer routes use exactly the explicit
`globalObserve` pushforward continuum law. -/
theorem finite_wilson_single_source_constructed_hamiltonian_transfer_four_route_measures_eq_explicit
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceConstructedHamiltonianTransferOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure :=
  finite_wilson_single_source_hamiltonian_eigenaction_four_route_measures_eq_explicit
    R S D.toHamiltonianEigenactionAnalyticData

end

end MathlibAnalytic
end MGAP4D
