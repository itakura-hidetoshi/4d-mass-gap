import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceFreePositiveInteractionOSLimitAssembly
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContraction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Complete continuum OS assembly in which the finite-volume free Hamiltonian
is constructed from explicit orthonormal modes and mode energies, and the
interaction Hamiltonian is positive. -/
structure FiniteWilsonOSAutomaticModeDiagonalFreePositiveInteractionAnalyticLimitConstructionData
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
  clusterModeDiagonalFreePositive :
    FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContractionData W
  regularityLimit : FiniteWilsonOSAutomaticRegularityLimitData W

attribute [instance]
  FiniteWilsonOSAutomaticModeDiagonalFreePositiveInteractionAnalyticLimitConstructionData.gaugeGroupGroup
  FiniteWilsonOSAutomaticModeDiagonalFreePositiveInteractionAnalyticLimitConstructionData.gaugeGroupTopology
  FiniteWilsonOSAutomaticModeDiagonalFreePositiveInteractionAnalyticLimitConstructionData.gaugeGroupCompact
  FiniteWilsonOSAutomaticModeDiagonalFreePositiveInteractionAnalyticLimitConstructionData.gaugeGroupNontrivial
  FiniteWilsonOSAutomaticModeDiagonalFreePositiveInteractionAnalyticLimitConstructionData.gaugeAction

/-- Enter the already established free-plus-positive-interaction assembly only
after deriving free coercivity from the explicit mode-energy lower bounds. -/
noncomputable def
    FiniteWilsonOSAutomaticModeDiagonalFreePositiveInteractionAnalyticLimitConstructionData.toFreePositiveInteractionAnalyticData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticModeDiagonalFreePositiveInteractionAnalyticLimitConstructionData W F L) :
    FiniteWilsonOSAutomaticFreePositiveInteractionAnalyticLimitConstructionData W F L :=
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
    clusterFreePositive :=
      D.clusterModeDiagonalFreePositive.toFreePositiveInteractionData
    regularityLimit := D.regularityLimit }

/-- Reflection positivity, Euclidean invariance, exact-gap clustering, and
regularity hold when the free mode energies have the uniform lower bound and
the interaction is positive. -/
theorem finite_wilson_os_mode_diagonal_free_positive_interaction_four_limit_properties
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticModeDiagonalFreePositiveInteractionAnalyticLimitConstructionData W F L) :
    D.toFreePositiveInteractionAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toFreePositiveInteractionAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toFreePositiveInteractionAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toFreePositiveInteractionAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_free_positive_interaction_four_limit_properties
    D.toFreePositiveInteractionAnalyticData

/-- The continuum connected correlation inherits the exact-gap estimate from
the explicit mode-energy lower bound and positivity of the interaction. -/
theorem finite_wilson_os_mode_diagonal_free_positive_interaction_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticModeDiagonalFreePositiveInteractionAnalyticLimitConstructionData W F L)
    (O : D.clusterModeDiagonalFreePositive.Observable) (r : ℕ) :
    ‖D.clusterModeDiagonalFreePositive.continuumConnectedCorrelation O r‖ ≤
      D.clusterModeDiagonalFreePositive.decayAmplitude O *
        exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_mode_diagonal_free_positive_interaction_continuum_bound
    D.clusterModeDiagonalFreePositive O r

/-- The mode-diagonal free-plus-positive-interaction continuum package is
OS/Wightman-ready. -/
theorem finite_wilson_os_mode_diagonal_free_positive_interaction_continuum_measure_package_ready
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticModeDiagonalFreePositiveInteractionAnalyticLimitConstructionData W F L) :
    D.toFreePositiveInteractionAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.toProjectiveLimitTransferData.toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_os_free_positive_interaction_continuum_measure_package_ready
    D.toFreePositiveInteractionAnalyticData

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

abbrev FiniteWilsonGibbsSingleSourceModeDiagonalFreePositiveInteractionOSLimitData :=
  FiniteWilsonOSAutomaticModeDiagonalFreePositiveInteractionAnalyticLimitConstructionData W
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.projectiveLimitMeasure

/-- The explicit common-source continuum law is OS/Wightman-ready when free
coercivity is generated from explicit mode energies. -/
theorem finite_wilson_single_source_mode_diagonal_free_positive_interaction_os_limit_ready
    (D : FiniteWilsonGibbsSingleSourceModeDiagonalFreePositiveInteractionOSLimitData R) :
    (R.explicitOSContinuumConstruction
      (R.automaticOSLimitTransferData
        D.toFreePositiveInteractionAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_free_positive_interaction_os_limit_ready
    R D.toFreePositiveInteractionAnalyticData

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

/-- All four continuum construction routes are OS/Wightman-ready under the
mode-diagonal free-plus-positive-interaction decomposition. -/
theorem finite_wilson_single_source_mode_diagonal_free_positive_interaction_four_routes_ready
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceModeDiagonalFreePositiveInteractionOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toFreePositiveInteractionAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toFreePositiveInteractionAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toFreePositiveInteractionAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toFreePositiveInteractionAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_free_positive_interaction_four_routes_ready
    R S D.toFreePositiveInteractionAnalyticData

/-- All four routes use exactly the explicit `globalObserve` pushforward law. -/
theorem finite_wilson_single_source_mode_diagonal_free_positive_interaction_four_route_measures_eq_explicit
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceModeDiagonalFreePositiveInteractionOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toFreePositiveInteractionAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toFreePositiveInteractionAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toFreePositiveInteractionAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toFreePositiveInteractionAnalyticData.toCoerciveTransferOrbitAnalyticData.toConstructedTransferOrbitAnalyticData.toConstructedHamiltonianTransferAnalyticData.toHamiltonianEigenactionAnalyticData.toFiniteDimensionalHamiltonianAnalyticData.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure :=
  finite_wilson_single_source_free_positive_interaction_four_route_measures_eq_explicit
    R S D.toFreePositiveInteractionAnalyticData

end

end MathlibAnalytic
end MGAP4D
