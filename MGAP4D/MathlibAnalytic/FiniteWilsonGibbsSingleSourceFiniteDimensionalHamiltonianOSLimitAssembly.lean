import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceOrthonormalEigenbasisOSLimitAssembly
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContraction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The automatic finite-Wilson continuum package with clustering controlled
by a finite-dimensional symmetric Hamiltonian whose generated eigenvalues are
uniformly bounded below by the public exact gap. -/
structure FiniteWilsonOSAutomaticFiniteDimensionalHamiltonianAnalyticLimitConstructionData
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
  clusterHamiltonian :
    FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W
  regularityLimit : FiniteWilsonOSAutomaticRegularityLimitData W

attribute [instance]
  FiniteWilsonOSAutomaticFiniteDimensionalHamiltonianAnalyticLimitConstructionData.gaugeGroupGroup
  FiniteWilsonOSAutomaticFiniteDimensionalHamiltonianAnalyticLimitConstructionData.gaugeGroupTopology
  FiniteWilsonOSAutomaticFiniteDimensionalHamiltonianAnalyticLimitConstructionData.gaugeGroupCompact
  FiniteWilsonOSAutomaticFiniteDimensionalHamiltonianAnalyticLimitConstructionData.gaugeGroupNontrivial
  FiniteWilsonOSAutomaticFiniteDimensionalHamiltonianAnalyticLimitConstructionData.gaugeAction

/-- Apply mathlib's finite-dimensional spectral theorem before entering the
orthonormal-eigenbasis continuum assembly. -/
noncomputable def
    FiniteWilsonOSAutomaticFiniteDimensionalHamiltonianAnalyticLimitConstructionData.toOrthonormalEigenbasisAnalyticData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticFiniteDimensionalHamiltonianAnalyticLimitConstructionData W F L) :
    FiniteWilsonOSAutomaticOrthonormalEigenbasisAnalyticLimitConstructionData W F L :=
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
    clusterEigenbasis := D.clusterHamiltonian.toOrthonormalEigenbasisData
    regularityLimit := D.regularityLimit }

/-- Reflection positivity, Euclidean invariance, Hamiltonian exact-gap
clustering, and regularity hold simultaneously for the continuum law. -/
theorem finite_wilson_os_finite_dimensional_hamiltonian_four_limit_properties
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticFiniteDimensionalHamiltonianAnalyticLimitConstructionData W F L) :
    D.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_orthonormal_eigenbasis_four_limit_properties
    D.toOrthonormalEigenbasisAnalyticData

/-- The continuum connected correlation inherits the exact-gap estimate from
the finite-dimensional Hamiltonian spectrum. -/
theorem finite_wilson_os_finite_dimensional_hamiltonian_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticFiniteDimensionalHamiltonianAnalyticLimitConstructionData W F L)
    (O : D.clusterHamiltonian.Observable) (r : ℕ) :
    ‖D.clusterHamiltonian.continuumConnectedCorrelation O r‖ ≤
      D.clusterHamiltonian.decayAmplitude O *
        exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_finite_dimensional_hamiltonian_continuum_bound
    D.clusterHamiltonian O r

/-- The finite-dimensional-Hamiltonian continuum measure package is
OS/Wightman-ready. -/
theorem finite_wilson_os_finite_dimensional_hamiltonian_continuum_measure_package_ready
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticFiniteDimensionalHamiltonianAnalyticLimitConstructionData W F L) :
    D.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.toProjectiveLimitTransferData.toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_os_orthonormal_eigenbasis_continuum_measure_package_ready
    D.toOrthonormalEigenbasisAnalyticData

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Finite-dimensional-Hamiltonian analytic data for the explicit common-source
Wilson continuum law. -/
abbrev FiniteWilsonGibbsSingleSourceFiniteDimensionalHamiltonianOSLimitData :=
  FiniteWilsonOSAutomaticFiniteDimensionalHamiltonianAnalyticLimitConstructionData W
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.projectiveLimitMeasure

/-- The explicit common-source Wilson continuum law is OS/Wightman-ready when
clustering is controlled by the finite-dimensional Hamiltonian spectrum. -/
theorem finite_wilson_single_source_finite_dimensional_hamiltonian_os_limit_ready
    (D : FiniteWilsonGibbsSingleSourceFiniteDimensionalHamiltonianOSLimitData R) :
    (R.explicitOSContinuumConstruction
      (R.automaticOSLimitTransferData
        D.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_orthonormal_eigenbasis_os_limit_ready
    R D.toOrthonormalEigenbasisAnalyticData

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

/-- All four continuum routes are simultaneously OS/Wightman-ready with
clustering controlled by the finite-dimensional Hamiltonian spectrum. -/
theorem finite_wilson_single_source_finite_dimensional_hamiltonian_four_routes_ready
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceFiniteDimensionalHamiltonianOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_orthonormal_eigenbasis_four_routes_ready
    R S D.toOrthonormalEigenbasisAnalyticData

/-- All four finite-dimensional-Hamiltonian constructions use exactly the
explicit `globalObserve` pushforward continuum law. -/
theorem finite_wilson_single_source_finite_dimensional_hamiltonian_four_route_measures_eq_explicit
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceFiniteDimensionalHamiltonianOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toOrthonormalEigenbasisAnalyticData.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure :=
  finite_wilson_single_source_orthonormal_eigenbasis_four_route_measures_eq_explicit
    R S D.toOrthonormalEigenbasisAnalyticData

end

end MathlibAnalytic
end MGAP4D
