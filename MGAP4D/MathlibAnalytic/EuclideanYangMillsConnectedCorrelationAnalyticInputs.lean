import MGAP4D.MathlibAnalytic.EuclideanYangMillsConnectedObservableSpectralFamily

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Common concrete data shared by the two hard analytic inputs in the
connected-correlation route.

This core already contains the continuum Euclidean measure, observable family,
Bochner-integral correlation identity, PVM source vectors, and nonzero spectral
projections.  It deliberately contains neither the OS spectral Laplace lower
bound nor the exponential clustering upper bound. -/
structure EuclideanYangMillsConnectedObservableCore where
  continuum : EuclideanYangMillsContinuumMeasureConstructionSpine
  explicitModel : ExplicitWightmanOSReconstructedModel
  explicitLegacyAxioms_identified :
    explicitModel.axioms.toLegacy = continuum.definitionBridge.spine.axioms
  pvmDisjointComposition :
    explicitModel.spectralPVM.HasDisjointCompositionZero
  vacuumEnergySpectralValue :
    0 ∈ explicitModel.hamiltonianEnergySpectrum
  euclideanTimeTranslate :
    ℝ → continuum.measurePackage.configurationSpace →
      continuum.measurePackage.configurationSpace
  observable :
    explicitModel.NonVacuumEnergy →
      continuum.measurePackage.configurationSpace → ℝ
  observable_integrable :
    ∀ e : explicitModel.NonVacuumEnergy,
      Integrable (observable e) continuum.measurePackage.euclideanMeasure
  translatedObservable_integrable :
    ∀ (e : explicitModel.NonVacuumEnergy) (t : ℝ),
      Integrable
        (fun ω => observable e (euclideanTimeTranslate t ω))
        continuum.measurePackage.euclideanMeasure
  correlationProduct_integrable :
    ∀ (e : explicitModel.NonVacuumEnergy) (t : ℝ),
      Integrable
        (fun ω =>
          observable e (euclideanTimeTranslate t ω) * observable e ω)
        continuum.measurePackage.euclideanMeasure
  connectedCorrelation :
    explicitModel.NonVacuumEnergy → ℝ → ℝ
  connectedCorrelation_eq_measure_integral :
    ∀ (e : explicitModel.NonVacuumEnergy) (t : ℝ),
      connectedCorrelation e t =
        (∫ ω,
          observable e (euclideanTimeTranslate t ω) * observable e ω
          ∂continuum.measurePackage.euclideanMeasure) -
        (∫ ω,
          observable e (euclideanTimeTranslate t ω)
          ∂continuum.measurePackage.euclideanMeasure) *
        (∫ ω,
          observable e ω
          ∂continuum.measurePackage.euclideanMeasure)
  sourceVector :
    explicitModel.NonVacuumEnergy → explicitModel.H
  projectedSource_ne_zero :
    ∀ e : explicitModel.NonVacuumEnergy,
      explicitModel.spectralPVM.projection ({(e : ℝ)} : Set ℝ)
        (sourceVector e) ≠ 0
  decayConstant : explicitModel.NonVacuumEnergy → ℝ
  decayConstant_nonneg :
    ∀ e : explicitModel.NonVacuumEnergy, 0 ≤ decayConstant e

/-- First hard analytic input: OS reconstruction and the spectral theorem identify
its canonical positive singleton-PVM mass beneath the Euclidean connected
correlation. -/
structure EuclideanYangMillsOSSpectralLaplaceRepresentation
    (C : EuclideanYangMillsConnectedObservableCore) where
  lowerBound :
    ∀ (e : C.explicitModel.NonVacuumEnergy) (t : ℝ), 0 ≤ t →
      ‖C.explicitModel.spectralPVM.projection ({(e : ℝ)} : Set ℝ)
        (C.sourceVector e)‖ ^ 2 * Real.exp (-(e : ℝ) * t) ≤
        C.connectedCorrelation e t

/-- Second hard analytic input: the connected Euclidean correlations decay
uniformly at the target rate `exactGapValueReal`. -/
structure EuclideanYangMillsExponentialClusteringEstimate
    (C : EuclideanYangMillsConnectedObservableCore) where
  upperBound :
    ∀ (e : C.explicitModel.NonVacuumEnergy) (t : ℝ), 0 ≤ t →
      C.connectedCorrelation e t ≤
        C.decayConstant e * Real.exp (-exactGapValueReal * t)

/-- Assemble the two independent analytic certificates into the previously
proved connected-observable spectral family. -/
def EuclideanYangMillsConnectedObservableCore.assemble
    (C : EuclideanYangMillsConnectedObservableCore)
    (L : EuclideanYangMillsOSSpectralLaplaceRepresentation C)
    (X : EuclideanYangMillsExponentialClusteringEstimate C) :
    EuclideanYangMillsConnectedObservableSpectralFamily :=
  { continuum := C.continuum
    explicitModel := C.explicitModel
    explicitLegacyAxioms_identified := C.explicitLegacyAxioms_identified
    pvmDisjointComposition := C.pvmDisjointComposition
    vacuumEnergySpectralValue := C.vacuumEnergySpectralValue
    euclideanTimeTranslate := C.euclideanTimeTranslate
    observable := C.observable
    observable_integrable := C.observable_integrable
    translatedObservable_integrable := C.translatedObservable_integrable
    correlationProduct_integrable := C.correlationProduct_integrable
    connectedCorrelation := C.connectedCorrelation
    connectedCorrelation_eq_measure_integral :=
      C.connectedCorrelation_eq_measure_integral
    sourceVector := C.sourceVector
    projectedSource_ne_zero := C.projectedSource_ne_zero
    decayConstant := C.decayConstant
    decayConstant_nonneg := C.decayConstant_nonneg
    osSpectralLaplaceLowerBound := L.lowerBound
    exponentialClusteringUpperBound := X.upperBound }

/-- The two analytic inputs imply the Hamiltonian mass gap.  This theorem makes
clear that all remaining analytic work is localized in `L` and `X`. -/
theorem euclidean_connected_correlation_analytic_inputs_hasHamiltonianMassGap
    (C : EuclideanYangMillsConnectedObservableCore)
    (L : EuclideanYangMillsOSSpectralLaplaceRepresentation C)
    (X : EuclideanYangMillsExponentialClusteringEstimate C) :
    HasHamiltonianMassGap
      C.explicitModel.hamiltonianEnergySpectrum exactGapValueReal := by
  exact euclidean_connected_observable_hasHamiltonianMassGap
    (C.assemble L X)

/-- The same separated inputs give the exact physical vacuum-orthogonal gap once
spectral attainment of the threshold is supplied. -/
theorem euclidean_connected_correlation_analytic_inputs_exact_gap
    (C : EuclideanYangMillsConnectedObservableCore)
    (L : EuclideanYangMillsOSSpectralLaplaceRepresentation C)
    (X : EuclideanYangMillsExponentialClusteringEstimate C)
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      ((C.assemble L X).vacuumOrthogonalSpectrum
        ((C.assemble L X).exactEnergy hExactSpectrum)).restrictedSpectrum ⊆
        Set.Ici exactGapValueReal ∧
      sInf
        ((C.assemble L X).vacuumOrthogonalSpectrum
          ((C.assemble L X).exactEnergy hExactSpectrum)).restrictedSpectrum =
        exactGapValueReal := by
  exact euclidean_connected_observable_vacuum_orthogonal_exact_gap
    (C.assemble L X) hExactSpectrum

end

end MathlibAnalytic
end MGAP4D
