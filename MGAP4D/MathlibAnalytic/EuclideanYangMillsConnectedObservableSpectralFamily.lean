import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine
import MGAP4D.MathlibAnalytic.WightmanOSConnectedCorrelationSpectralGap
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

attribute [instance] EuclideanYangMillsMeasurePackage.instMeasurableSpace

/-- The non-vacuum Hamiltonian energies of an explicitly reconstructed
OS/Wightman model. -/
abbrev ExplicitWightmanOSReconstructedModel.NonVacuumEnergy
    (M : ExplicitWightmanOSReconstructedModel) : Type :=
  {E : ℝ // E ∈ M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)}

/-- A Euclidean observable family indexed by every non-vacuum Hamiltonian
spectral energy.

The connected correlations are genuine Bochner integrals against the continuum
Euclidean Yang--Mills measure.  Each energy has a Hilbert-space source vector
whose singleton PVM projection is nonzero.  Thus its spectral weight is derived
from an actual PVM projection norm rather than supplied as a free positive
number. -/
structure EuclideanYangMillsConnectedObservableSpectralFamily where
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
  osSpectralLaplaceLowerBound :
    ∀ (e : explicitModel.NonVacuumEnergy) (t : ℝ), 0 ≤ t →
      ‖explicitModel.spectralPVM.projection ({(e : ℝ)} : Set ℝ)
        (sourceVector e)‖ * Real.exp (-(e : ℝ) * t) ≤
        connectedCorrelation e t
  exponentialClusteringUpperBound :
    ∀ (e : explicitModel.NonVacuumEnergy) (t : ℝ), 0 ≤ t →
      connectedCorrelation e t ≤
        decayConstant e * Real.exp (-exactGapValueReal * t)

/-- The PVM projection norm gives a strictly positive spectral weight for every
non-vacuum energy in the observable family. -/
theorem euclidean_connected_observable_spectralWeight_pos
    (B : EuclideanYangMillsConnectedObservableSpectralFamily)
    (e : B.explicitModel.NonVacuumEnergy) :
    0 < ‖B.explicitModel.spectralPVM.projection ({(e : ℝ)} : Set ℝ)
      (B.sourceVector e)‖ := by
  exact norm_pos_iff.mpr (B.projectedSource_ne_zero e)

/-- Every non-vacuum spectral energy has a concrete nonzero singleton-PVM
witness. -/
def EuclideanYangMillsConnectedObservableSpectralFamily.spectralWitness
    (B : EuclideanYangMillsConnectedObservableSpectralFamily)
    (e : B.explicitModel.NonVacuumEnergy) :
    ExplicitWightmanOSNonzeroSpectralPVMWitness B.explicitModel :=
  { energy := e
    energy_mem := e.property.1
    energy_ne_zero := by
      simpa using e.property.2
    source := B.sourceVector e
    projected_ne_zero := B.projectedSource_ne_zero e }

/-- Measure-defined connected correlations with uniform decay rate
`exactGapValueReal` exclude every lower non-vacuum Hamiltonian energy. -/
theorem euclidean_connected_observable_nonvacuum_spectrum_subset_Ici
    (B : EuclideanYangMillsConnectedObservableSpectralFamily) :
    B.explicitModel.hamiltonianEnergySpectrum \ ({0} : Set ℝ) ⊆
      Set.Ici exactGapValueReal := by
  intro E hE
  let e : B.explicitModel.NonVacuumEnergy := ⟨E, hE⟩
  show exactGapValueReal ≤ E
  by_contra hNot
  have hSubgap : E < exactGapValueReal := lt_of_not_ge hNot
  obtain ⟨t, ht, hSeparation⟩ :=
    exists_subgap_exponential_separation
      (euclidean_connected_observable_spectralWeight_pos B e)
      (B.decayConstant_nonneg e) hSubgap
  have hLower := B.osSpectralLaplaceLowerBound e t ht
  have hUpper := B.exponentialClusteringUpperBound e t ht
  change
    B.decayConstant e * Real.exp (-exactGapValueReal * t) <
      ‖B.explicitModel.spectralPVM.projection ({E} : Set ℝ)
        (B.sourceVector e)‖ * Real.exp (-E * t)
    at hSeparation
  linarith

/-- The concrete Euclidean observable family supplies a Hamiltonian mass gap
without using the legacy first-excitation positivity field. -/
theorem euclidean_connected_observable_hasHamiltonianMassGap
    (B : EuclideanYangMillsConnectedObservableSpectralFamily) :
    HasHamiltonianMassGap
      B.explicitModel.hamiltonianEnergySpectrum exactGapValueReal := by
  refine ⟨exactGapValueReal_pos, B.vacuumEnergySpectralValue, ?_⟩
  intro E hE hE0
  exact euclidean_connected_observable_nonvacuum_spectrum_subset_Ici B
    ⟨hE, by simpa using hE0⟩

/-- Choose the canonical vacuum-orthogonal spectrum bridge using the spectral
probe attached to a selected non-vacuum energy. -/
def EuclideanYangMillsConnectedObservableSpectralFamily.vacuumOrthogonalSpectrum
    (B : EuclideanYangMillsConnectedObservableSpectralFamily)
    (e : B.explicitModel.NonVacuumEnergy) :
    ExplicitWightmanOSVacuumOrthogonalSpectrumBridge B.explicitModel :=
  explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVM
    B.explicitModel B.pvmDisjointComposition (B.spectralWitness e)

/-- The exact normalized threshold as a non-vacuum energy, once spectral
attainment has been supplied. -/
def EuclideanYangMillsConnectedObservableSpectralFamily.exactEnergy
    (B : EuclideanYangMillsConnectedObservableSpectralFamily)
    (hExactSpectrum :
      exactGapValueReal ∈ B.explicitModel.hamiltonianEnergySpectrum) :
    B.explicitModel.NonVacuumEnergy :=
  ⟨exactGapValueReal,
    ⟨hExactSpectrum, by simpa using (ne_of_gt exactGapValueReal_pos)⟩⟩

/-- If the exact decay threshold is attained by the Hamiltonian spectrum, the
measure-defined connected correlations identify the exact physical gap on
`Ω⊥`. -/
theorem euclidean_connected_observable_vacuum_orthogonal_exact_gap
    (B : EuclideanYangMillsConnectedObservableSpectralFamily)
    (hExactSpectrum :
      exactGapValueReal ∈ B.explicitModel.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      (B.vacuumOrthogonalSpectrum
        (B.exactEnergy hExactSpectrum)).restrictedSpectrum ⊆
        Set.Ici exactGapValueReal ∧
      sInf
        (B.vacuumOrthogonalSpectrum
          (B.exactEnergy hExactSpectrum)).restrictedSpectrum =
        exactGapValueReal := by
  have hGap := euclidean_connected_observable_hasHamiltonianMassGap B
  exact ⟨exactGapValueReal_pos,
    vacuum_orthogonal_restrictedSpectrum_subset_Ici
      (B.vacuumOrthogonalSpectrum (B.exactEnergy hExactSpectrum)) hGap,
    vacuum_orthogonal_restrictedSpectrum_sInf_eq
      (B.vacuumOrthogonalSpectrum (B.exactEnergy hExactSpectrum))
      hGap hExactSpectrum⟩

end

end MathlibAnalytic
end MGAP4D
