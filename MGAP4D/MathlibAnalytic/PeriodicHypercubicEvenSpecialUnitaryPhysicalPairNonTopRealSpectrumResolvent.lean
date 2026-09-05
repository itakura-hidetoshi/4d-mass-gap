import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopPointSpectrumExclusion
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalPairNonTopRealSpectrumTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairNonTopRealSpectrumCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairNonTopRealSpectrumSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairNonTopRealSpectrumMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairNonTopRealSpectrumBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairNonTopRealSpectrumSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairNonTopRealSpectrumSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section NonTopRealSpectrumResolvent

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
local notation "NN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure H N hN beta hbeta
local notation "SN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator H N hN beta hbeta

/-- Every real scalar whose modulus lies strictly outside the finite-volume
non-top contraction factor belongs to the real resolvent set of the bundled
completed non-top transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_mem_realResolventSet_of_factor_lt_abs
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) :
    lambda ∈ resolventSet ℝ SN := by
  apply spectrum.mem_resolventSet_of_norm_lt
  simpa only [Real.norm_eq_abs] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_norm_le
      H N hN beta hbeta).trans_lt hlambda

/-- The full real spectrum, not merely the point spectrum, is bounded in modulus
by the finite-volume contraction factor inherited from the one-slice orthogonal
restriction. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realSpectrum_abs_le_factor
    (lambda : ℝ) (hlambda : lambda ∈ spectrum ℝ SN) :
    |lambda| ≤ ‖R‖ := by
  have hnorm : ‖lambda‖ ≤ ‖SN‖ :=
    spectrum.norm_le_norm_of_mem hlambda
  have hSN : ‖SN‖ ≤ ‖R‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_norm_le
      H N hN beta hbeta
  simpa only [Real.norm_eq_abs] using hnorm.trans hSN

/-- The finite-volume real spectrum of completed non-top transfer is contained
in the closed interval determined by the contraction factor. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realSpectrum_subset_Icc_factor :
    spectrum ℝ SN ⊆ Set.Icc (-‖R‖) ‖R‖ := by
  intro lambda hlambda
  exact abs_le.mp
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realSpectrum_abs_le_factor
      H N hN beta hbeta lambda hlambda)

/-- Since the contraction factor is strictly below one at each fixed finite
volume, the entire real non-top spectrum lies strictly inside the unit interval. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realSpectrum_subset_Ioo_unit :
    spectrum ℝ SN ⊆ Set.Ioo (-1) 1 := by
  intro lambda hlambda
  have habs : |lambda| ≤ ‖R‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realSpectrum_abs_le_factor
      H N hN beta hbeta lambda hlambda
  have hq : ‖R‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H N hN beta hbeta
  exact abs_lt.mp (habs.trans_lt hq)

/-- Audit-visible finite-volume real spectrum/resolvent separation package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopRealSpectrumResolventPackage :
    Prop where
  resolventOutsideFactor :
    ∀ lambda : ℝ, ‖R‖ < |lambda| → lambda ∈ resolventSet ℝ SN
  spectrumBound :
    ∀ lambda : ℝ, lambda ∈ spectrum ℝ SN → |lambda| ≤ ‖R‖
  spectrumInterval :
    spectrum ℝ SN ⊆ Set.Icc (-‖R‖) ‖R‖
  strictUnitSpectrum :
    spectrum ℝ SN ⊆ Set.Ioo (-1) 1

/-- Construct the finite-volume real spectrum/resolvent separation package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopRealSpectrumResolventPackage :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopRealSpectrumResolventPackage
      H N hN beta hbeta :=
  { resolventOutsideFactor :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_mem_realResolventSet_of_factor_lt_abs
        H N hN beta hbeta
    spectrumBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realSpectrum_abs_le_factor
        H N hN beta hbeta
    spectrumInterval :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realSpectrum_subset_Icc_factor
        H N hN beta hbeta
    strictUnitSpectrum :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realSpectrum_subset_Ioo_unit
        H N hN beta hbeta }

end NonTopRealSpectrumResolvent

end

end MathlibAnalytic
end MGAP4D
