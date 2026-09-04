import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryOneSidedExcitationTransfer
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtSeparableKernelOperator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance pairPhysicalVacuumTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pairPhysicalVacuumCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pairPhysicalVacuumSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pairPhysicalVacuumMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pairPhysicalVacuumBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance pairPhysicalVacuumSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance pairPhysicalVacuumSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The physically selected pair-Haar vacuum vector: the normalized physical
one-slice top mode on each ordered endpoint. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  realL2ExternalTensor
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
      H N hN beta hbeta)

/-- The selected physical pair vacuum has unit norm. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
      H N hN beta hbeta‖ = 1 := by
  change
    ‖(realL2ExternalTensor
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta) :
      Lp ℝ 2
        ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))‖ = 1
  rw [realL2ExternalTensor_norm,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2_norm]
  norm_num

/-- Every represented one-particle physical excitation `f ⊗ Ω_top` is exactly
orthogonal to the selected pair vacuum `Ω_top ⊗ Ω_top` in the ambient pair-Haar
Hilbert carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2_inner_oneSidedExcitation_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
          H N hN beta hbeta f) = 0 := by
  have hf := f.property
  change
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      H N) ∈
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta)ᗮ at hf
  rw [Submodule.mem_orthogonal] at hf
  have hphysical :
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
            H N hN beta hbeta)
          (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            H N) = 0 :=
    hf
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
        H N hN beta hbeta)
  have hfirst :
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f) = 0 := by
    simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2] using
      hphysical
  change
    inner ℝ
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
            H N hN beta hbeta))
        (realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            H N hN beta hbeta f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
            H N hN beta hbeta)) = 0
  rw [realL2ExternalTensor_inner, hfirst, zero_mul]

/-- The same orthogonality in the opposite inner-product orientation. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitation_inner_PhysicalOneSlabPairTopModeL2_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          H N hN beta hbeta) = 0 := by
  rw [real_inner_comm]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2_inner_oneSidedExcitation_eq_zero
      H N hN beta hbeta f

/-- Audit-visible finite-volume identification of the selected physical pair
vacuum and the exact one-particle excitation orthogonality inside pair-Haar
`L²`.  This statement does not identify the literal ambient pair transfer with
the normalized physical transfer; that operator intertwining remains a separate
model theorem. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairVacuumSectorPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  vacuumNorm :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
      H N hN beta hbeta‖ = 1
  oneSidedExcitationOrthogonal :
    ∀ f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
            H N hN beta hbeta f) = 0

/-- Construct the selected physical pair-vacuum sector package directly from
the normalized one-slice top mode and the exact external-tensor inner product. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairVacuumSectorPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairVacuumSectorPackage
      H N hN beta hbeta :=
  { vacuumNorm :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2_norm
        H N hN beta hbeta
    oneSidedExcitationOrthogonal :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2_inner_oneSidedExcitation_eq_zero
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
