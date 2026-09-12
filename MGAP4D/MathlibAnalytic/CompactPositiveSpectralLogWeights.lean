import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupport
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace TensorProduct lp

noncomputable section

universe u

/-- The logarithmic energy attached to a strictly-positive eigenvalue of the
zero-eigenspace support restriction.  This is the scalar diagonal weight for
the future unbounded generator `-log T`. -/
noncomputable def realHilbertZeroEigenspaceSupportLogEnergy
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T))) : ℝ :=
  -Real.log (mu : ℝ)

/-- Exponentiating the negative logarithmic energy reconstructs the original
strictly-positive transfer eigenvalue exactly. -/
theorem realHilbertZeroEigenspaceSupportLogEnergy_exp_neg_eq
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T))) :
    Real.exp (- realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu) =
      (mu : ℝ) := by
  have hmu :=
    realHilbertZeroEigenspaceSupportRestriction_eigenvalue_pos T hPositive mu
  simpa [realHilbertZeroEigenspaceSupportLogEnergy] using Real.exp_log hmu

/-- The diagonal logarithmic coordinate map on a single support eigenspace. -/
noncomputable def realHilbertZeroEigenspaceSupportLogEnergyCoordinateMap
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T))) :
    eigenspace
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu →ₗ[ℝ]
      realHilbertZeroEigenspaceSupport T :=
  realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
    (eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu).subtype

@[simp] theorem realHilbertZeroEigenspaceSupportLogEnergyCoordinateMap_apply
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)))
    (v : eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) :
    realHilbertZeroEigenspaceSupportLogEnergyCoordinateMap T hPositive mu v =
      realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
        (v : realHilbertZeroEigenspaceSupport T) := by
  rfl

/-- On a support eigenvector the original transfer is exactly the exponential
of the negative logarithmic energy.  This is the one-coordinate identity
`T = exp(-H)` required before assembling the unbounded diagonal operator. -/
theorem realHilbertZeroEigenspaceSupportRestriction_apply_eigenvector_eq_exp_neg_logEnergy_smul
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)))
    (v : eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) :
    realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric
        (v : realHilbertZeroEigenspaceSupport T) =
      Real.exp (- realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu) •
        (v : realHilbertZeroEigenspaceSupport T) := by
  have hv := mem_eigenspace_iff.mp v.property
  rw [realHilbertZeroEigenspaceSupportLogEnergy_exp_neg_eq T hPositive mu]
  exact hv

local instance osBoundaryExcitationSpectralLogWeightsSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationSpectralLogWeightsSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationSpectralLogWeightsSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationSpectralLogWeightsSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationSpectralLogWeightsSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationSpectralLogWeightsSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationSpectralLogWeightsSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationSpectralLogWeightsPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Concrete logarithmic energy for an eigenvalue of the completed one-step
pair transfer restricted to its strictly-positive spectral support. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (mu : Eigenvalues
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta :
        Module.End ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta))) : ℝ :=
  -Real.log (mu : ℝ)

/-- Every concrete logarithmic spectral weight reconstructs its transfer
eigenvalue by `mu = exp (-E(mu))`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy_exp_neg_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (mu : Eigenvalues
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta :
        Module.End ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta))) :
    Real.exp
        (- periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy
          H N hN beta hbeta mu) =
      (mu : ℝ) := by
  have hmu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_eigenvalue_pos
      H N hN beta hbeta mu
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy]
    using Real.exp_log hmu

/-- Concrete one-coordinate `T = exp(-H)` identity on the positive spectral
support of the completed one-step pair transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_apply_eigenvector_eq_exp_neg_logEnergy_smul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (mu : Eigenvalues
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta :
        Module.End ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta)))
    (v : eigenspace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta :
        Module.End ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta)) mu) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta
        (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta) =
      Real.exp
          (- periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy
            H N hN beta hbeta mu) •
        (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta) := by
  have hv := mem_eigenspace_iff.mp v.property
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy_exp_neg_eq
    H N hN beta hbeta mu]
  exact hv

end

end MathlibAnalytic
end MGAP4D