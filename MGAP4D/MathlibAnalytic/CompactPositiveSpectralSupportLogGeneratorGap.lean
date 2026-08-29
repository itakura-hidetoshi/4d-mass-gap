import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorSelfAdjoint
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairCompactSpectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace lp LinearPMap

noncomputable section

universe u

/-- An eigenvalue of the restriction of a symmetric operator to the orthogonal
complement of its zero eigenspace is also an eigenvalue of the ambient
operator.  This bridge lets ambient spectral bounds control the intrinsic
positive-support coordinates used by the logarithmic Hamiltonian. -/
theorem realHilbertZeroEigenspaceSupportRestriction_hasEigenvalue_ambient
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hSymm : T.IsSymmetric)
    (lambda : ℝ)
    (hEigen : HasEigenvalue
      (realHilbertZeroEigenspaceSupportRestriction T hSymm :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) lambda) :
    HasEigenvalue (T : Module.End ℝ E) lambda := by
  rw [Module.End.hasEigenvalue_iff] at hEigen ⊢
  intro hAmbientBot
  apply hEigen
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hxRestriction := mem_eigenspace_iff.mp hx
  have hxCoe := congrArg
    (fun z : realHilbertZeroEigenspaceSupport T => (z : E)) hxRestriction
  have hxAmbient :
      T (x : E) = lambda • (x : E) := by
    simpa using hxCoe
  have hxAmbientMem :
      (x : E) ∈ eigenspace (T : Module.End ℝ E) lambda :=
    mem_eigenspace_iff.mpr hxAmbient
  rw [hAmbientBot] at hxAmbientMem
  have hxZero : (x : E) = 0 := by
    simpa using hxAmbientMem
  exact Subtype.ext hxZero

local instance osBoundaryExcitationSpectralSupportLogGeneratorGapSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationSpectralSupportLogGeneratorGapSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationSpectralSupportLogGeneratorGapSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationSpectralSupportLogGeneratorGapSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationSpectralSupportLogGeneratorGapSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationSpectralSupportLogGeneratorGapSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationSpectralSupportLogGeneratorGapSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationSpectralSupportLogGeneratorGapPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Every eigenvalue of the intrinsic positive spectral-support restriction is
an ambient spectral value of the completed one-step pair transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_eigenvalue_mem_ambient_spectrum
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
    (mu : ℝ) ∈ spectrum ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1) := by
  have hmuPos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_eigenvalue_pos
      H N hN beta hbeta mu
  have hAmbientEigen :
      HasEigenvalue
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1 :
          Module.End ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta))
        (mu : ℝ) := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport]
      using
        (realHilbertZeroEigenspaceSupportRestriction_hasEigenvalue_ambient
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta 1)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
            H N hN beta hbeta 1).isSymmetric
          (mu : ℝ)
          mu.property)
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_nonzero_hasEigenvalue_iff_mem_spectrum
      H N hN beta hbeta (mu : ℝ) hmuPos.ne').1 hAmbientEigen

/-- Hence every positive-support eigenvalue is bounded above by the explicit
one-step finite-volume decay radius. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_eigenvalue_le_decayRadius
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
    (mu : ℝ) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
        H N hN beta hbeta 1 := by
  have hspec :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_eigenvalue_mem_ambient_spectrum
      H N hN beta hbeta mu
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_spectrum_subset_nonneg_decayInterval
      H N hN beta hbeta hspec).2

/-- The logarithmic energy of every actual positive-support eigenmode is at
least twice the already-constructed finite-volume one-slab decay rate.  This
is the exact spectral conversion `mu ≤ exp(-2 r) => -log mu ≥ 2 r`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy_ge_two_mul_finiteVolumeDecayRate
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
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy
        H N hN beta hbeta mu := by
  have hmuPos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_eigenvalue_pos
      H N hN beta hbeta mu
  have hrhoPos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius_pos
      H N hN beta hbeta 1
  have hmuLe :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_eigenvalue_le_decayRadius
      H N hN beta hbeta mu
  have hlog := Real.strictMonoOn_log.monotoneOn hmuPos hrhoPos hmuLe
  have hlogRho :
      Real.log
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
            H N hN beta hbeta 1) =
        -2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta := by
    simp [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius]
  rw [hlogRho] at hlog
  change
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta ≤ -Real.log (mu : ℝ)
  linarith

/-- In particular every logarithmic support energy is strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy_pos
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
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy
        H N hN beta hbeta mu := by
  have hr :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
      H N hN beta hbeta
  have hgap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy_ge_two_mul_finiteVolumeDecayRate
      H N hN beta hbeta mu
  nlinarith

/-- The actual self-adjoint logarithmic Hamiltonian on the completed one-step
pair-transfer support. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta →ₗ.[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  exact
    realHilbertCompactPositiveZeroSupportLogGenerator
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
        H N hN beta hbeta 1 (by norm_num))
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
        H N hN beta hbeta 1)

/-- The concrete completed-support logarithmic Hamiltonian is self-adjoint. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_isSelfAdjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
  exact
    realHilbertCompactPositiveZeroSupportLogGenerator_isSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
        H N hN beta hbeta 1 (by norm_num))
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
        H N hN beta hbeta 1)

/-- Every support eigenvector belongs to the domain of the concrete
logarithmic Hamiltonian. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_eigenvector_mem_domain
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
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) ∈
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta).domain := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport]
    using
      (realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_mem_domain
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
          H N hN beta hbeta 1 (by norm_num))
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
          H N hN beta hbeta 1)
        mu v)

/-- On every support eigenspace the concrete self-adjoint Hamiltonian acts by
the logarithmic energy, whose value is bounded below by `2 r`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_apply_eigenvector
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
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta
        ⟨(v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta),
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_eigenvector_mem_domain
            H N hN beta hbeta mu v⟩ =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy
          H N hN beta hbeta mu •
        (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta) := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport]
    using
      (realHilbertCompactPositiveZeroSupportLogGenerator_apply_eigenvector
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
          H N hN beta hbeta 1 (by norm_num))
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
          H N hN beta hbeta 1)
        mu v)

/-- Audit package for the finite-volume logarithmic-Hamiltonian gap stage. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedLogGeneratorGapPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  selfAdjoint :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta)
  eigenEnergyLowerBound :
    ∀ mu : Eigenvalues
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta :
        Module.End ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta)),
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy
          H N hN beta hbeta mu
  eigenEnergyPositive :
    ∀ mu : Eigenvalues
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta :
        Module.End ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta)),
      0 <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy
          H N hN beta hbeta mu

/-- Construct the finite-volume logarithmic-Hamiltonian gap package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedLogGeneratorGapPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedLogGeneratorGapPackage
      H N hN beta hbeta :=
  { selfAdjoint :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_isSelfAdjoint
        H N hN beta hbeta
    eigenEnergyLowerBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy_ge_two_mul_finiteVolumeDecayRate
        H N hN beta hbeta
    eigenEnergyPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy_pos
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D