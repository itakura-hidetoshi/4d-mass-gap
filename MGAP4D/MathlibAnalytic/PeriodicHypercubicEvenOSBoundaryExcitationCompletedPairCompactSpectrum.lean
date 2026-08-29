import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairCompactness
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedTransferPositivity
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module
open scoped InnerProductSpace TensorProduct

noncomputable section

/-- For a compact positive bounded operator on a complete real Hilbert space,
every spectral point is either zero or a strictly positive eigenvalue of finite
multiplicity.  This is the correct compact-operator replacement for trying to
exclude zero from the spectrum on an infinite-dimensional carrier. -/
theorem realHilbertCompactPositive_spectrum_zero_or_positive_finiteDimensional_eigenvalue
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (lambda : ℝ)
    (hlambda : lambda ∈ spectrum ℝ T) :
    lambda = 0 ∨
      (0 < lambda ∧
        HasEigenvalue (T : Module.End ℝ E) lambda ∧
        FiniteDimensional ℝ (eigenspace (T : Module.End ℝ E) lambda)) := by
  by_cases hzero : lambda = 0
  · exact Or.inl hzero
  · right
    have hEigen : HasEigenvalue (T : Module.End ℝ E) lambda :=
      (hCompact.hasEigenvalue_iff_mem_spectrum hzero).2 hlambda
    have hNonneg : 0 ≤ lambda := by
      have hrestrict := hPositive.spectrumRestricts
      rw [SpectrumRestricts.nnreal_iff] at hrestrict
      exact hrestrict lambda hlambda
    have hFinite :
        FiniteDimensional ℝ (eigenspace (T : Module.End ℝ E) lambda) :=
      ContinuousLinearMap.finite_dimensional_eigenspace hCompact lambda hzero
    exact ⟨lt_of_le_of_ne hNonneg hzero.symm, hEigen, hFinite⟩

/-- The spectral theorem for compact positive operators, phrased in the exact
submodule form needed for the later logarithmic generator: the joint
orthogonal complement of all eigenspaces is trivial. -/
theorem realHilbertCompactPositive_orthogonalComplement_iSup_eigenspaces_eq_bot
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    (⨆ lambda : ℝ, eigenspace (T : Module.End ℝ E) lambda)ᗮ = ⊥ := by
  exact
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      hCompact hPositive.isSymmetric

/-- Away from zero, compactness identifies spectrum and point spectrum
exactly.  This small generic receipt is kept explicit because the logarithmic
energy construction will work only on this nonzero sector. -/
theorem realHilbertCompact_nonzero_hasEigenvalue_iff_mem_spectrum
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    HasEigenvalue (T : Module.End ℝ E) lambda ↔ lambda ∈ spectrum ℝ T := by
  exact hCompact.hasEigenvalue_iff_mem_spectrum hlambda

local instance osBoundaryExcitationCompletedPairCompactSpectrumSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedPairCompactSpectrumSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedPairCompactSpectrumSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedPairCompactSpectrumSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedPairCompactSpectrumSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedPairCompactSpectrumSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedPairCompactSpectrumSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedPairCompactSpectrumPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- On the actual completed one-step pair transfer, every nonzero spectral
value is exactly an eigenvalue. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_nonzero_hasEigenvalue_iff_mem_spectrum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    HasEigenvalue
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1 :
          Module.End ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta))
        lambda ↔
      lambda ∈ spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1) := by
  exact
    realHilbertCompact_nonzero_hasEigenvalue_iff_mem_spectrum
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
        H N hN beta hbeta 1 (by norm_num))
      lambda hlambda

/-- Every nonzero eigenspace of the completed one-step pair transfer has finite
multiplicity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_nonzero_eigenspace_finiteDimensional
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    FiniteDimensional ℝ
      (eigenspace
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1 :
          Module.End ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta))
        lambda) := by
  exact
    ContinuousLinearMap.finite_dimensional_eigenspace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
        H N hN beta hbeta 1 (by norm_num))
      lambda hlambda

/-- The concrete compact positive one-step transfer has no nonzero continuous
spectral remainder: every spectral value is zero or a strictly positive,
finite-multiplicity eigenvalue. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_spectrum_zero_or_positive_finiteDimensional_eigenvalue
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : lambda ∈ spectrum ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)) :
    lambda = 0 ∨
      (0 < lambda ∧
        HasEigenvalue
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta 1 :
            Module.End ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                H N hN beta hbeta))
          lambda ∧
        FiniteDimensional ℝ
          (eigenspace
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
              H N hN beta hbeta 1 :
              Module.End ℝ
                (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta))
            lambda)) := by
  exact
    realHilbertCompactPositive_spectrum_zero_or_positive_finiteDimensional_eigenvalue
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
        H N hN beta hbeta 1 (by norm_num))
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
        H N hN beta hbeta 1)
      lambda hlambda

/-- The eigenspaces of the actual completed one-step pair transfer are total:
there is no hidden orthogonal spectral sector left after compactness and
self-adjoint positivity are combined. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_orthogonalComplement_iSup_eigenspaces_eq_bot
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (⨆ lambda : ℝ,
      eigenspace
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1 :
          Module.End ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta))
        lambda)ᗮ = ⊥ := by
  exact
    realHilbertCompactPositive_orthogonalComplement_iSup_eigenspaces_eq_bot
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
        H N hN beta hbeta 1 (by norm_num))
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
        H N hN beta hbeta 1)

/-- Audit-visible receipt for the first compact spectral frontier of the
completed pair transfer.  Zero is retained explicitly as the only possible
non-eigen spectral point, exactly as required before an unbounded `-log T`
construction. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairCompactSpectrumPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  nonzeroSpectrumPointSpectrum :
    ∀ lambda : ℝ, lambda ≠ 0 →
      (HasEigenvalue
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta 1 :
            Module.End ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                H N hN beta hbeta))
          lambda ↔
        lambda ∈ spectrum ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta 1))
  nonzeroEigenspaceFiniteDimensional :
    ∀ lambda : ℝ, lambda ≠ 0 →
      FiniteDimensional ℝ
        (eigenspace
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta 1 :
            Module.End ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                H N hN beta hbeta))
          lambda)
  spectrumDichotomy :
    ∀ lambda : ℝ,
      lambda ∈ spectrum ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta 1) →
        lambda = 0 ∨
          (0 < lambda ∧
            HasEigenvalue
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
                H N hN beta hbeta 1 :
                Module.End ℝ
                  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                    H N hN beta hbeta))
              lambda ∧
            FiniteDimensional ℝ
              (eigenspace
                (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
                  H N hN beta hbeta 1 :
                  Module.End ℝ
                    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                      H N hN beta hbeta))
                lambda))
  eigenspacesTotal :
    (⨆ lambda : ℝ,
      eigenspace
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1 :
          Module.End ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta))
        lambda)ᗮ = ⊥

/-- Construct the completed pair compact-spectrum package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedPairCompactSpectrumPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairCompactSpectrumPackage
      H N hN beta hbeta :=
  { nonzeroSpectrumPointSpectrum :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_nonzero_hasEigenvalue_iff_mem_spectrum
        H N hN beta hbeta
    nonzeroEigenspaceFiniteDimensional :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_nonzero_eigenspace_finiteDimensional
        H N hN beta hbeta
    spectrumDichotomy :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_spectrum_zero_or_positive_finiteDimensional_eigenvalue
        H N hN beta hbeta
    eigenspacesTotal :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_orthogonalComplement_iSup_eigenspaces_eq_bot
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
