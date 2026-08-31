import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorPointSpectrumConcrete
import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianPointSpectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace lp LinearPMap Topology BigOperators

noncomputable section

/-- Operator-level unitary intertwining data for partially-defined real-linear
operators.  The bridge records the Hilbert-space equivalence, exact domain
transport in both directions, and operator intertwining on the source domain.
Point-spectrum identification is derived from these data rather than assumed. -/
structure RealLinearPMapUnitaryIntertwining
    {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E →ₗ.[ℝ] E) (B : F →ₗ.[ℝ] F) where
  equiv : E ≃ₗᵢ[ℝ] F
  domain_iff : ∀ x : E, x ∈ A.domain ↔ equiv x ∈ B.domain
  intertwines : ∀ x : A.domain,
    B ⟨equiv (x : E), (domain_iff (x : E)).1 x.property⟩ =
      equiv (A x)

/-- Unitary intertwining with exact domain transport preserves the real point
spectrum of a partially-defined operator. -/
theorem realLinearPMapPointSpectrum_eq_of_unitaryIntertwining
    {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E →ₗ.[ℝ] E) (B : F →ₗ.[ℝ] F)
    (I : RealLinearPMapUnitaryIntertwining A B) :
    realLinearPMapPointSpectrum A = realLinearPMapPointSpectrum B := by
  ext a
  constructor
  · rintro ⟨x, hx, hAx⟩
    let y : B.domain :=
      ⟨I.equiv (x : E), (I.domain_iff (x : E)).1 x.property⟩
    refine ⟨y, ?_, ?_⟩
    · intro hy0
      apply hx
      apply I.equiv.injective
      simpa [y] using hy0
    · change B y = a • (y : F)
      calc
        B y = I.equiv (A x) := I.intertwines x
        _ = I.equiv (a • (x : E)) := by rw [hAx]
        _ = a • I.equiv (x : E) := by rw [I.equiv.map_smul]
        _ = a • (y : F) := by rfl
  · rintro ⟨y, hy, hBy⟩
    let x0 : E := I.equiv.symm (y : F)
    have hxmem : x0 ∈ A.domain := by
      apply (I.domain_iff x0).2
      simpa [x0] using y.property
    let x : A.domain := ⟨x0, hxmem⟩
    have hxy : I.equiv (x : E) = (y : F) := by
      simp [x, x0]
    have hdomainPoint :
        (⟨I.equiv (x : E), (I.domain_iff (x : E)).1 x.property⟩ : B.domain) = y := by
      apply Subtype.ext
      exact hxy
    refine ⟨x, ?_, ?_⟩
    · intro hx0
      apply hy
      change (y : F) = 0
      rw [← hxy, hx0]
      simp
    · apply I.equiv.injective
      calc
        I.equiv (A x) =
            B ⟨I.equiv (x : E), (I.domain_iff (x : E)).1 x.property⟩ :=
          (I.intertwines x).symm
        _ = B y := by rw [hdomainPoint]
        _ = a • (y : F) := hBy
        _ = a • I.equiv (x : E) := by rw [hxy]
        _ = I.equiv (a • (x : E)) := by rw [I.equiv.map_smul]

local instance logGeneratorWightmanSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance logGeneratorWightmanSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance logGeneratorWightmanSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance logGeneratorWightmanSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance logGeneratorWightmanSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance logGeneratorWightmanSpatialSliceHaarSFinite
    (H N : ℕ) : SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance logGeneratorWightmanPairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete H N hN beta hbeta
local instance logGeneratorWightmanSpectralSupportNormedSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  infer_instance
local instance logGeneratorWightmanSpectralSupportComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  exact (realHilbertZeroEigenspaceSupport_isClosed
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1)).completeSpace_coe

/-- The operator-level OS/Wightman bridge required at the present frontier.
It does not assume equality of spectra: it identifies the physical transfer
support Hilbert space with `Ω⊥`, transports the generator domain exactly, and
intertwines the two actual partially-defined operators. -/
structure PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanIntertwining
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) where
  unitaryIntertwining :
    RealLinearPMapUnitaryIntertwining
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta)
      M.canonicalVacuumOrthogonalHamiltonian

/-- Operator-level intertwining identifies the physical transfer log-generator
point energies with the point spectrum of the reconstructed Hamiltonian on
`Ω⊥`. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_pointSpectrum_eq_wightman
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel)
    (I : PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanIntertwining
      H N hN beta hbeta M) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet
        H N hN beta hbeta =
      M.canonicalVacuumOrthogonalPointSpectrum := by
  change
    realLinearPMapPointSpectrum
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
          H N hN beta hbeta) =
      realLinearPMapPointSpectrum M.canonicalVacuumOrthogonalHamiltonian
  exact realLinearPMapPointSpectrum_eq_of_unitaryIntertwining
    _ _ I.unitaryIntertwining

/-- Hence the intrinsic physical spectral floor is the infimum of the actual
Wightman `Ω⊥` Hamiltonian point spectrum. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_logEnergyInf_eq_wightmanPointSpectrum_inf
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel)
    (I : PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanIntertwining
      H N hN beta hbeta M) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf
        H N hN beta hbeta =
      sInf M.canonicalVacuumOrthogonalPointSpectrum := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf_eq_logGeneratorPointEnergySet_inf,
    periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_pointSpectrum_eq_wightman
      H N hN beta hbeta M I]

/-- For every admissible resolvent parameter, the asymptotic effective-energy
variational infimum is exactly the Wightman `Ω⊥` point-spectrum infimum. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_effectiveEnergyLimitSet_inf_eq_wightmanPointSpectrum_inf
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel)
    (I : PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanIntertwining
      H N hN beta hbeta M)
    (hSupport : ∃ v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta, v ≠ 0)
    (lambda : ℝ)
    (hlambda : |lambda| < 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta) :
    sInf (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportEffectiveEnergyLimitSet
        H N hN beta hbeta lambda) =
      sInf M.canonicalVacuumOrthogonalPointSpectrum := by
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet_inf_eq_effectiveEnergyLimitSet_inf
    H N hN beta hbeta hSupport lambda hlambda]
  rw [periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_pointSpectrum_eq_wightman
    H N hN beta hbeta M I]

/-- The finite-volume coercive decay scale therefore remains a rigorous lower
bound for the reconstructed Wightman `Ω⊥` Hamiltonian point-spectrum floor. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_wightmanPointSpectrum_inf_ge_two_mul_finiteVolumeDecayRate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel)
    (I : PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanIntertwining
      H N hN beta hbeta M)
    (hSupport : ∃ v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta, v ≠ 0) :
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta ≤
      sInf M.canonicalVacuumOrthogonalPointSpectrum := by
  rw [← periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_pointSpectrum_eq_wightman
    H N hN beta hbeta M I]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet_inf_ge_two_mul_finiteVolumeDecayRate
    H N hN beta hbeta hSupport

end

end MathlibAnalytic
end MGAP4D
