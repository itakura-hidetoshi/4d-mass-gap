import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2TransferFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2PhysicalVacuumSector
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance pairPhysicalIntertwiningTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pairPhysicalIntertwiningCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pairPhysicalIntertwiningSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pairPhysicalIntertwiningMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pairPhysicalIntertwiningBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance pairPhysicalIntertwiningSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance pairPhysicalIntertwiningSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Exact one-sided physical matrix-coefficient intertwining for the literal
raw ordered-pair transfer.

If `T_phys` is the raw Gauss-law one-slab transfer, `lambda = ‖T_phys‖`,
`S = lambda⁻¹ T_phys` its normalized version, and `R` the restriction of `S`
to the orthogonal complement of the full top eigenspace, then the literal pair
transfer on `f ⊠ Ω_top` carries the exact raw normalization `lambda²`:

`⟪T_pair J f, J u⟫ = lambda² * ⟪R f, u⟫`.

The square is essential: the literal raw pair operator acts on both endpoints,
while the physical one-sided transfer used downstream is normalized so that the
companion top mode is fixed. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_oneSidedExcitation_matrixCoefficient_eq_sq_physicalNorm_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
            H N hN beta hbeta f))
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
          H N hN beta hbeta u) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2 *
        inner ℝ
          (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta f :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
              H N hN beta hbeta) :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
          (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) := by
  let Tphys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta
  let lambda : ℝ := ‖Tphys‖
  let F :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta f
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta u
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
      H N hN beta hbeta
  have hlambdaPos : 0 < lambda := by
    simpa [lambda, Tphys] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta
  have hlambdaNe : lambda ≠ 0 := hlambdaPos.ne'
  have hfirstPhysical :
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta F) U =
        inner ℝ
          (Tphys (f :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
          (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) := by
    rfl
  have htopPhysical :
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta Omega) Omega = lambda := by
    change
      inner ℝ
          (Tphys
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
              H N hN beta hbeta))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
            H N hN beta hbeta) = lambda
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_eigen]
    rw [real_inner_smul_left]
    rw [real_inner_self_eq_norm_sq]
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm]
    simp [lambda, Tphys]
  have hTphysEq :
      Tphys (f :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
        lambda •
          S (f :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) := by
    change
      Tphys (f :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
        lambda •
          (lambda⁻¹ •
            Tphys (f :
              periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
    rw [smul_smul, mul_inv_cancel₀ hlambdaNe, one_smul]
  have hRcoe :
      ((R f :
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H N hN beta hbeta) :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
      S (f :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) := by
    rfl
  have hfirstNormalized :
      inner ℝ
          (Tphys (f :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
          (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
        lambda *
          inner ℝ
            (((R f :
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
                  H N hN beta hbeta) :
              periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
            (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) := by
    rw [hTphysEq, real_inner_smul_left, hRcoe]
  change
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta (realL2ExternalTensor F Omega))
        (realL2ExternalTensor U Omega) = _
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_inner_externalTensor_factorization]
  rw [hfirstPhysical, htopPhysical, hfirstNormalized]
  simp [lambda, Tphys]
  ring

/-- Audit-visible receipt for the exact raw-to-normalized one-sided physical
intertwining seam.  It records both the exact `lambda²` coefficient and the
already-proved strict contraction of the normalized excitation operator. -/
structure PeriodicHypercubicEvenSpecialUnitaryPairTransferOneSidedPhysicalIntertwiningPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  exactMatrixCoefficient :
    ∀ f u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
              H N hN beta hbeta f))
          (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
            H N hN beta hbeta u) =
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖ ^ 2 *
          inner ℝ
            (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
                H N hN beta hbeta f :
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
                H N hN beta hbeta) :
              periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
            (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
  normalizedExcitationStrict :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖ < 1

/-- Construct the exact one-sided physical intertwining receipt directly from
the literal pair factorization, physical top-eigenvector equation, and the
normalized excitation restriction. -/
theorem periodicHypercubicEvenSpecialUnitaryPairTransferOneSidedPhysicalIntertwiningPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPairTransferOneSidedPhysicalIntertwiningPackage
      H N hN beta hbeta :=
  { exactMatrixCoefficient :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_oneSidedExcitation_matrixCoefficient_eq_sq_physicalNorm_mul
        H N hN beta hbeta
    normalizedExcitationStrict :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
