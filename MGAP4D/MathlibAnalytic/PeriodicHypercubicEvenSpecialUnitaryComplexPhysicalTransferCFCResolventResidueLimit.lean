import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCResolventLaurentSplitting
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set Filter Topology
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance periodicHypercubicEvenSpecialUnitaryComplexResidueRealCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance periodicHypercubicEvenSpecialUnitaryComplexResidueComplexCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- The centered complex Wilson resolvent is continuous at the isolated top
spectral point.  This is the regular block in the Laurent decomposition. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_resolvent_continuousAt_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ContinuousAt
      (fun z : ℂ =>
        resolvent
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
            H N hN beta hbeta) z)
      (1 : ℂ) := by
  let R := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
    H N hN beta hbeta
  have hmem :
      (1 : ℂ) ∈ resolventSet ℂ R := by
    simpa [R] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_one_mem_resolventSet
        H N hN beta hbeta
  have hunit : IsUnit
      (algebraMap ℂ
          (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
            PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) (1 : ℂ) - R) :=
    hmem
  rcases hunit with ⟨u, hu⟩
  have hshift :
      Tendsto
        (fun z : ℂ =>
          algebraMap ℂ
              (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
                PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) z - R)
        (𝓝 (1 : ℂ))
        (𝓝
          (algebraMap ℂ
              (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
                PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) (1 : ℂ) - R)) := by
    fun_prop
  have hshiftUnit :
      Tendsto
        (fun z : ℂ =>
          algebraMap ℂ
              (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
                PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) z - R)
        (𝓝 (1 : ℂ))
        (𝓝
          (u : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
            PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)) := by
    simpa [hu] using hshift
  have hinv :=
    (NormedRing.inverse_continuousAt u).comp (1 : ℂ) hshiftUnit
  simpa [resolvent, R, hu] using hinv

/-- The CFC top projection is the actual operator-norm residue of the genuine
complex normalized Wilson transfer resolvent at the isolated spectral point
`1`, approached inside the punctured right-half-plane resolvent region. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_scaled_resolvent_tendsto_cfcTopProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Tendsto
      (fun z : ℂ =>
        (z - 1) •
          resolvent
            (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) z)
      (𝓝[
        {z : ℂ |
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta‖ < z.re ∧ z ≠ 1}]
        (1 : ℂ))
      (𝓝
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta)) := by
  let S := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
    H N hN beta hbeta
  let R := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
    H N hN beta hbeta
  let Q := (1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) - P
  let U : Set ℂ :=
    {z : ℂ |
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ < z.re ∧ z ≠ 1}
  change Tendsto
    (fun z : ℂ => (z - 1) • resolvent S z)
    (𝓝[U] (1 : ℂ)) (𝓝 P)
  have hreg :
      Tendsto (fun z : ℂ => resolvent R z)
        (𝓝 (1 : ℂ)) (𝓝 (resolvent R (1 : ℂ))) := by
    simpa [R] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_resolvent_continuousAt_one
        H N hN beta hbeta
  have hregQ :
      Tendsto (fun z : ℂ => resolvent R z * Q)
        (𝓝 (1 : ℂ)) (𝓝 (resolvent R (1 : ℂ) * Q)) :=
    hreg.mul tendsto_const_nhds
  have hz0 :
      Tendsto (fun z : ℂ => z - 1)
        (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
    fun_prop
  have hrem :
      Tendsto
        (fun z : ℂ => (z - 1) • (resolvent R z * Q))
        (𝓝 (1 : ℂ))
        (𝓝 (0 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
          PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)) := by
    simpa using hz0.smul hregQ
  have hremWithin :
      Tendsto
        (fun z : ℂ => (z - 1) • (resolvent R z * Q))
        (𝓝[U] (1 : ℂ))
        (𝓝 (0 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
          PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)) :=
    hrem.mono_left inf_le_left
  have heq :
      (fun z : ℂ => (z - 1) • resolvent S z) =ᶠ[𝓝[U] (1 : ℂ)]
        (fun z : ℂ => P + (z - 1) • (resolvent R z * Q)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rcases hz with ⟨hzq, hz1⟩
    have hLaurent :
        resolvent S z =
          (z - 1)⁻¹ • P + resolvent R z * Q := by
      simpa [S, P, R, Q] using
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolvent_eq_topPole_add_centered
          H N hN beta hbeta z hzq hz1
    rw [hLaurent, smul_add, smul_smul]
    rw [mul_inv_cancel₀ (sub_ne_zero.mpr hz1), one_smul]
  have htarget :
      Tendsto
        (fun z : ℂ => P + (z - 1) • (resolvent R z * Q))
        (𝓝[U] (1 : ℂ)) (𝓝 P) := by
    simpa using tendsto_const_nhds.add hremWithin
  exact htarget.congr' heq.symm

/-- Audit-visible package for the isolated CFC pole: the centered block is
regular at `1`, and the scaled full resolvent converges in operator norm to the
full CFC top projection. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCResolventResiduePackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  centeredResolventContinuousAtOne :
    ContinuousAt
      (fun z : ℂ =>
        resolvent
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
            H N hN beta hbeta) z)
      (1 : ℂ)
  scaledResolventResidue :
    Tendsto
      (fun z : ℂ =>
        (z - 1) •
          resolvent
            (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) z)
      (𝓝[
        {z : ℂ |
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta‖ < z.re ∧ z ≠ 1}]
        (1 : ℂ))
      (𝓝
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta))

/-- Construct the rank-free CFC resolvent residue package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCResolventResiduePackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCResolventResiduePackage
      H N hN beta hbeta :=
  { centeredResolventContinuousAtOne :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_resolvent_continuousAt_one
        H N hN beta hbeta
    scaledResolventResidue :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_scaled_resolvent_tendsto_cfcTopProjection
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D
