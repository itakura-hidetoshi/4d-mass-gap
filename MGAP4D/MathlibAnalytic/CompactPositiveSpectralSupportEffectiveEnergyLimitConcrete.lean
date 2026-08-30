import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportEffectiveEnergyOrderRigidityConcrete
import Mathlib.Topology.Order.MonotoneConvergence

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

/-- The asymptotic effective logarithmic energy reconstructed from the full
factorial-normalized resolvent derivative-ratio hierarchy.

It is defined intrinsically as the infimum of the finite-order effective
energies. The admissible-gap hypotheses enter only when proving that this
infimum is finite, bounded below by the physical coercive gap, and is the
actual `atTop` limit. -/
def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (lambda : ℝ) : ℝ :=
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  sInf (Set.range fun n : ℕ =>
    lambda +
      (iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹)

/-- The physical effective-energy hierarchy converges to its infimum as the
derivative order tends to infinity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_tendsto_effectiveEnergyLimit
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    Tendsto
      (fun n : ℕ =>
        lambda +
          (iteratedDeriv (n + 1) q lambda /
            ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹)
      atTop
      (𝓝 (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
        H N hN beta hbeta v lambda)) := by
  dsimp only
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  let rho := fun n : ℕ =>
    lambda +
      (iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹
  let c :=
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  have hanti :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergy_antitone
      H N hN beta hbeta v hv lambda hlambda
  dsimp only at hanti
  have hanti' : Antitone rho := by
    simpa [rho, q] using hanti
  have hgap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergy_gapLowerBound
      H N hN beta hbeta v hv lambda hlambda
  dsimp only at hgap
  have hbdd : BddBelow (Set.range rho) := by
    refine ⟨c, ?_⟩
    rintro _ ⟨n, rfl⟩
    simpa [rho, q, c] using hgap n
  change Tendsto rho atTop
    (𝓝 (sInf (Set.range rho)))
  exact tendsto_atTop_isGLB hanti' (isGLB_csInf (Set.range_nonempty rho) hbdd)

/-- The asymptotic effective energy remains above the finite-volume coercive
gap and lies below every finite-order reconstructed effective energy. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit_bounds
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    let c :=
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta
    c ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
          H N hN beta hbeta v lambda ∧
      ∀ n : ℕ,
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
            H N hN beta hbeta v lambda ≤
          lambda +
            (iteratedDeriv (n + 1) q lambda /
              ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹ := by
  dsimp only
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  let rho := fun n : ℕ =>
    lambda +
      (iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹
  let c :=
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  have hgap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergy_gapLowerBound
      H N hN beta hbeta v hv lambda hlambda
  dsimp only at hgap
  have hbdd : BddBelow (Set.range rho) := by
    refine ⟨c, ?_⟩
    rintro _ ⟨n, rfl⟩
    simpa [rho, q, c] using hgap n
  change c ≤ sInf (Set.range rho) ∧ ∀ n : ℕ, sInf (Set.range rho) ≤ rho n
  constructor
  · exact le_csInf (Set.range_nonempty rho) (by
      rintro _ ⟨n, rfl⟩
      simpa [rho, q, c] using hgap n)
  · intro n
    exact csInf_le hbdd ⟨n, rfl⟩

/-- Off the single logarithmic-generator-mode locus, every finite-order
effective energy lies strictly above the asymptotic effective-energy limit.
Thus the strictly decreasing hierarchy approaches the limit without attaining
it at any finite derivative order. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit_lt_of_not_logGeneratorMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)
    (hnot :
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    ∀ n : ℕ,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
          H N hN beta hbeta v lambda <
        lambda +
          (iteratedDeriv (n + 1) q lambda /
            ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹ := by
  dsimp only
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  let rho := fun n : ℕ =>
    lambda +
      (iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹
  have hbounds :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit_bounds
      H N hN beta hbeta v hv lambda hlambda
  dsimp only at hbounds
  have hstrict :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergy_strictAnti_iff_not_logGeneratorMode
      H N hN beta hbeta v hv lambda hlambda).2 hnot
  dsimp only at hstrict
  intro n
  have hnext :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
          H N hN beta hbeta v lambda ≤ rho (n + 1) := by
    simpa [rho, q] using hbounds.2 (n + 1)
  have hdrop : rho (n + 1) < rho n := by
    have := hstrict (Nat.lt_succ_self n)
    simpa [rho, q] using this
  exact hnext.trans_lt hdrop

end

end MathlibAnalytic
end MGAP4D
