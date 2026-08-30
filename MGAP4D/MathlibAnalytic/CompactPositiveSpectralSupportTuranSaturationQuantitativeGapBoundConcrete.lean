import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportTuranSaturationGlobalSpectralInvariantConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

local instance turanGapBoundConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance turanGapBoundConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance turanGapBoundConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance turanGapBoundConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance turanGapBoundConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance turanGapBoundConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance turanGapBoundConcreteSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance turanGapBoundConcretePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- A scalar Turán saturation not only reconstructs the exact physical spectral
mode; the reconstructed logarithmic energy automatically lies above the
finite-volume coercive gap.  Consequently the reconstructed one-step transfer
spectral value is positive, bounded by the corresponding exponential gap
factor, and strictly below one.

Writing `R = R_n(lambda)` and
`c = 2 * finiteVolumeDecayRate`, saturation gives the directly observable
bounds
`c ≤ lambda + R⁻¹` and
`0 < exp (-(lambda + R⁻¹)) ≤ exp (-c) < 1`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_turanSaturation_quantitativeSpectralGap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0)
    (n : ℕ) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)
    (hsaturation :
      let q :=
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
          H N hN beta hbeta v
      iteratedDeriv (n + 1) q lambda /
          ((n + 1 : ℝ) * iteratedDeriv n q lambda) =
        iteratedDeriv (n + 2) q lambda /
          ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda)) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    let R := iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda)
    let c :=
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta
    R ≠ 0 ∧
      c ≤ lambda + R⁻¹ ∧
      0 < Real.exp (-(lambda + R⁻¹)) ∧
      Real.exp (-(lambda + R⁻¹)) ≤ Real.exp (-c) ∧
      Real.exp (-(lambda + R⁻¹)) < 1 := by
  dsimp only at hsaturation ⊢
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta
  let T : E →L[ℝ] E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  letI : CompleteSpace (realHilbertZeroEigenspaceSupport T) := by
    exact (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe
  let A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  let R := iteratedDeriv (n + 1) q lambda /
    ((n + 1 : ℝ) * iteratedDeriv n q lambda)
  let c :=
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  have hc : 0 < c := by
    exact mul_pos (by norm_num)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
        H N hN beta hbeta)
  have hpair :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniqueTransferGeneratorSpectralPair
        H N hN beta hbeta v :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_uniqueTransferGeneratorSpectralPair
      H N hN beta hbeta v hv n lambda hlambda).mp hsaturation
  change
    (∃! tau : ℝ,
      ∃! rho : ℝ,
        0 < tau ∧
        tau = Real.exp (-rho) ∧
        rho = -Real.log tau ∧
        T (v : E) = tau • (v : E) ∧
        ∃ x : A.domain,
          (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta) = v ∧
          A x = rho • v) at hpair
  rcases hpair with ⟨tau, htauPair, _⟩
  rcases htauPair with ⟨rho, hrho, _⟩
  rcases hrho with ⟨_, _, _, _, x, hxv, hAx⟩
  have hR : R = (rho - lambda)⁻¹ := by
    simpa [R, q, A] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_of_logGeneratorEigenmode
        H N hN beta hbeta v hv rho x hxv hAx n lambda hlambda)
  have hRPos : 0 < R := by
    have hn :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
        H N hN beta hbeta v hv n lambda hlambda
    have hn1 :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
        H N hN beta hbeta v hv (n + 1) lambda hlambda
    dsimp [R, q]
    positivity
  have hR0 : R ≠ 0 := ne_of_gt hRPos
  have hreconstruct : rho = lambda + R⁻¹ := by
    rw [hR]
    simp
  have hquad :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_quadratic_lower_bound
      H N hN beta hbeta x
  have hquad' : c * ‖v‖ ^ 2 ≤ rho * ‖v‖ ^ 2 := by
    simpa [A, c, hAx, hxv, real_inner_smul_left, real_inner_self_eq_norm_sq] using hquad
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hvnormsq : 0 < ‖v‖ ^ 2 := by positivity
  have hcrho : c ≤ rho := by
    nlinarith
  have hcR : c ≤ lambda + R⁻¹ := by
    rw [← hreconstruct]
    exact hcrho
  have hExpPos : 0 < Real.exp (-(lambda + R⁻¹)) := Real.exp_pos _
  have hExpUpper :
      Real.exp (-(lambda + R⁻¹)) ≤ Real.exp (-c) := by
    apply Real.exp_le_exp.mpr
    rw [← hreconstruct]
    linarith
  have hGapExpLtOne : Real.exp (-c) < 1 := by
    have h := Real.exp_lt_exp.mpr (neg_lt_zero.mpr hc)
    simpa using h
  exact ⟨hR0, hcR, hExpPos, hExpUpper, lt_of_le_of_lt hExpUpper hGapExpLtOne⟩

end

end MathlibAnalytic
end MGAP4D
