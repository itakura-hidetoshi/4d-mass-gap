import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportDerivativeRatioSharpGapCapConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

/-- The saturation-free sharp derivative-ratio cap already forces every
factorial-normalized resolvent ratio to reconstruct an effective logarithmic
energy above the finite-volume coercive gap.

Writing

`R_n(lambda) = q^(n+1)(lambda) / ((n+1) q^n(lambda))`

and `c = 2 * finiteVolumeDecayRate`, every nonzero physical support state and
every admissible `(n, lambda)` satisfy

`0 < R_n(lambda) <= (c - lambda)^(-1)`,
`c <= lambda + R_n(lambda)^(-1)`.

Consequently the associated effective one-step transfer value
`exp (-(lambda + R_n(lambda)^(-1)))` is positive, bounded by `exp (-c)`, and
strictly below one.  No Turán saturation or single-mode hypothesis is used. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_quantitativeEffectiveEnergyGap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (n : ℕ) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    let R := iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda)
    let c :=
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta
    0 < R ∧
      R ≤ (c - lambda)⁻¹ ∧
      c ≤ lambda + R⁻¹ ∧
      0 < Real.exp (-(lambda + R⁻¹)) ∧
      Real.exp (-(lambda + R⁻¹)) ≤ Real.exp (-c) ∧
      Real.exp (-(lambda + R⁻¹)) < 1 := by
  dsimp only
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  let R := iteratedDeriv (n + 1) q lambda /
    ((n + 1 : ℝ) * iteratedDeriv n q lambda)
  let c :=
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  have hcap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_le_gapResolventDistance
      H N hN beta hbeta v hv n lambda hlambda
  dsimp only at hcap
  have hRPos : 0 < R := by
    simpa [R, q] using hcap.1
  have hRUpper : R ≤ (c - lambda)⁻¹ := by
    simpa [R, q, c] using hcap.2
  have hc : 0 < c := by
    exact mul_pos (by norm_num)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
        H N hN beta hbeta)
  have hlambdaC : |lambda| < c := by
    simpa [c] using hlambda
  have hgapDistancePos : 0 < c - lambda := by
    have hlambdaLtC : lambda < c :=
      lt_of_le_of_lt (le_abs_self lambda) hlambdaC
    linarith
  have hRUpperDiv : R ≤ 1 / (c - lambda) := by
    simpa [one_div] using hRUpper
  have hmul : R * (c - lambda) ≤ 1 :=
    (le_div_iff₀ hgapDistancePos).mp hRUpperDiv
  have hgapDistanceLeInv : c - lambda ≤ R⁻¹ := by
    have h : c - lambda ≤ 1 / R := by
      apply (le_div_iff₀ hRPos).2
      simpa [mul_comm] using hmul
    simpa [one_div] using h
  have hcEnergy : c ≤ lambda + R⁻¹ := by
    linarith
  have hExpPos : 0 < Real.exp (-(lambda + R⁻¹)) := Real.exp_pos _
  have hExpUpper :
      Real.exp (-(lambda + R⁻¹)) ≤ Real.exp (-c) := by
    apply (Real.exp_le_exp).2
    linarith
  have hGapExpLtOne : Real.exp (-c) < 1 := by
    have hneg : -c < 0 := by
      linarith
    simpa using (Real.exp_lt_exp.mpr hneg)
  have hExpLtOne : Real.exp (-(lambda + R⁻¹)) < 1 :=
    lt_of_le_of_lt hExpUpper hGapExpLtOne
  exact ⟨hRPos, hRUpper, hcEnergy, hExpPos, hExpUpper, hExpLtOne⟩

end

end MathlibAnalytic
end MGAP4D
