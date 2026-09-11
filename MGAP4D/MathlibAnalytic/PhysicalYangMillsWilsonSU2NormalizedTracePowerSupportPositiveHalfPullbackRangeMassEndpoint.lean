import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerSupportPositiveHalfReadoutMassEndpoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem normalizedTracePowerSupportPositiveHalfPullbackRangeMassEndpointTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerSupportPositiveHalfPullbackRangeMassEndpointNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerSupportPositiveHalfPullbackRangeMassEndpointTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerSupportPositiveHalfPullbackRangeMassEndpointCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerSupportPositiveHalfPullbackRangeMassEndpointSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerSupportPositiveHalfPullbackRangeMassEndpointMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerSupportPositiveHalfPullbackRangeMassEndpointBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerSupportPositiveHalfPullbackRangeMassEndpointSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

private abbrev normalizedTracePowerSupportPositiveHalfPullbackRangeMassEndpointPreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerSupportPositiveHalfPullbackRangeMassEndpointTwoRankPositive
        beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2
      normalizedTracePowerSupportPositiveHalfPullbackRangeMassEndpointTwoRankPositive
      beta hbeta Q.toWeakStarBridge hInvariant n

/-- For one normalized-trace polynomial, it is enough that the raw actual-analysis
bounded representative of each nonzero trace-power coefficient lie in the
coherent positive-half pullback range.

This is strictly weaker than supplying pointwise physical cylinder readouts:
there is no reflection/interpolation compatibility premise and no chosen
positive-time observable in the theorem statement.  Mathlib's canonical
bounded-continuous-to-`L²` map transports each supported range witness to the
actual-analysis `L²` range, and finite linearity reconstructs the polynomial. -/
theorem
    normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_support_rawPowerBounded_mem_positiveHalfPullbackRange
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerSupportPositiveHalfPullbackRangeMassEndpointTwoRankPositive
        beta hbeta)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hPowerRange : ∀ j : Fin (k + 1), c j ≠ 0 →
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) (j : ℕ) ∈
        LinearMap.range (Q.positiveHalfPullback n)) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n) := by
  apply
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_support_powerActualAnalysis_mem_range
      n k c
  intro j hcj
  exact
    Q.normalizedTracePowerActualAnalysis_mem_positiveTimeL2Range_of_rawBounded_mem_positiveHalfPullbackRange
      n (j : ℕ) (hPowerRange j hcj)

/-- Terminal reconstructed-Hamiltonian consequence with the model-facing
realization reduced to finitely many exact coherent positive-half pullback range
memberships, one for each nonzero polynomial coefficient.

No whole actual-plaquette-algebra lift, density, global surjectivity,
multiplicativity, pointwise cylinder readout, reflection compatibility, or new
Hamiltonian hypothesis is introduced here. -/
theorem
    normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_support_rawPowerBounded_mem_positiveHalfPullbackRange
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerSupportPositiveHalfPullbackRangeMassEndpointTwoRankPositive
        beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (M : PhysicalYangMillsWilsonSU2NormalizedTracePolynomialMassInput
      halfExtent beta hbeta n k c)
    (hPowerRange : ∀ j : Fin (k + 1), c j ≠ 0 →
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) (j : ℕ) ∈
        LinearMap.range (Q.positiveHalfPullback n))
    (T : (normalizedTracePowerSupportPositiveHalfPullbackRangeMassEndpointPreHilbert
      Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 ≤ T.physicalYangMillsMass := by
  apply
    Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_support_powerActualAnalysis_mem_range
      hInvariant U n k c
      M.halfExtent_gt_one M.beta_pos M.coefficient_ne_zero M.vacuum_orthogonal
      _ T hSelf
  intro j hcj
  exact
    Q.normalizedTracePowerActualAnalysis_mem_positiveTimeL2Range_of_rawBounded_mem_positiveHalfPullbackRange
      n (j : ℕ) (hPowerRange j hcj)

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D