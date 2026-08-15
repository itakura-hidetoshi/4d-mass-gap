import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerSupportPositiveHalfPullbackRangeMassEndpoint
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2RawActualAnalysisContinuousPullbackClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointOpenHalfHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

local instance normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointSU2Nontrivial :
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

private abbrev normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointPreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointTwoRankPositive
        beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2
      normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointTwoRankPositive
      beta hbeta Q.toWeakStarBridge hInvariant n

/-- Sup-norm closure realizability of one raw normalized-trace power transports
canonically to closure of the corresponding physical positive-time `L²` range.

This is the one-hot specialization of the already-proved continuous-to-`L²`
closure theorem.  No exact preimage is chosen. -/
theorem
    normalizedTracePowerActualAnalysis_mem_positiveTimeL2RangeClosure_of_rawBounded_mem_positiveHalfPullbackRangeClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointTwoRankPositive
        beta hbeta)
    (n j : ℕ)
    (hClosure :
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) j ∈
        closure (LinearMap.range (Q.positiveHalfPullback n))) :
    periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) j ∈
      closure (LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)) := by
  have h :=
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_mem_positiveHalfPullbackRangeClosure
      n j (normalizedTracePowerLastCoefficient j) (by
        simpa [periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction]
          using hClosure)
  simpa using
    (show
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
          (halfExtent n) (beta n) (hbeta n) j
            (normalizedTracePowerLastCoefficient j) =
        periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
          (halfExtent n) (beta n) (hbeta n) j from
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2_lastCoefficient_eq_powerActualAnalysis
        (halfExtent n) (beta n) (hbeta n) j) ▸ h

/-- For a fixed normalized-trace polynomial, only the nonzero coefficient
support must be approximable in the coherent positive-half pullback image.
Finite linearity of the topological closure submodule then reconstructs the
whole raw actual-analysis `L²` mode in range closure.

This removes exact positive-half preimages from the model-facing endpoint. -/
theorem
    normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_support_rawPowerBounded_mem_positiveHalfPullbackRangeClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointTwoRankPositive
        beta hbeta)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hPowerClosure : ∀ j : Fin (k + 1), c j ≠ 0 →
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) (j : ℕ) ∈
        closure (LinearMap.range (Q.positiveHalfPullback n))) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)) := by
  let R := LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)
  rw [periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2_eq_sum_powerActualAnalysis]
  have hSum :
      (∑ j : Fin (k + 1), c j •
        periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
          (halfExtent n) (beta n) (hbeta n) (j : ℕ)) ∈ R.topologicalClosure := by
    apply R.topologicalClosure.sum_mem
    intro j _hj
    by_cases hcj : c j = 0
    · simp [hcj]
    · apply R.topologicalClosure.smul_mem
      have hj :
          periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
              (halfExtent n) (beta n) (hbeta n) (j : ℕ) ∈
            closure (R : Set _) := by
        simpa [R] using
          Q.normalizedTracePowerActualAnalysis_mem_positiveTimeL2RangeClosure_of_rawBounded_mem_positiveHalfPullbackRangeClosure
            n (j : ℕ) (hPowerClosure j hcj)
      simpa only [Submodule.topologicalClosure_coe] using hj
  simpa only [R, Submodule.topologicalClosure_coe] using hSum

/-- Terminal reconstructed-Hamiltonian consequence with the physical
realization obligation reduced to finitely many sup-norm closure statements,
one for each nonzero trace-power coefficient.

No exact positive-half preimage, pointwise cylinder lift, whole-algebra lift,
global density/surjectivity, multiplicativity, or new Hamiltonian assumption is
used. -/
theorem
    normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_support_rawPowerBounded_mem_positiveHalfPullbackRangeClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointTwoRankPositive
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
    (hPowerClosure : ∀ j : Fin (k + 1), c j ≠ 0 →
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) (j : ℕ) ∈
        closure (LinearMap.range (Q.positiveHalfPullback n)))
    (T : (normalizedTracePowerSupportPositiveHalfPullbackClosureMassEndpointPreHilbert
      Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 ≤ T.physicalYangMillsMass := by
  have hL2Closure :=
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_support_rawPowerBounded_mem_positiveHalfPullbackRangeClosure
      n k c hPowerClosure
  exact
    Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_rawActualAnalysis_mem_positiveTimeRangeClosure
      hInvariant U n k c
      M.halfExtent_gt_one M.beta_pos M.coefficient_ne_zero M.vacuum_orthogonal
      hL2Closure T hSelf

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D