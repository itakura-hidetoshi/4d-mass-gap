import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2RawActualAnalysisContinuousPullbackClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem rawActualAnalysisPositiveHalfCylinderApproximationTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance rawActualAnalysisPositiveHalfCylinderApproximationNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance rawActualAnalysisPositiveHalfCylinderApproximationTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance rawActualAnalysisPositiveHalfCylinderApproximationCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance rawActualAnalysisPositiveHalfCylinderApproximationSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance rawActualAnalysisPositiveHalfCylinderApproximationMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance rawActualAnalysisPositiveHalfCylinderApproximationBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance rawActualAnalysisPositiveHalfCylinderApproximationSU2Nontrivial :
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

private abbrev rawActualAnalysisPositiveHalfCylinderApproximationPreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        rawActualAnalysisPositiveHalfCylinderApproximationTwoRankPositive
        beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2
      rawActualAnalysisPositiveHalfCylinderApproximationTwoRankPositive
      beta hbeta Q.toWeakStarBridge hInvariant n

/-- The explicit raw actual-Wilson sup-norm mode lies in the coherent
positive-half pullback closure as soon as it is uniformly approximated by
actual physical positive-time cylinder readouts.

This is strictly more target-specific than lifting the whole actual plaquette
algebra.  No assumption is made about boundary-fixed plaquette generators that
need not themselves be physical gauge-invariant observables.  The approximants
`u m` are required only to have genuine positive-time physical readouts, while
Mathlib handles the sup-norm limit. -/
theorem
    normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_tendsto_positiveHalfCylinderReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        rawActualAnalysisPositiveHalfCylinderApproximationTwoRankPositive
        beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (u : ℕ → BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2) ℝ)
    (R : ∀ m,
      PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n (u m))
    (hu : Tendsto u atTop
      (𝓝
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) k c))) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveHalfPullback n)) := by
  exact
    Q.mem_positiveHalfPullbackRangeClosure_of_tendsto_positiveHalfCylinderReadout
      C hInvariant U n
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) k c)
      u R hu

/-- The same concrete cylinder-readout approximation reaches the open-half Haar
`L²` range closure through the already-proved canonical `C⁰ → L²` map. -/
theorem
    normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_tendsto_positiveHalfCylinderReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        rawActualAnalysisPositiveHalfCylinderApproximationTwoRankPositive
        beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (u : ℕ → BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2) ℝ)
    (R : ∀ m,
      PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n (u m))
    (hu : Tendsto u atTop
      (𝓝
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) k c))) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)) := by
  apply
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_mem_positiveHalfPullbackRangeClosure
  exact
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_tendsto_positiveHalfCylinderReadout
      C hInvariant U n k c u R hu

/-- Terminal reconstructed-Hamiltonian consequence with the remaining physical
realization obligation reduced to one explicit sup-norm convergence statement:
a sequence of genuine positive-time cylinder readouts converges to the raw
actual-Wilson mode.

No whole-algebra lift, boundary-generator gauge-invariance premise, global
density, global surjectivity, multiplicativity of the coherent pullback, or new
Hamiltonian/spectral hypothesis is introduced. -/
theorem
    normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_tendsto_positiveHalfCylinderReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        rawActualAnalysisPositiveHalfCylinderApproximationTwoRankPositive
        beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hH : 1 < halfExtent n)
    (hbetaPos : 0 < beta n)
    (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (periodicHypercubicEvenBoundaryMarginalVacuumL2
          (halfExtent n) (beta n) (hbeta n))
        (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
          (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (u : ℕ → BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2) ℝ)
    (R : ∀ m,
      PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n (u m))
    (hu : Tendsto u atTop
      (𝓝
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) k c)))
    (T : (rawActualAnalysisPositiveHalfCylinderApproximationPreHilbert
      Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 ≤ T.physicalYangMillsMass := by
  apply
    Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure
      hInvariant U n k c hH hbetaPos hc hzero _ T hSelf
  exact
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_tendsto_positiveHalfCylinderReadout
      C hInvariant U n k c u R hu

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
