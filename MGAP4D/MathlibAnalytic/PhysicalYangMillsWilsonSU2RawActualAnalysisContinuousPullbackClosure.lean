import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PositiveTimeSubmoduleRangeClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem continuousPullbackClosureTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance continuousPullbackClosureTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance continuousPullbackClosureCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance continuousPullbackClosureSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance continuousPullbackClosureMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance continuousPullbackClosureBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance continuousPullbackClosureOpenHalfHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

local instance continuousPullbackClosureSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Sup-norm representative of the explicit raw actual-Wilson analysis mode.
On the compact open-half configuration space, `ContinuousMap` and bounded
continuous functions are canonically linearly isometric in Mathlib. -/
noncomputable def
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) ℝ :=
  ContinuousMap.linearIsometryBoundedOfCompact
    (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) ℝ ℝ
    (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMap
      H beta hbeta k c)

/-- Sending the sup-norm raw mode through the canonical bounded-continuous
`toLp` map gives exactly the already-used raw actual-analysis Haar `L²` mode. -/
theorem periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction_toLp
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    BoundedContinuousFunction.toLp
        (E := ℝ) 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2) ℝ
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
          H beta hbeta k c) =
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        H beta hbeta k c := by
  rfl

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

private abbrev continuousPullbackClosurePreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 continuousPullbackClosureTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 continuousPullbackClosureTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n

/-- Sup-norm closure of the coherent positive-time pullback image implies the
`L²` range-closure realization used by the physical-excitation theorem.

The proof is purely functorial: choose an image-valued sequence converging in
the bounded-continuous norm, then apply Mathlib's continuous linear map
`BoundedContinuousFunction.toLp`.  No extra density, surjectivity, Wilson
positivity, or Hamiltonian assumption is inserted here. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_mem_positiveHalfPullbackRangeClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 continuousPullbackClosureTwoRankPositive beta hbeta)
    (n k : ℕ) (c : Fin (k + 1) → ℝ)
    (hClosure : periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
      (halfExtent n) (beta n) (hbeta n) k c ∈ closure (LinearMap.range (Q.positiveHalfPullback n))) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)) := by
  let μ := periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) 2
  let L := BoundedContinuousFunction.toLp (E := ℝ) 2 μ ℝ
  let g := periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
    (halfExtent n) (beta n) (hbeta n) k c
  have hClosureG : g ∈ closure (LinearMap.range (Q.positiveHalfPullback n)) := by
    simpa [g] using hClosure
  rcases mem_closure_iff_seq_limit.mp hClosureG with ⟨u, huRange, huTendsto⟩
  have hLContinuous : Tendsto L (𝓝 g) (𝓝 (L g)) :=
    L.continuous.continuousAt
  have hLpTendsto : Tendsto (fun m => L (u m)) atTop (𝓝 (L g)) :=
    hLContinuous.comp huTendsto
  have hLpRange : ∀ m, L (u m) ∈ LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n) := by
    intro m
    rcases huRange m with ⟨F, hF⟩
    refine ⟨F, ?_⟩
    change L (Q.positiveHalfPullback n F) = L (u m)
    exact congrArg L hF
  have hLpClosure : L g ∈ closure (LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)) :=
    mem_closure_iff_seq_limit.mpr ⟨fun m => L (u m), hLpRange, hLpTendsto⟩
  simpa [L, g,
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction_toLp]
    using hLpClosure

/-- The full downstream reconstructed-Hamiltonian consequence can therefore be
stated using only finite continuous-observable realizability in sup norm. -/
theorem normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 continuousPullbackClosureTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ) (hH : 1 < halfExtent n) (hbetaPos : 0 < beta n) (hc : c ≠ 0)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hClosure : periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
      (halfExtent n) (beta n) (hbeta n) k c ∈ closure (LinearMap.range (Q.positiveHalfPullback n)))
    (T : (continuousPullbackClosurePreHilbert Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) : 0 ≤ T.physicalYangMillsMass := by
  have hL2Closure :=
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_mem_positiveHalfPullbackRangeClosure
      n k c hClosure
  exact Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_rawActualAnalysis_mem_positiveTimeRangeClosure
    hInvariant U n k c hH hbetaPos hc hzero hL2Closure T hSelf

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
