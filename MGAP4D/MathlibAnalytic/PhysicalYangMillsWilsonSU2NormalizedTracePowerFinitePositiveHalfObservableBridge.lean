import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2FinitePositiveHalfObservableRangeBridge
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerSupportRangeDerivedRayleighMass
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem normalizedTracePowerFinitePositiveHalfObservableBridgeTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerFinitePositiveHalfObservableBridgeNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerFinitePositiveHalfObservableBridgeTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerFinitePositiveHalfObservableBridgeCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerFinitePositiveHalfObservableBridgeSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerFinitePositiveHalfObservableBridgeMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerFinitePositiveHalfObservableBridgeBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerFinitePositiveHalfObservableBridgeSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance normalizedTracePowerFinitePositiveHalfObservableBridgeBoundaryHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance normalizedTracePowerFinitePositiveHalfObservableBridgeOpenHalfHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

local instance normalizedTracePowerFinitePositiveHalfObservableBridgeOpenHalfHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- The coefficient vector selecting exactly the top normalized-trace power.
This lets us reuse the already-proved polynomial raw-analysis construction
without introducing a second analytic integral. -/
def normalizedTracePowerLastCoefficient (j : ℕ) : Fin (j + 1) → ℝ :=
  fun i => if i = Fin.last j then 1 else 0

/-- Sup-norm representative of one explicit trace-power actual-analysis mode.
It is the existing raw polynomial observable specialized to the one-hot
coefficient vector selecting the power `j`. -/
noncomputable def
    periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (j : ℕ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) ℝ :=
  periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
    H beta hbeta j (normalizedTracePowerLastCoefficient j)

/-- The one-hot polynomial raw-analysis `L²` mode is exactly the previously
constructed trace-power analysis image.  The proof is only finite-dimensional
linearity: after expanding the polynomial, Mathlib's finite-sum simplifier
removes every zero coefficient except `Fin.last j`. -/
theorem
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2_lastCoefficient_eq_powerActualAnalysis
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (j : ℕ) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        H beta hbeta j (normalizedTracePowerLastCoefficient j) =
      periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
        H beta hbeta j := by
  rw [periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2_eq_sum_powerActualAnalysis]
  simp [normalizedTracePowerLastCoefficient]

/-- Therefore the canonical bounded-continuous-to-`L²` map sends the explicit
trace-power sup-norm representative to exactly the trace-power actual-analysis
vector used by the finite-support range theorem. -/
theorem
    periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction_toLp
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (j : ℕ) :
    BoundedContinuousFunction.toLp
        (E := ℝ) 2
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2) ℝ
        (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          H beta hbeta j) =
      periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
        H beta hbeta j := by
  calc
    BoundedContinuousFunction.toLp
        (E := ℝ) 2
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2) ℝ
        (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          H beta hbeta j) =
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        H beta hbeta j (normalizedTracePowerLastCoefficient j) := by
          simpa [periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction]
            using
              periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction_toLp
                H beta hbeta j (normalizedTracePowerLastCoefficient j)
    _ = periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
        H beta hbeta j :=
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2_lastCoefficient_eq_powerActualAnalysis
        H beta hbeta j

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

private abbrev normalizedTracePowerFinitePositiveHalfObservableBridgePreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerFinitePositiveHalfObservableBridgeTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2
      normalizedTracePowerFinitePositiveHalfObservableBridgeTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n

/-- Exact sup-norm range membership of one trace-power raw observable gives
exact `L²` range membership of its actual-analysis image.  This is simply
functoriality of Mathlib's `BoundedContinuousFunction.toLp` through the
already-defined composite `positiveTimeSubmoduleL2LinearMap`. -/
theorem
    normalizedTracePowerActualAnalysis_mem_positiveTimeL2Range_of_rawBounded_mem_positiveHalfPullbackRange
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerFinitePositiveHalfObservableBridgeTwoRankPositive beta hbeta)
    (n j : ℕ)
    (hRange :
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) j ∈
        LinearMap.range (Q.positiveHalfPullback n)) :
    periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) j ∈
      LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n) := by
  rcases hRange with ⟨F, hF⟩
  refine ⟨F, ?_⟩
  calc
    Q.positiveTimeSubmoduleL2LinearMap n F =
      BoundedContinuousFunction.toLp
        (E := ℝ) 2
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) 2) ℝ
        (Q.positiveHalfPullback n F) := rfl
    _ = BoundedContinuousFunction.toLp
        (E := ℝ) 2
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) 2) ℝ
        (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) j) := by
      exact congrArg
        (BoundedContinuousFunction.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) 2) ℝ) hF
    _ = periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) j :=
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction_toLp
        (halfExtent n) (beta n) (hbeta n) j

/-- The previous theorem can be stated with no abstract pullback-range input at
all: membership in the already-constructed finite positive-half OS observable
image is enough, because that image has already been proved equal to the
coherent positive-half pullback range. -/
theorem
    normalizedTracePowerActualAnalysis_mem_positiveTimeL2Range_of_rawBounded_mem_finitePositiveHalfObservableRange
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerFinitePositiveHalfObservableBridgeTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n j : ℕ)
    (hFiniteRange :
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) j ∈
        Set.range
          (fun F :
            (normalizedTracePowerFinitePositiveHalfObservableBridgePreHilbert
              Q hInvariant n).Carrier =>
            physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
              S D halfExtent 2
                normalizedTracePowerFinitePositiveHalfObservableBridgeTwoRankPositive
                beta hbeta Q.toWeakStarBridge hInvariant n F)) :
    periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) j ∈
      LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n) := by
  apply Q.normalizedTracePowerActualAnalysis_mem_positiveTimeL2Range_of_rawBounded_mem_positiveHalfPullbackRange
    n j
  exact Q.finitePositiveHalfObservable_range_subset_positiveHalfPullback_range
    hInvariant n hFiniteRange

/-- For a chosen polynomial, the model-facing range obligation is now only a
finite family of concrete sup-norm trace-power observables indexed by the
nonzero coefficient support.  From those exact finite OS range facts, the full
raw polynomial actual-analysis mode lies in the physical positive-time `L²`
range exactly. -/
theorem
    normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_support_rawPowerBounded_mem_finitePositiveHalfObservableRange
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerFinitePositiveHalfObservableBridgeTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hPowerFiniteRange : ∀ j : Fin (k + 1), c j ≠ 0 →
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) (j : ℕ) ∈
        Set.range
          (fun F :
            (normalizedTracePowerFinitePositiveHalfObservableBridgePreHilbert
              Q hInvariant n).Carrier =>
            physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
              S D halfExtent 2
                normalizedTracePowerFinitePositiveHalfObservableBridgeTwoRankPositive
                beta hbeta Q.toWeakStarBridge hInvariant n F)) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n) := by
  apply Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_support_powerActualAnalysis_mem_range
    n k c
  intro j hcj
  exact
    Q.normalizedTracePowerActualAnalysis_mem_positiveTimeL2Range_of_rawBounded_mem_finitePositiveHalfObservableRange
      hInvariant n (j : ℕ) (hPowerFiniteRange j hcj)

/-- Feeding the same finite concrete support realization into the reconstructed
Hamiltonian route yields the established variational Yang--Mills mass bound.
No global density, global pullback surjectivity, multiplicativity of the
coherent pullback, universal plaquette-algebra lift, or new Hamiltonian
hypothesis is used. -/
theorem
    normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_support_rawPowerBounded_mem_finitePositiveHalfObservableRange
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerFinitePositiveHalfObservableBridgeTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
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
    (hPowerFiniteRange : ∀ j : Fin (k + 1), c j ≠ 0 →
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) (j : ℕ) ∈
        Set.range
          (fun F :
            (normalizedTracePowerFinitePositiveHalfObservableBridgePreHilbert
              Q hInvariant n).Carrier =>
            physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
              S D halfExtent 2
                normalizedTracePowerFinitePositiveHalfObservableBridgeTwoRankPositive
                beta hbeta Q.toWeakStarBridge hInvariant n F))
    (T : (normalizedTracePowerFinitePositiveHalfObservableBridgePreHilbert
      Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 ≤ T.physicalYangMillsMass := by
  apply Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_support_powerActualAnalysis_mem_range
    hInvariant U n k c hH hbetaPos hc hzero _ T hSelf
  intro j hcj
  exact
    Q.normalizedTracePowerActualAnalysis_mem_positiveTimeL2Range_of_rawBounded_mem_finitePositiveHalfObservableRange
      hInvariant n (j : ℕ) (hPowerFiniteRange j hcj)

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
