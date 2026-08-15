import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerFinitePositiveHalfObservableBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem normalizedTracePowerPositiveTimeReadoutTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerPositiveTimeReadoutNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerPositiveTimeReadoutTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerPositiveTimeReadoutCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerPositiveTimeReadoutSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerPositiveTimeReadoutMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerPositiveTimeReadoutBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerPositiveTimeReadoutSU2Nontrivial :
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

/-- Concrete model-facing readout data for the normalized-trace-power family at
one finite Wilson scale.

This is deliberately much weaker than surjectivity of `positiveHalfPullback`:
it chooses only the countable family of positive-time observables whose finite
readouts are the explicit trace-power raw actual-analysis representatives.  No
multiplicativity, density, decay, coercivity, or Hamiltonian statement is part
of the data.  A subsequent actual Wilson/cylinder construction should build
this structure rather than assume a global range property. -/
structure PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveTimeReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerPositiveTimeReadoutTwoRankPositive beta hbeta)
    (n : ℕ) where
  observable : ℕ → D.positiveTimeSubalgebra.toSubmodule
  positiveHalfPullback_eq : ∀ j : ℕ,
    Q.positiveHalfPullback n (observable j) =
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) j

namespace PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveTimeReadout

variable
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerPositiveTimeReadoutTwoRankPositive beta hbeta}
    {n : ℕ}

/-- Every trace-power representative selected by concrete readout data lies in
the coherent positive-half pullback range, with the selected positive-time
observable as an explicit preimage. -/
theorem rawBounded_mem_positiveHalfPullbackRange
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveTimeReadout Q n)
    (j : ℕ) :
    periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) j ∈
      LinearMap.range (Q.positiveHalfPullback n) := by
  refine ⟨R.observable j, ?_⟩
  exact R.positiveHalfPullback_eq j

end PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveTimeReadout

/-- Concrete trace-power readout data automatically realizes every selected
raw bounded observable in the theorem-generated finite positive-half OS image.
The reverse carrier construction is supplied by the already-proved exact range
equality; no global surjectivity assertion is introduced. -/
theorem normalizedTracePower_rawBounded_mem_finitePositiveHalfObservableRange_of_readout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerPositiveTimeReadoutTwoRankPositive beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n j : ℕ)
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveTimeReadout Q n) :
    periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) j ∈
      Set.range
        (fun F :
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent 2 normalizedTracePowerPositiveTimeReadoutTwoRankPositive
              beta hbeta Q.toWeakStarBridge hInvariant n).Carrier =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent 2 normalizedTracePowerPositiveTimeReadoutTwoRankPositive
              beta hbeta Q.toWeakStarBridge hInvariant n F) := by
  rw [Q.finitePositiveHalfObservable_range_eq_positiveHalfPullback_range hInvariant n]
  exact R.rawBounded_mem_positiveHalfPullbackRange j

/-- Once the concrete trace-power readout family is supplied, the supportwise
finite-range premise of the previous theorem disappears completely.  Mathlib
finite linearity then places the whole normalized-trace polynomial raw
actual-analysis vector in the exact physical positive-time `L²` range. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_readout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerPositiveTimeReadoutTwoRankPositive beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveTimeReadout Q n) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n) := by
  apply Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_support_rawPowerBounded_mem_finitePositiveHalfObservableRange
    hInvariant n k c
  intro j _
  exact Q.normalizedTracePower_rawBounded_mem_finitePositiveHalfObservableRange_of_readout
    hInvariant n (j : ℕ) R

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
