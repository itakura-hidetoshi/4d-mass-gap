import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveTimeReadout
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set

noncomputable section

private theorem normalizedTracePowerFiniteReadoutEquivalenceTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerFiniteReadoutEquivalenceSU2Nontrivial :
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

private abbrev normalizedTracePowerFiniteReadoutEquivalencePreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerFiniteReadoutEquivalenceTwoRankPositive beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 normalizedTracePowerFiniteReadoutEquivalenceTwoRankPositive
      beta hbeta Q.toWeakStarBridge hInvariant n

/-- A concrete finite-Wilson realization of every normalized-trace power
constructs the reusable positive-time readout record.

The construction uses only the already-proved equality between the range of the
actual finite positive-half observable map and the range of the coherent
positive-half pullback.  In particular, no surjectivity, density,
multiplicativity, decay, coercivity, or Hamiltonian hypothesis is added. -/
noncomputable def normalizedTracePowerPositiveTimeReadout_of_finitePositiveHalfObservableRange
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerFiniteReadoutEquivalenceTwoRankPositive beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n : ℕ)
    (hFiniteRange : ∀ j : ℕ,
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) j ∈
        Set.range
          (fun F :
            (normalizedTracePowerFiniteReadoutEquivalencePreHilbert
              Q hInvariant n).Carrier =>
            physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
              S D halfExtent 2 normalizedTracePowerFiniteReadoutEquivalenceTwoRankPositive
                beta hbeta Q.toWeakStarBridge hInvariant n F)) :
    PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveTimeReadout Q n := by
  have hPullbackRange : ∀ j : ℕ,
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) j ∈
        LinearMap.range (Q.positiveHalfPullback n) := by
    intro j
    rw [← Q.finitePositiveHalfObservable_range_eq_positiveHalfPullback_range
      hInvariant n]
    exact hFiniteRange j
  exact
    { observable := fun j => Classical.choose (hPullbackRange j)
      positiveHalfPullback_eq := fun j => Classical.choose_spec (hPullbackRange j) }

/-- At one finite Wilson scale, existence of the normalized-trace-power
positive-time readout is equivalent to the concrete family of finite
positive-half range statements.

Thus the readout structure is only a reusable packaging of actual finite Wilson
realizability; it is not an additional model assumption. -/
theorem nonempty_normalizedTracePowerPositiveTimeReadout_iff_finitePositiveHalfObservableRange
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerFiniteReadoutEquivalenceTwoRankPositive beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n : ℕ) :
    Nonempty (PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveTimeReadout Q n) ↔
      ∀ j : ℕ,
        periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
            (halfExtent n) (beta n) (hbeta n) j ∈
          Set.range
            (fun F :
              (normalizedTracePowerFiniteReadoutEquivalencePreHilbert
                Q hInvariant n).Carrier =>
              physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
                S D halfExtent 2 normalizedTracePowerFiniteReadoutEquivalenceTwoRankPositive
                  beta hbeta Q.toWeakStarBridge hInvariant n F) := by
  constructor
  · rintro ⟨R⟩ j
    exact Q.normalizedTracePower_rawBounded_mem_finitePositiveHalfObservableRange_of_readout
      hInvariant n j R
  · intro hFiniteRange
    exact ⟨Q.normalizedTracePowerPositiveTimeReadout_of_finitePositiveHalfObservableRange
      hInvariant n hFiniteRange⟩

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
