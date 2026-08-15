import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PositiveTimeCylinderDensityBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Topology

noncomputable section

private theorem finitePositiveHalfObservableRangeBridgeTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance finitePositiveHalfObservableRangeBridgeSU2Nontrivial :
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

/-- Every theorem-generated finite positive-half observable on the actual OS
carrier has a concrete preimage under the coherent physical positive-time
pullback.  The preimage is the existing positive-time observable
`Pn.toPositiveTime F`; no surjectivity or density hypothesis is used. -/
theorem finitePositiveHalfObservable_mem_positiveHalfPullback_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive
        beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive
          beta hbeta Q.toWeakStarBridge hInvariant n F ∈
      LinearMap.range (Q.positiveHalfPullback n) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive
        beta hbeta Q.toWeakStarBridge hInvariant n
  refine ⟨Pn.toPositiveTime F, ?_⟩
  exact (Q.finitePositiveHalfObservable_eq_positiveHalfPullback
    hInvariant n F).symm

/-- Hence the entire actual finite-positive-half image of the OS carrier is a
subcarrier of the coherent physical positive-time pullback range.  This is a
range inclusion for the already-constructed finite observables, not a claim
that the coherent pullback is globally surjective. -/
theorem finitePositiveHalfObservable_range_subset_positiveHalfPullback_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    Set.range
        (fun F :
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive
              beta hbeta Q.toWeakStarBridge hInvariant n).Carrier =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive
              beta hbeta Q.toWeakStarBridge hInvariant n F) ⊆
      LinearMap.range (Q.positiveHalfPullback n) := by
  rintro f ⟨F, rfl⟩
  exact Q.finitePositiveHalfObservable_mem_positiveHalfPullback_range hInvariant n F

/-- The finite-positive-half observable image on the actual OS carrier is
exactly the range of the coherent physical positive-time pullback.

The reverse inclusion is not a surjectivity assertion onto all bounded
continuous open-half observables.  It uses the canonical right inverse from a
physical positive-time observable into the OS carrier and then the existing
`finitePositiveHalfObservable_eq_positiveHalfPullback` identity. -/
theorem finitePositiveHalfObservable_range_eq_positiveHalfPullback_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    Set.range
        (fun F :
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive
              beta hbeta Q.toWeakStarBridge hInvariant n).Carrier =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive
              beta hbeta Q.toWeakStarBridge hInvariant n F) =
      LinearMap.range (Q.positiveHalfPullback n) := by
  apply Set.Subset.antisymm
  · exact Q.finitePositiveHalfObservable_range_subset_positiveHalfPullback_range
      hInvariant n
  · rintro u ⟨G, rfl⟩
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive
          beta hbeta Q.toWeakStarBridge hInvariant n
    rcases Pn.carrierToPositiveTimeLinearMap_surjective G with ⟨F, hF⟩
    refine ⟨F, ?_⟩
    calc
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
          S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive
            beta hbeta Q.toWeakStarBridge hInvariant n F =
        Q.positiveHalfPullback n (Pn.toPositiveTime F) :=
          Q.finitePositiveHalfObservable_eq_positiveHalfPullback hInvariant n F
      _ = Q.positiveHalfPullback n G := by
        exact congrArg (fun x => Q.positiveHalfPullback n x) hF

/-- Taking sup-norm closure preserves the exact identification between the
finite OS positive-half image and the coherent positive-half pullback range.
This is the form needed for approximate actual-Wilson/cylinder realization:
no exact preimage of the approximated observable is required. -/
theorem finitePositiveHalfObservable_rangeClosure_eq_positiveHalfPullback_rangeClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    closure
        (Set.range
          (fun F :
            (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive
                beta hbeta Q.toWeakStarBridge hInvariant n).Carrier =>
            physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
              S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive
                beta hbeta Q.toWeakStarBridge hInvariant n F)) =
      closure (LinearMap.range (Q.positiveHalfPullback n)) := by
  rw [Q.finitePositiveHalfObservable_range_eq_positiveHalfPullback_range hInvariant n]

/-- If the actual finite-positive-half OS image is sup-norm dense, the existing
cylinder-density bridge now yields the raw actual-analysis range-closure
statement without a separate `hLift` hypothesis. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_finitePositiveHalfObservable_dense
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ) (c : Fin (k + 1) → ℝ)
    (hDense : Dense
      (Set.range
        (fun F :
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive
              beta hbeta Q.toWeakStarBridge hInvariant n).Carrier =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive
              beta hbeta Q.toWeakStarBridge hInvariant n F))) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveHalfPullback n)) := by
  apply Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_dense_carrier
    n k c
    (Set.range
      (fun F :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive
            beta hbeta Q.toWeakStarBridge hInvariant n).Carrier =>
        physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
          S D halfExtent 2 finitePositiveHalfObservableRangeBridgeTwoRankPositive
            beta hbeta Q.toWeakStarBridge hInvariant n F))
    hDense
  exact Q.finitePositiveHalfObservable_range_subset_positiveHalfPullback_range hInvariant n

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
