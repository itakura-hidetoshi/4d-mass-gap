import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PositiveTimeBoundaryPairGraphEquality
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransfer
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

private theorem boundaryPairCompletedTransferCriterionTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance boundaryPairCompletedTransferCriterionSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryPairCompletedTransferCriterionTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryPairCompletedTransferCriterionCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryPairCompletedTransferCriterionSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryPairCompletedTransferCriterionMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryPairCompletedTransferCriterionBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryPairCompletedTransferCriterionOpenHalfHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]

private abbrev boundaryPairCompletedTransferCriterionPreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 boundaryPairCompletedTransferCriterionTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 boundaryPairCompletedTransferCriterionTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n

/-- Exact boundary-level criterion for membership in the completed finite
Wilson time-one graph.

A pair `(x₀,x₁)` lies in the graph represented by the canonical boundary
isometry exactly when `x₀` lies in the physical boundary range and the genuine
completed boundary transfer at boundary time two sends `x₀` to `x₁`.
Boundary time two corresponds to physical OS semigroup time one by the existing
half-time convention in `completedBoundaryTransfer`. -/
theorem mem_range_completedPhysicalTransferGraph_iff_mem_range_and_completedBoundaryTransfer_two
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 boundaryPairCompletedTransferCriterionTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 boundaryPairCompletedTransferCriterionTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (xZero xOne : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) 2) :
    (xZero, xOne) ∈ Set.range (fun psi :
        (boundaryPairCompletedTransferCriterionPreHilbert Q hInvariant n).PhysicalHilbert =>
          (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi,
           Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
             (C.finiteOperator n 1 psi))) ↔
      xZero ∈ Set.range (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n) ∧
      Q.completedBoundaryTransfer hInvariant C n 2 xZero = xOne := by
  constructor
  · rintro ⟨psi, hpsi⟩
    have hZero := congrArg Prod.fst hpsi
    have hOne := congrArg Prod.snd hpsi
    refine ⟨⟨psi, hZero⟩, ?_⟩
    calc
      Q.completedBoundaryTransfer hInvariant C n 2 xZero =
          Q.completedBoundaryTransfer hInvariant C n 2
            (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi) := by rw [← hZero]
      _ = Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
            (C.finiteOperator n (2 / 2) psi) := by
        rw [Q.completedBoundaryTransfer_apply_physicalHilbertBoundaryMoment]
      _ = Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
            (C.finiteOperator n 1 psi) := by norm_num
      _ = xOne := hOne
  · rintro ⟨⟨psi, hZero⟩, hTransfer⟩
    refine ⟨psi, ?_⟩
    apply Prod.ext
    · exact hZero
    · have hTransfer' :
          Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
              (C.finiteOperator n 1 psi) = xOne := by
        calc
          Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
              (C.finiteOperator n 1 psi) =
            Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
              (C.finiteOperator n (2 / 2) psi) := by norm_num
          _ = Q.completedBoundaryTransfer hInvariant C n 2
                (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi) := by
            rw [Q.completedBoundaryTransfer_apply_physicalHilbertBoundaryMoment]
          _ = Q.completedBoundaryTransfer hInvariant C n 2 xZero := by rw [hZero]
          _ = xOne := hTransfer
      exact hTransfer'

/-- The positive-time boundary-pair closure condition is therefore equivalent
to a concrete completed-boundary-transfer statement: the time-zero endpoint
must lie in the actual physical OS boundary image, and the genuine completed
boundary transfer at time two must produce the requested time-one endpoint.

This removes all approximating-sequence language from the model-facing seam. -/
theorem oneSidedPositiveTimeSubmoduleBoundaryPairClosureAt_iff_mem_range_and_completedBoundaryTransfer_two
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 boundaryPairCompletedTransferCriterionTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 boundaryPairCompletedTransferCriterionTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f omega fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
        (halfExtent n) 2)) :
    OneSidedPositiveTimeSubmoduleBoundaryPairClosureAt
        Q hInvariant C n f omega fOne omegaOne ↔
      periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
          (halfExtent n) 2 f omega ∈
        Set.range (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n) ∧
      Q.completedBoundaryTransfer hInvariant C n 2
          (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
            (halfExtent n) 2 f omega) =
        periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
          (halfExtent n) 2 fOne omegaOne := by
  rw [Q.oneSidedPositiveTimeSubmoduleBoundaryPairClosureAt_iff_exists_completedTransferGraph
    hInvariant C n f omega fOne omegaOne]
  constructor
  · rintro ⟨psi, hZero, hOne⟩
    refine ⟨⟨psi, hZero⟩, ?_⟩
    calc
      Q.completedBoundaryTransfer hInvariant C n 2
          (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
            (halfExtent n) 2 f omega) =
        Q.completedBoundaryTransfer hInvariant C n 2
          (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi) := by rw [← hZero]
      _ = Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (C.finiteOperator n (2 / 2) psi) := by
        rw [Q.completedBoundaryTransfer_apply_physicalHilbertBoundaryMoment]
      _ = Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (C.finiteOperator n 1 psi) := by norm_num
      _ = periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
          (halfExtent n) 2 fOne omegaOne := hOne
  · rintro ⟨⟨psi, hZero⟩, hTransfer⟩
    refine ⟨psi, hZero, ?_⟩
    calc
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (C.finiteOperator n 1 psi) =
        Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (C.finiteOperator n (2 / 2) psi) := by norm_num
      _ = Q.completedBoundaryTransfer hInvariant C n 2
          (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi) := by
        rw [Q.completedBoundaryTransfer_apply_physicalHilbertBoundaryMoment]
      _ = Q.completedBoundaryTransfer hInvariant C n 2
          (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
            (halfExtent n) 2 f omega) := by rw [hZero]
      _ = periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
          (halfExtent n) 2 fOne omegaOne := hTransfer

/-- A convenient one-way form for downstream endpoint theorems. -/
theorem oneSidedPositiveTimeSubmoduleBoundaryPairClosureAt_of_mem_range_and_completedBoundaryTransfer_two
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 boundaryPairCompletedTransferCriterionTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 boundaryPairCompletedTransferCriterionTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (f omega fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
        (halfExtent n) 2))
    (hRange : periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
        (halfExtent n) 2 f omega ∈
      Set.range (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n))
    (hTransfer : Q.completedBoundaryTransfer hInvariant C n 2
        (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
          (halfExtent n) 2 f omega) =
      periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
        (halfExtent n) 2 fOne omegaOne) :
    OneSidedPositiveTimeSubmoduleBoundaryPairClosureAt
      Q hInvariant C n f omega fOne omegaOne := by
  exact
    (Q.oneSidedPositiveTimeSubmoduleBoundaryPairClosureAt_iff_mem_range_and_completedBoundaryTransfer_two
      hInvariant C n f omega fOne omegaOne).2 ⟨hRange, hTransfer⟩

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end MathlibAnalytic
end MGAP4D