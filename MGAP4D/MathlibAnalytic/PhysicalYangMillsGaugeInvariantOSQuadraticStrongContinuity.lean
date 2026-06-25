import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveTimeObservableStrongContinuity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PositiveTimeObservableContractionSemigroup

/-- Scalar continuity input for the actual Osterwalder--Schrader quadratic
expectation of translated observable differences.

This is weaker than assuming Hilbert-valued strong continuity directly.  It is
stated entirely in terms of continuum reflected expectations and is therefore
the natural target for dominated-convergence or weak-convergence arguments. -/
structure OSQuadraticContinuityAtZero
    (T : P.PositiveTimeObservableContractionSemigroup) : Prop where
  continuousAt_zero_osQuadraticDifference :
    ∀ F : D.positiveTimeSubalgebra,
      ContinuousAt
        (fun t : NNReal =>
          P.osQuadraticValue
            (P.carrierOfPositiveTime (T.translate t F) -
              P.carrierOfPositiveTime F)) 0

namespace OSQuadraticContinuityAtZero

variable {T : P.PositiveTimeObservableContractionSemigroup}

private theorem osQuadraticDifference_zero
    (F : D.positiveTimeSubalgebra) :
    P.osQuadraticValue
        (P.carrierOfPositiveTime (T.translate 0 F) -
          P.carrierOfPositiveTime F) = 0 := by
  rw [T.translate_zero]
  simp [P.osQuadraticValue_eq_norm_sq]

private theorem physicalStateDifference_dist_sq
    (t : NNReal) (F : D.positiveTimeSubalgebra) :
    dist
        (P.physicalState (P.carrierOfPositiveTime (T.translate t F)))
        (P.physicalState (P.carrierOfPositiveTime F)) ^ 2 =
      P.osQuadraticValue
        (P.carrierOfPositiveTime (T.translate t F) -
          P.carrierOfPositiveTime F) := by
  let A := P.carrierOfPositiveTime (T.translate t F)
  let B := P.carrierOfPositiveTime F
  have hsub :
      P.physicalState A - P.physicalState B = P.physicalState (A - B) := by
    calc
      P.physicalState A - P.physicalState B =
          P.physicalStateLinearMap A - P.physicalStateLinearMap B := by
        rw [P.physicalStateLinearMap_apply, P.physicalStateLinearMap_apply]
      _ = P.physicalStateLinearMap (A - B) := by
        exact (P.physicalStateLinearMap.map_sub A B).symm
      _ = P.physicalState (A - B) := P.physicalStateLinearMap_apply _ _
  calc
    dist (P.physicalState A) (P.physicalState B) ^ 2 =
        ‖P.physicalState A - P.physicalState B‖ ^ 2 := by
      rw [dist_eq_norm]
    _ = ‖P.physicalState (A - B)‖ ^ 2 := by rw [hsub]
    _ = ‖A - B‖ ^ 2 := by rw [P.norm_physicalState]
    _ = P.osQuadraticValue (A - B) := by
      rw [P.osQuadraticValue_eq_norm_sq]
  
/-- Continuity of the scalar OS quadratic difference implies continuity at time
zero of every represented positive-time observable state. -/
theorem physicalState_continuousAt_zero
    (hT : T.OSQuadraticContinuityAtZero)
    (F : D.positiveTimeSubalgebra) :
    ContinuousAt
      (fun t : NNReal =>
        P.physicalState
          (P.carrierOfPositiveTime (T.translate t F))) 0 := by
  rw [Metric.continuousAt_iff]
  intro epsilon hepsilon
  have hepsilonSq : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  rcases Metric.continuousAt_iff.mp
      (hT.continuousAt_zero_osQuadraticDifference F)
      (epsilon ^ 2) hepsilonSq with
    ⟨delta, hdelta, hnear⟩
  refine ⟨delta, hdelta, ?_⟩
  intro t ht
  have hqNear := hnear ht
  have hqNonneg :
      0 ≤ P.osQuadraticValue
        (P.carrierOfPositiveTime (T.translate t F) -
          P.carrierOfPositiveTime F) := by
    rw [P.osQuadraticValue_eq_norm_sq]
    positivity
  have hqLt :
      P.osQuadraticValue
          (P.carrierOfPositiveTime (T.translate t F) -
            P.carrierOfPositiveTime F) < epsilon ^ 2 := by
    rw [osQuadraticDifference_zero (T := T) F, Real.dist_eq, sub_zero,
      abs_of_nonneg hqNonneg] at hqNear
    exact hqNear
  have hdistSq := physicalStateDifference_dist_sq (T := T) t F
  have hdistNonneg :
      0 ≤ dist
        (P.physicalState (P.carrierOfPositiveTime (T.translate t F)))
        (P.physicalState (P.carrierOfPositiveTime F)) := dist_nonneg
  have hzeroState :
      P.physicalState (P.carrierOfPositiveTime (T.translate 0 F)) =
        P.physicalState (P.carrierOfPositiveTime F) := by
    rw [T.translate_zero]
    rfl
  rw [hzeroState]
  nlinarith

/-- Scalar reflected-expectation continuity generates the exact
`StrongContinuityOnObservableStates` input used by the completed OS semigroup. -/
def toStrongContinuityOnObservableStates
    (hT : T.OSQuadraticContinuityAtZero) :
    T.StrongContinuityOnObservableStates where
  continuousAt_zero_on_physicalState :=
    hT.physicalState_continuousAt_zero

end OSQuadraticContinuityAtZero

end PositiveTimeObservableContractionSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
