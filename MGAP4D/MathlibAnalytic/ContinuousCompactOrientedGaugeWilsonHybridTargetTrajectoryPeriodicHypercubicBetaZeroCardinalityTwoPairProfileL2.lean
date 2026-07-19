import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityOneSingletonWitnessL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A vector fixed by two distinct coordinates and killed by every other
coordinate belongs to the corresponding two-element joint sector. -/
theorem continuousLinearMap_mem_pair_jointSectorSubmoduleL2_of_pair_profile
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (target source : ι)
    {f : V}
    (hTarget : Q target f = f)
    (hSource : Q source f = f)
    (hOther : ∀ edge : ι, edge ≠ target → edge ≠ source → Q edge f = 0) :
    f ∈ continuousLinearMapJointSectorSubmoduleL2 Q {target, source} := by
  rw [continuousLinearMapJointSectorSubmoduleL2_mem_iff]
  constructor
  · intro edge hEdge
    have hCases : edge = target ∨ edge = source := by
      simpa using hEdge
    rcases hCases with hEq | hEq
    · subst edge
      exact hTarget
    · subst edge
      exact hSource
  · intro edge hEdge
    apply hOther edge
    · intro hEq
      subst edge
      exact hEdge (by simp)
    · intro hEq
      subst edge
      exact hEdge (by simp)

/-- A two-element finite set has cardinality two when its entries are distinct. -/
theorem finset_pair_card_eq_two
    {ι : Type*}
    [DecidableEq ι]
    (target source : ι)
    (hNe : target ≠ source) :
    ({target, source} : Finset ι).card = 2 := by
  simpa [hNe]

/-- The cardinality-two projector fixes every vector with a two-coordinate
joint-sector profile. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_two_apply_eq_self_of_pair_profile
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (target source : ι)
    (hNe : target ≠ source)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {f : V}
    (hTarget : Q target f = f)
    (hSource : Q source f = f)
    (hOther : ∀ edge : ι, edge ≠ target → edge ≠ source → Q edge f = 0) :
    continuousLinearMapCardinalitySectorProjectorL2 Q 2 hComm f = f := by
  exact
    continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
      Q 2 {target, source} hComm
      (finset_pair_card_eq_two target source hNe)
      (continuousLinearMap_mem_pair_jointSectorSubmoduleL2_of_pair_profile
        Q target source hTarget hSource hOther)

/-- A nonzero two-coordinate profile witnesses nonvanishing of the
cardinality-two projector. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_two_ne_zero_of_nonzero_pair_profile
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (target source : ι)
    (hNe : target ≠ source)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {f : V}
    (hfNonzero : f ≠ 0)
    (hTarget : Q target f = f)
    (hSource : Q source f = f)
    (hOther : ∀ edge : ι, edge ≠ target → edge ≠ source → Q edge f = 0) :
    continuousLinearMapCardinalitySectorProjectorL2 Q 2 hComm ≠ 0 := by
  intro hZero
  have hApply := congrArg (fun T : V →L[ℝ] V => T f) hZero
  have hProjectedZero :
      continuousLinearMapCardinalitySectorProjectorL2 Q 2 hComm f = 0 := by
    simpa using hApply
  have hProjectedSelf :=
    continuousLinearMap_cardinalitySectorProjectorL2_two_apply_eq_self_of_pair_profile
      Q target source hNe hComm hTarget hSource hOther
  exact hfNonzero (hProjectedSelf.symm.trans hProjectedZero)

end

end MathlibAnalytic
end MGAP4D
