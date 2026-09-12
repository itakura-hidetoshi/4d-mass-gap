import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityTwoPairWitnessL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A vector fixed by three coordinates and killed by every other coordinate
belongs to the corresponding three-element joint sector. -/
theorem continuousLinearMap_mem_triple_jointSectorSubmoduleL2_of_triple_profile
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (target source third : ι)
    {f : V}
    (hTarget : Q target f = f)
    (hSource : Q source f = f)
    (hThird : Q third f = f)
    (hOther :
      ∀ edge : ι,
        edge ≠ target → edge ≠ source → edge ≠ third → Q edge f = 0) :
    f ∈ continuousLinearMapJointSectorSubmoduleL2 Q {target, source, third} := by
  rw [continuousLinearMapJointSectorSubmoduleL2_mem_iff]
  constructor
  · intro edge hEdge
    have hCases : edge = target ∨ edge = source ∨ edge = third := by
      simpa using hEdge
    rcases hCases with hEq | hEq | hEq
    · subst edge
      exact hTarget
    · subst edge
      exact hSource
    · subst edge
      exact hThird
  · intro edge hEdge
    apply hOther edge
    · intro hEq
      subst edge
      exact hEdge (by simp)
    · intro hEq
      subst edge
      exact hEdge (by simp)
    · intro hEq
      subst edge
      exact hEdge (by simp)

/-- Three pairwise distinct entries form a finite set of cardinality three. -/
theorem finset_triple_card_eq_three
    {ι : Type*}
    [DecidableEq ι]
    (target source third : ι)
    (hTargetSource : target ≠ source)
    (hTargetThird : target ≠ third)
    (hSourceThird : source ≠ third) :
    ({target, source, third} : Finset ι).card = 3 := by
  simp [hTargetSource, hTargetThird, hSourceThird]

/-- The cardinality-three projector fixes every vector with a three-coordinate
joint-sector profile. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_three_apply_eq_self_of_triple_profile
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (target source third : ι)
    (hTargetSource : target ≠ source)
    (hTargetThird : target ≠ third)
    (hSourceThird : source ≠ third)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {f : V}
    (hTarget : Q target f = f)
    (hSource : Q source f = f)
    (hThird : Q third f = f)
    (hOther :
      ∀ edge : ι,
        edge ≠ target → edge ≠ source → edge ≠ third → Q edge f = 0) :
    continuousLinearMapCardinalitySectorProjectorL2 Q 3 hComm f = f := by
  exact
    continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
      Q 3 {target, source, third} hComm
      (finset_triple_card_eq_three
        target source third hTargetSource hTargetThird hSourceThird)
      (continuousLinearMap_mem_triple_jointSectorSubmoduleL2_of_triple_profile
        Q target source third hTarget hSource hThird hOther)

/-- A nonzero three-coordinate profile witnesses nonvanishing of the
cardinality-three projector. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_three_ne_zero_of_nonzero_triple_profile
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (target source third : ι)
    (hTargetSource : target ≠ source)
    (hTargetThird : target ≠ third)
    (hSourceThird : source ≠ third)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {f : V}
    (hfNonzero : f ≠ 0)
    (hTarget : Q target f = f)
    (hSource : Q source f = f)
    (hThird : Q third f = f)
    (hOther :
      ∀ edge : ι,
        edge ≠ target → edge ≠ source → edge ≠ third → Q edge f = 0) :
    continuousLinearMapCardinalitySectorProjectorL2 Q 3 hComm ≠ 0 := by
  intro hZero
  have hApply := congrArg (fun T : V →L[ℝ] V => T f) hZero
  have hProjectedZero :
      continuousLinearMapCardinalitySectorProjectorL2 Q 3 hComm f = 0 := by
    simpa using hApply
  have hProjectedSelf :=
    continuousLinearMap_cardinalitySectorProjectorL2_three_apply_eq_self_of_triple_profile
      Q target source third
      hTargetSource hTargetThird hSourceThird hComm
      hTarget hSource hThird hOther
  exact hfNonzero (hProjectedSelf.symm.trans hProjectedZero)

end

end MathlibAnalytic
end MGAP4D
