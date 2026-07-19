import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityThreeTripleWitnessL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A vector fixed by every coordinate in `s` and killed by every coordinate
outside `s` belongs to the corresponding joint sector. -/
theorem continuousLinearMap_mem_jointSectorSubmoduleL2_of_finset_profile
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    {f : V}
    (hSelected : ∀ edge ∈ s, Q edge f = f)
    (hOther : ∀ edge ∉ s, Q edge f = 0) :
    f ∈ continuousLinearMapJointSectorSubmoduleL2 Q s := by
  rw [continuousLinearMapJointSectorSubmoduleL2_mem_iff]
  exact ⟨hSelected, hOther⟩

/-- The cardinality projector indexed by `s.card` fixes every vector with the
exact finite-set coordinate profile `s`. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_card_apply_eq_self_of_finset_profile
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {f : V}
    (hSelected : ∀ edge ∈ s, Q edge f = f)
    (hOther : ∀ edge ∉ s, Q edge f = 0) :
    continuousLinearMapCardinalitySectorProjectorL2 Q s.card hComm f = f := by
  exact
    continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
      Q s.card s hComm rfl
      (continuousLinearMap_mem_jointSectorSubmoduleL2_of_finset_profile
        Q s hSelected hOther)

/-- A nonzero vector with exact finite-set profile `s` witnesses nonvanishing
of the cardinality-`s.card` projector. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_card_ne_zero_of_nonzero_finset_profile
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {f : V}
    (hfNonzero : f ≠ 0)
    (hSelected : ∀ edge ∈ s, Q edge f = f)
    (hOther : ∀ edge ∉ s, Q edge f = 0) :
    continuousLinearMapCardinalitySectorProjectorL2 Q s.card hComm ≠ 0 := by
  intro hZero
  have hApply := congrArg (fun T : V →L[ℝ] V => T f) hZero
  have hProjectedZero :
      continuousLinearMapCardinalitySectorProjectorL2 Q s.card hComm f = 0 := by
    simpa using hApply
  have hProjectedSelf :=
    continuousLinearMap_cardinalitySectorProjectorL2_card_apply_eq_self_of_finset_profile
      Q s hComm hSelected hOther
  exact hfNonzero (hProjectedSelf.symm.trans hProjectedZero)

end

end MathlibAnalytic
end MGAP4D
