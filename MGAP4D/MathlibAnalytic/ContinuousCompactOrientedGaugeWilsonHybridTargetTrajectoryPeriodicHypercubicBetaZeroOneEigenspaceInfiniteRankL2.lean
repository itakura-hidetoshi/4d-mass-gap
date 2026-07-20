import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroZeroEigenspaceMultiplicityOneL2
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A countably infinite linearly independent family contained in one exact joint
sector forces the matching cardinality eigenspace of a finite commuting
idempotent family to have Cardinal rank at least `aleph0`. -/
theorem continuousLinearMap_aleph0_le_rank_cardinalityEigenspace_of_linearIndependent_mem_jointSectorL2
    {ι κ : Type*}
    [Fintype ι]
    [DecidableEq ι]
    [Infinite κ]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (v : κ → V)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (hLinearIndependent : LinearIndependent ℝ v)
    (hMem : ∀ a : κ, v a ∈ continuousLinearMapJointSectorSubmoduleL2 Q s) :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (Module.End.genEigenspace
          ((∑ i : ι, Q i).toLinearMap)
          (s.card : ℝ) 1) := by
  classical
  have hsLe : s.card ≤ Fintype.card ι := by
    simpa using Finset.card_le_card (Finset.subset_univ s)
  let w : κ →
      Module.End.genEigenspace
        ((∑ i : ι, Q i).toLinearMap)
        (s.card : ℝ) 1 :=
    fun a => ⟨v a, by
      rw [← continuousLinearMap_range_cardinalitySectorProjectorL2_eq_eigenspace
        Q s.card hIdempotent hComm hsLe]
      exact ⟨v a,
        continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
          Q s.card s hComm rfl (hMem a)⟩⟩
  have hwLinearIndependent : LinearIndependent ℝ w := by
    apply LinearIndependent.of_comp
      (Module.End.genEigenspace
        ((∑ i : ι, Q i).toLinearMap)
        (s.card : ℝ) 1).subtype
    simpa [w, Function.comp_def] using hLinearIndependent
  exact hwLinearIndependent.aleph0_le_rank

end

end MathlibAnalytic
end MGAP4D
