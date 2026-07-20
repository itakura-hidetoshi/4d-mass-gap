import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityEigenspaceRankLowerBoundL2
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators DirectSum Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The ordinary eigenspaces of the full coordinate sum at the admissible
integer eigenvalues `0, ..., card ι`. -/
noncomputable def continuousLinearMapCardinalityEigenspaceFamilyL2
    {ι : Type*}
    [Fintype ι]
    (Q : ι → V →L[ℝ] V) :
    Fin (Fintype.card ι + 1) → Submodule ℝ V :=
  fun k =>
    Module.End.genEigenspace
      ((∑ i : ι, Q i).toLinearMap)
      (k.1 : ℝ)
      1

/-- Eigenspaces at distinct admissible integer values are supremum-independent. -/
theorem continuousLinearMap_cardinalityEigenspaceFamilyL2_iSupIndep
    {ι : Type*}
    [Fintype ι]
    (Q : ι → V →L[ℝ] V) :
    iSupIndep (continuousLinearMapCardinalityEigenspaceFamilyL2 Q) := by
  classical
  let H : Module.End ℝ V := (∑ i : ι, Q i).toLinearMap
  have hAll :
      iSupIndep (fun μ : ℝ => Module.End.genEigenspace H μ 1) :=
    Module.End.independent_genEigenspace H 1
  have hCastInjective :
      Function.Injective
        (fun k : Fin (Fintype.card ι + 1) => (k.1 : ℝ)) := by
    intro a b hab
    apply Fin.ext
    exact_mod_cast hab
  simpa [continuousLinearMapCardinalityEigenspaceFamilyL2, H,
    Function.comp_def]
    using hAll.comp hCastInjective

/-- For a finite commuting idempotent family, the admissible integer
eigenspaces span the whole module. -/
theorem continuousLinearMap_iSup_cardinalityEigenspaceFamilyL2_eq_top
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    (⨆ k : Fin (Fintype.card ι + 1),
      continuousLinearMapCardinalityEigenspaceFamilyL2 Q k) = ⊤ := by
  classical
  apply le_antisymm
  · exact le_top
  · intro f _hf
    have hDecomp :
        (∑ k ∈ Finset.range (Fintype.card ι + 1),
          continuousLinearMapCardinalitySectorProjectorL2 Q k hComm f) = f := by
      have hOperator :=
        continuousLinearMap_sum_range_cardinalitySectorProjectorL2_eq_one
          Q hComm
      have hApply := congrArg
        (fun T : V →L[ℝ] V => T f)
        hOperator
      simpa using hApply
    rw [← hDecomp]
    refine
      (⨆ k : Fin (Fintype.card ι + 1),
        continuousLinearMapCardinalityEigenspaceFamilyL2 Q k).sum_mem ?_
    intro k hk
    have hkLe : k ≤ Fintype.card ι :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hRangeMem :
        continuousLinearMapCardinalitySectorProjectorL2 Q k hComm f ∈
          LinearMap.range
            (continuousLinearMapCardinalitySectorProjectorL2 Q k hComm).toLinearMap := by
      exact ⟨f, rfl⟩
    have hEigMem :
        continuousLinearMapCardinalitySectorProjectorL2 Q k hComm f ∈
          continuousLinearMapCardinalityEigenspaceFamilyL2 Q
            ⟨k, Finset.mem_range.mp hk⟩ := by
      rw [continuousLinearMapCardinalityEigenspaceFamilyL2]
      rw [← continuousLinearMap_range_cardinalitySectorProjectorL2_eq_eigenspace
        Q k hIdempotent hComm hkLe]
      exact hRangeMem
    exact
      (le_iSup
        (fun j : Fin (Fintype.card ι + 1) =>
          continuousLinearMapCardinalityEigenspaceFamilyL2 Q j)
        ⟨k, Finset.mem_range.mp hk⟩)
        hEigMem

/-- The admissible integer eigenspaces form an internal direct-sum
decomposition for every finite commuting idempotent family. -/
theorem continuousLinearMap_cardinalityEigenspaceFamilyL2_isInternal
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    DirectSum.IsInternal
      (continuousLinearMapCardinalityEigenspaceFamilyL2 Q) := by
  exact
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (continuousLinearMap_cardinalityEigenspaceFamilyL2_iSupIndep Q)
      (continuousLinearMap_iSup_cardinalityEigenspaceFamilyL2_eq_top
        Q hIdempotent hComm)

end

end MathlibAnalytic
end MGAP4D
