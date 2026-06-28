import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonOffLinkL2Fluctuation

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Native compact-group orientation-correct heat-bath Hamiltonian on the
Gibbs `L²` space: the finite sum of all physical-link fluctuation
projections. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.heatBathHamiltonianL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure :=
  ∑ target : C.base.geometry.Edge,
    C.singleLinkHeatBathFluctuationL2 target

@[simp] theorem continuous_compact_oriented_heatBathHamiltonianL2_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 f =
      ∑ target : C.base.geometry.Edge,
        C.singleLinkHeatBathFluctuationL2 target f := by
  classical
  simp [ContinuousCompactOrientedGaugeWilsonSystem.heatBathHamiltonianL2]

/-- The native compact-group heat-bath Hamiltonian is self-adjoint in the
pairing sense. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f g : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.heatBathHamiltonianL2 f) g =
      inner ℝ f (C.heatBathHamiltonianL2 g) := by
  classical
  rw [continuous_compact_oriented_heatBathHamiltonianL2_apply,
    continuous_compact_oriented_heatBathHamiltonianL2_apply,
    sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro target _htarget
  exact
    continuous_compact_oriented_singleLinkHeatBathFluctuationL2_inner_symm
      C target f g

/-- The compact heat-bath Hamiltonian quadratic form is the finite sum of
squared local fluctuation norms. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.heatBathHamiltonianL2 f) f =
      ∑ target : C.base.geometry.Edge,
        ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2 := by
  classical
  rw [continuous_compact_oriented_heatBathHamiltonianL2_apply,
    sum_inner]
  apply Finset.sum_congr rfl
  intro target _htarget
  exact
    continuous_compact_oriented_singleLinkHeatBathFluctuationL2_quadraticForm
      C target f

/-- The compact orientation-correct heat-bath Hamiltonian is nonnegative. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    0 ≤ inner ℝ (C.heatBathHamiltonianL2 f) f := by
  rw [continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm]
  exact Finset.sum_nonneg fun target _ => sq_nonneg _

end

end MathlibAnalytic
end MGAP4D
