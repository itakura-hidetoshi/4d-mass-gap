import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonHeatBathHamiltonianL2
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- The normalized compact oriented Gibbs vacuum: the constant-one vector in
`L²` of the Wilson Gibbs measure. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsVacuumL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Lp ℝ 2 C.gibbsMeasure :=
  indicatorConstLp 2 MeasurableSet.univ
    (measure_ne_top C.gibbsMeasure Set.univ) (1 : ℝ)

/-- The compact oriented Gibbs vacuum has norm one. -/
theorem continuous_compact_oriented_gibbsVacuumL2_norm
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    ‖C.gibbsVacuumL2‖ = 1 := by
  rw [ContinuousCompactOrientedGaugeWilsonSystem.gibbsVacuumL2,
    norm_indicatorConstLp]
  · simp
  · norm_num
  · norm_num

/-- Every compact one-link `L²` heat-bath conditional expectation fixes the
Gibbs vacuum. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionL2_vacuum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.singleLinkHeatBathProjectionL2 target C.gibbsVacuumL2 =
      C.gibbsVacuumL2 := by
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply]
  let m := C.base.offLinkMeasurableSpace target
  let hm : m ≤ (inferInstance : MeasurableSpace C.base.Configuration) :=
    compact_oriented_offLinkMeasurableSpace_le C.base target
  have hFix := condExpL2_indicator_of_measurable
    (E := ℝ) (𝕜 := ℝ) hm
    (MeasurableSet.univ : MeasurableSet[m] Set.univ)
    (measure_ne_top C.gibbsMeasure Set.univ)
    (1 : ℝ)
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.gibbsVacuumL2,
    m, hm] using hFix

/-- Every local compact heat-bath fluctuation projection annihilates the
Gibbs vacuum. -/
theorem continuous_compact_oriented_singleLinkHeatBathFluctuationL2_vacuum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.singleLinkHeatBathFluctuationL2 target C.gibbsVacuumL2 = 0 := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply,
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_vacuum]
  simp

/-- The native compact orientation-correct heat-bath Hamiltonian has zero
vacuum energy. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_vacuum
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.heatBathHamiltonianL2 C.gibbsVacuumL2 = 0 := by
  classical
  rw [continuous_compact_oriented_heatBathHamiltonianL2_apply]
  apply Finset.sum_eq_zero
  intro target _htarget
  exact
    continuous_compact_oriented_singleLinkHeatBathFluctuationL2_vacuum
      C target

end

end MathlibAnalytic
end MGAP4D
