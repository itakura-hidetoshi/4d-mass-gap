import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonCenteredHeatBathEvolutionL2
import MGAP4D.MathlibAnalytic.RealContinuousLinearOperatorExponentialSemigroupPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The bounded generator of the full compact Wilson heat-bath semigroup.  The
factor `1/2` matches the existing heat-bath evolution normalization. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathGeneratorL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure :=
  (-(1 / 2 : ℝ)) • C.heatBathHamiltonianL2

/-- Real-time extension of the already constructed nonnegative-time compact
Wilson heat-bath evolution. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (t : ℝ) :
    Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure :=
  realContinuousLinearOperatorExponentialSemigroup
    C.fullHeatBathGeneratorL2 t

/-- The real-time extension restricts exactly to the existing `NNReal`-time
heat-bath evolution. -/
theorem continuous_compact_oriented_fullHeatBathEvolutionRealL2_nnreal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (t : NNReal) :
    C.fullHeatBathEvolutionRealL2 (t : ℝ) = C.heatBathEvolutionL2 t := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
  unfold ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathGeneratorL2
  unfold realContinuousLinearOperatorExponentialSemigroup
  unfold ContinuousCompactOrientedGaugeWilsonSystem.heatBathEvolutionL2
  congr 1
  module

@[simp] theorem continuous_compact_oriented_fullHeatBathEvolutionRealL2_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.fullHeatBathEvolutionRealL2 0 = 1 :=
  realContinuousLinearOperatorExponentialSemigroup_zero
    C.fullHeatBathGeneratorL2

/-- Exact additive semigroup law on the full Gibbs `L²` carrier. -/
theorem continuous_compact_oriented_fullHeatBathEvolutionRealL2_add
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (s t : ℝ) :
    C.fullHeatBathEvolutionRealL2 (s + t) =
      C.fullHeatBathEvolutionRealL2 s *
        C.fullHeatBathEvolutionRealL2 t :=
  realContinuousLinearOperatorExponentialSemigroup_add
    C.fullHeatBathGeneratorL2 s t

/-- Operator-norm continuity of the full compact Wilson heat-bath semigroup. -/
theorem continuous_compact_oriented_fullHeatBathEvolutionRealL2_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Continuous C.fullHeatBathEvolutionRealL2 :=
  continuous_realContinuousLinearOperatorExponentialSemigroup
    C.fullHeatBathGeneratorL2

/-- Operator-norm derivative at every real time. -/
theorem continuous_compact_oriented_fullHeatBathEvolutionRealL2_hasDerivAt
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (t : ℝ) :
    HasDerivAt C.fullHeatBathEvolutionRealL2
      (C.fullHeatBathEvolutionRealL2 t * C.fullHeatBathGeneratorL2) t :=
  realContinuousLinearOperatorExponentialSemigroup_hasDerivAt
    C.fullHeatBathGeneratorL2 t

/-- At time zero, the operator generator is exactly minus one half of the
native compact Wilson heat-bath Hamiltonian. -/
theorem continuous_compact_oriented_fullHeatBathEvolutionRealL2_hasDerivAt_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    HasDerivAt C.fullHeatBathEvolutionRealL2
      ((-(1 / 2 : ℝ)) • C.heatBathHamiltonianL2) 0 := by
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathGeneratorL2]
    using
      (continuous_compact_oriented_fullHeatBathEvolutionRealL2_hasDerivAt C 0)

/-- Strong derivative on every Gibbs `L²` state. -/
theorem continuous_compact_oriented_fullHeatBathEvolutionRealL2_hasDerivAt_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (t : ℝ)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    HasDerivAt
      (fun u : ℝ => C.fullHeatBathEvolutionRealL2 u f)
      ((C.fullHeatBathEvolutionRealL2 t * C.fullHeatBathGeneratorL2) f) t :=
  realContinuousLinearOperatorExponentialSemigroup_hasDerivAt_apply
    C.fullHeatBathGeneratorL2 t f

/-- Strong generator identity at time zero. -/
theorem continuous_compact_oriented_fullHeatBathEvolutionRealL2_hasDerivAt_zero_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    HasDerivAt
      (fun u : ℝ => C.fullHeatBathEvolutionRealL2 u f)
      (-(1 / 2 : ℝ) • C.heatBathHamiltonianL2 f) 0 := by
  have h :=
    continuous_compact_oriented_fullHeatBathEvolutionRealL2_hasDerivAt_apply
      C 0 f
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathGeneratorL2]
    using h

/-- The full heat-bath semigroup fixes the normalized Gibbs vacuum at every
real time. -/
theorem continuous_compact_oriented_fullHeatBathEvolutionRealL2_vacuum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (t : ℝ) :
    C.fullHeatBathEvolutionRealL2 t C.gibbsVacuumL2 = C.gibbsVacuumL2 := by
  have hgen :
      C.fullHeatBathGeneratorL2 C.gibbsVacuumL2 =
        (0 : ℝ) • C.gibbsVacuumL2 := by
    unfold ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathGeneratorL2
    rw [ContinuousLinearMap.smul_apply,
      continuous_compact_oriented_heatBathHamiltonianL2_vacuum]
    simp
  have h :=
    realContinuousLinearOperatorExponentialSemigroup_apply_eigenvector
      C.fullHeatBathGeneratorL2 C.gibbsVacuumL2 0 t hgen
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2]
    using h

@[simp] theorem continuous_compact_oriented_heatBathEvolutionL2_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.heatBathEvolutionL2 0 = 1 := by
  rw [← continuous_compact_oriented_fullHeatBathEvolutionRealL2_nnreal C 0]
  exact continuous_compact_oriented_fullHeatBathEvolutionRealL2_zero C

/-- The existing nonnegative-time heat-bath evolution is an exact semigroup. -/
theorem continuous_compact_oriented_heatBathEvolutionL2_add
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (s t : NNReal) :
    C.heatBathEvolutionL2 (s + t) =
      C.heatBathEvolutionL2 s * C.heatBathEvolutionL2 t := by
  rw [← continuous_compact_oriented_fullHeatBathEvolutionRealL2_nnreal C (s + t),
    ← continuous_compact_oriented_fullHeatBathEvolutionRealL2_nnreal C s,
    ← continuous_compact_oriented_fullHeatBathEvolutionRealL2_nnreal C t]
  simpa using
    continuous_compact_oriented_fullHeatBathEvolutionRealL2_add
      C (s : ℝ) (t : ℝ)

/-- The existing nonnegative-time evolution fixes the Gibbs vacuum. -/
theorem continuous_compact_oriented_heatBathEvolutionL2_vacuum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (t : NNReal) :
    C.heatBathEvolutionL2 t C.gibbsVacuumL2 = C.gibbsVacuumL2 := by
  rw [← continuous_compact_oriented_fullHeatBathEvolutionRealL2_nnreal]
  exact continuous_compact_oriented_fullHeatBathEvolutionRealL2_vacuum C (t : ℝ)

/-- On a vacuum-orthogonal state, the centered and full evolutions agree
exactly. -/
theorem continuous_compact_oriented_centeredHeatBathEvolutionL2_eq_full_of_orthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (t : NNReal)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hf : inner ℝ C.gibbsVacuumL2 f = 0) :
    C.centeredHeatBathEvolutionL2 t f = C.heatBathEvolutionL2 t f := by
  rw [continuous_compact_oriented_centeredHeatBathEvolutionL2_apply,
    continuous_compact_oriented_vacuumCenteredL2_eq_self C f hf]

end

end MathlibAnalytic
end MGAP4D
