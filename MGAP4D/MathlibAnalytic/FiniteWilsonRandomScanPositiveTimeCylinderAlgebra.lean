import MGAP4D.MathlibAnalytic.LinearMarkovPositiveTimeCylinderAlgebra
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanInfinitePathCylinderIntegral
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanInfinitePathShiftInvariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The concrete real algebra of strictly positive-time cylinder observables on
the actual finite Wilson random-scan path space. -/
abbrev FiniteLatticeWilsonSystem.randomScanPositiveTimeCylinderSubalgebra
    (L : FiniteLatticeWilsonSystem) :
    Subalgebra ℝ ((ℕ → L.Configuration) → ℝ) :=
  linearMarkovPositiveTimeCylinderSubalgebra (Ω := L.Configuration)

/-- The concrete one-step translation endomorphism of finite Wilson positive-time
cylinder observables. -/
abbrev FiniteLatticeWilsonSystem.randomScanPositiveTimeShiftAlgHom
    (L : FiniteLatticeWilsonSystem) :
    L.randomScanPositiveTimeCylinderSubalgebra →ₐ[ℝ]
      L.randomScanPositiveTimeCylinderSubalgebra :=
  linearMarkovPositiveTimeShiftAlgHom

/-- Every finite product supported at consecutive positive natural times belongs
to the actual Wilson positive-time cylinder algebra. -/
theorem finite_lattice_randomScanPositiveTimePathProduct_mem
    (L : FiniteLatticeWilsonSystem)
    (n : ℕ)
    (fs : Fin (n + 1) → L.Configuration → ℝ) :
    linearMarkovPositiveTimePathProduct fs ∈
      L.randomScanPositiveTimeCylinderSubalgebra :=
  linearMarkovPositiveTimePathProduct_mem fs

/-- The Gibbs-started stationary Wilson path expectation is preserved by the
positive-time translation endomorphism. -/
theorem finite_lattice_randomScanPositiveTimeCylinder_integral_shift
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F : L.randomScanPositiveTimeCylinderSubalgebra) :
    (∫ path,
        (((L.randomScanPositiveTimeShiftAlgHom F :
          L.randomScanPositiveTimeCylinderSubalgebra) :
            (ℕ → L.Configuration) → ℝ) path)
      ∂L.randomScanInfinitePathMeasure) =
      ∫ path, ((F : (ℕ → L.Configuration) → ℝ) path)
        ∂L.randomScanInfinitePathMeasure := by
  unfold FiniteLatticeWilsonSystem.randomScanInfinitePathMeasure
  exact linearMarkovPositiveTimeCylinder_integral_shift
    L.gibbsPMF L.randomScanTransitionPMF
    (finite_lattice_randomScanTransitionPMF_gibbs_expectation_stationary L)
    F

/-- Every consecutive strictly positive-time product cylinder under the actual
infinite Wilson random-scan path law has exactly the existing random-scan
cylinder moment. -/
theorem finite_lattice_randomScanInfinitePathMeasure_positiveTime_cylinder_integral
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (fs : Fin (n + 1) → L.Configuration → ℝ) :
    (∫ path,
        linearMarkovPositiveTimePathProduct fs path
      ∂L.randomScanInfinitePathMeasure) =
      L.randomScanCylinderMoment (List.ofFn fs) := by
  unfold FiniteLatticeWilsonSystem.randomScanInfinitePathMeasure
  rw [linearMarkovInfinitePathMeasure_positiveTime_cylinder_integral
    L.gibbsPMF L.randomScanTransitionPMF
    (finite_lattice_randomScanTransitionPMF_gibbs_expectation_stationary L)]
  rw [finite_lattice_randomScanTransitionExpectationLinearMap_eq L]
  unfold FiniteLatticeWilsonSystem.randomScanCylinderMoment
    linearMarkovCylinderMoment
  rw [finite_lattice_finitePMFExpectationReal_gibbsPMF]

end

end MathlibAnalytic
end MGAP4D
