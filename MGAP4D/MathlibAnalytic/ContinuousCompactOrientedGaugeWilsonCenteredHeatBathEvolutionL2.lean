import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonHeatBathPoincareL2
import MGAP4D.MathlibAnalytic.RealHilbertCenteredAdjointFactorization
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

/-- The normalized Gibbs-vacuum rank-one projection. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsVacuumProjectionL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure :=
  ContinuousLinearMap.smulRight
    (innerSL ℝ C.gibbsVacuumL2) C.gibbsVacuumL2

@[simp] theorem continuous_compact_oriented_gibbsVacuumProjectionL2_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.gibbsVacuumProjectionL2 f =
      inner ℝ C.gibbsVacuumL2 f • C.gibbsVacuumL2 :=
  rfl

/-- Orthogonal centering away from the normalized Gibbs vacuum, bundled as a
continuous linear map. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteringL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure :=
  ContinuousLinearMap.id ℝ (Lp ℝ 2 C.gibbsMeasure) -
    C.gibbsVacuumProjectionL2

@[simp] theorem continuous_compact_oriented_vacuumCenteringL2_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.vacuumCenteringL2 f = C.vacuumCenteredL2 f :=
  rfl

/-- Vacuum centering fixes every vector orthogonal to the Gibbs vacuum. -/
theorem continuous_compact_oriented_vacuumCenteringL2_apply_of_orthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hf : inner ℝ C.gibbsVacuumL2 f = 0) :
    C.vacuumCenteringL2 f = f := by
  rw [continuous_compact_oriented_vacuumCenteringL2_apply,
    continuous_compact_oriented_vacuumCenteredL2_eq_self C f hf]

/-- The actual bounded-operator heat-bath evolution on the full finite Wilson
Gibbs `L²` carrier.  It fixes the Gibbs vacuum and is therefore not claimed to
contract below one on the full space. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.heatBathEvolutionL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (t : NNReal) :
    Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure :=
  NormedSpace.exp
    ((-((t : ℝ) / 2)) • C.heatBathHamiltonianL2)

/-- The actual centered heat-bath evolution: first remove the normalized Gibbs
vacuum component, then apply the bounded-operator exponential.  This operator
annihilates the vacuum and is the correct full-space representative of the
vacuum-orthogonal dynamics. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (t : NNReal) :
    Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure :=
  C.heatBathEvolutionL2 t ∘L C.vacuumCenteringL2

@[simp] theorem continuous_compact_oriented_centeredHeatBathEvolutionL2_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (t : NNReal)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.centeredHeatBathEvolutionL2 t f =
      C.heatBathEvolutionL2 t (C.vacuumCenteredL2 f) :=
  rfl

@[simp] theorem continuous_compact_oriented_centeredHeatBathEvolutionL2_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.centeredHeatBathEvolutionL2 0 = C.vacuumCenteringL2 := by
  simp [ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2,
    ContinuousCompactOrientedGaugeWilsonSystem.heatBathEvolutionL2]

/-- Any native compact heat-bath Poincaré inequality gives coercivity of the
actual heat-bath Hamiltonian on every explicitly centered vector. -/
theorem continuous_compact_oriented_centeredHeatBathHamiltonianL2_coercive
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (gap : ℝ)
    (hPoincare : C.HeatBathPoincareL2 gap)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hf : inner ℝ C.gibbsVacuumL2 f = 0) :
    gap * ‖f‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 f) f :=
  continuous_compact_oriented_heatBathHamiltonianL2_gap_on_vacuumOrthogonal
    C gap hPoincare f hf

end

end MathlibAnalytic
end MGAP4D