import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonHeatBathPoincareL2
import MGAP4D.MathlibAnalytic.RealHilbertCenteredAdjointFactorization
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The native compact Wilson heat-bath Hamiltonian preserves the orthogonal
complement of the normalized Gibbs vacuum. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_preserves_vacuumOrthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hf : f ∈ C.VacuumOrthogonalL2) :
    C.heatBathHamiltonianL2 f ∈ C.VacuumOrthogonalL2 := by
  rw [continuous_compact_oriented_mem_vacuumOrthogonalL2_iff] at hf ⊢
  calc
    inner ℝ C.gibbsVacuumL2 (C.heatBathHamiltonianL2 f) =
        inner ℝ (C.heatBathHamiltonianL2 f) C.gibbsVacuumL2 :=
      real_inner_comm _ _
    _ = inner ℝ f (C.heatBathHamiltonianL2 C.gibbsVacuumL2) :=
      continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
        C f C.gibbsVacuumL2
    _ = 0 := by
      rw [continuous_compact_oriented_heatBathHamiltonianL2_vacuum,
        inner_zero_right]

/-- Restriction of the actual compact Wilson heat-bath Hamiltonian to the
Gibbs-vacuum orthogonal Hilbert space. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathHamiltonianL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.VacuumOrthogonalL2 →L[ℝ] C.VacuumOrthogonalL2 :=
  C.heatBathHamiltonianL2.restrict
    (continuous_compact_oriented_heatBathHamiltonianL2_preserves_vacuumOrthogonal C)

@[simp] theorem continuous_compact_oriented_centeredHeatBathHamiltonianL2_coe
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.VacuumOrthogonalL2) :
    ((C.centeredHeatBathHamiltonianL2 f : C.VacuumOrthogonalL2) :
        Lp ℝ 2 C.gibbsMeasure) =
      C.heatBathHamiltonianL2 (f : Lp ℝ 2 C.gibbsMeasure) :=
  rfl

/-- Any native compact heat-bath Poincaré inequality becomes coercivity of the
restricted centered Hamiltonian on its whole carrier. -/
theorem continuous_compact_oriented_centeredHeatBathHamiltonianL2_coercive
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (gap : ℝ)
    (hPoincare : C.HeatBathPoincareL2 gap)
    (f : C.VacuumOrthogonalL2) :
    gap * ‖f‖ ^ 2 ≤
      inner ℝ (C.centeredHeatBathHamiltonianL2 f) f := by
  have hf :
      inner ℝ C.gibbsVacuumL2
        (f : Lp ℝ 2 C.gibbsMeasure) = 0 :=
    (continuous_compact_oriented_mem_vacuumOrthogonalL2_iff C
      (f : Lp ℝ 2 C.gibbsMeasure)).mp f.property
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathHamiltonianL2]
    using
      continuous_compact_oriented_heatBathHamiltonianL2_gap_on_vacuumOrthogonal
        C gap hPoincare (f : Lp ℝ 2 C.gibbsMeasure) hf

/-- The actual centered compact Wilson heat-bath evolution, defined by the
bounded-operator exponential of one half of the restricted heat-bath
Hamiltonian.  The half-time normalization matches the OS boundary transfer
convention, whose squared norm decays at rate `gap * t`. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (t : NNReal) :
    C.VacuumOrthogonalL2 →L[ℝ] C.VacuumOrthogonalL2 :=
  NormedSpace.exp ℝ
    ((-((t : ℝ) / 2)) • C.centeredHeatBathHamiltonianL2)

@[simp] theorem continuous_compact_oriented_centeredHeatBathEvolutionL2_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.centeredHeatBathEvolutionL2 0 =
      ContinuousLinearMap.id ℝ C.VacuumOrthogonalL2 := by
  simp [ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2]

end

end MathlibAnalytic
end MGAP4D