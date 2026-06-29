import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanSpectralEnclosureL2
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The heat-bath Hamiltonian sends every vector into the orthogonal complement
of the normalized Gibbs vacuum. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_mem_vacuumOrthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 f ∈ C.VacuumOrthogonalL2 := by
  rw [continuous_compact_oriented_mem_vacuumOrthogonalL2_iff]
  calc
    inner ℝ C.gibbsVacuumL2 (C.heatBathHamiltonianL2 f) =
        inner ℝ (C.heatBathHamiltonianL2 C.gibbsVacuumL2) f := by
      symm
      exact continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
        C C.gibbsVacuumL2 f
    _ = 0 := by
      rw [continuous_compact_oriented_heatBathHamiltonianL2_vacuum,
        inner_zero_left]

/-- The normalized random-scan operator restricted to the genuine
Gibbs-vacuum orthogonal Hilbert sector. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.randomScanVacuumOrthogonalL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge) :
    C.VacuumOrthogonalL2 →L[ℝ] C.VacuumOrthogonalL2 :=
  C.randomScanHeatBathL2.restrict fun f hf =>
    continuous_compact_oriented_randomScanHeatBathL2_mem_vacuumOrthogonal
      C hEdge f hf

/-- The native heat-bath Hamiltonian restricted to the genuine
Gibbs-vacuum orthogonal Hilbert sector. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.heatBathHamiltonianVacuumOrthogonalL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.VacuumOrthogonalL2 →L[ℝ] C.VacuumOrthogonalL2 :=
  C.heatBathHamiltonianL2.restrict fun f _hf =>
    continuous_compact_oriented_heatBathHamiltonianL2_mem_vacuumOrthogonal C f

@[simp] theorem continuous_compact_oriented_randomScanVacuumOrthogonalL2_coe_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : C.VacuumOrthogonalL2) :
    ((C.randomScanVacuumOrthogonalL2 hEdge f : C.VacuumOrthogonalL2) :
        Lp ℝ 2 C.gibbsMeasure) =
      C.randomScanHeatBathL2 (f : Lp ℝ 2 C.gibbsMeasure) :=
  rfl

@[simp] theorem continuous_compact_oriented_heatBathHamiltonianVacuumOrthogonalL2_coe_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.VacuumOrthogonalL2) :
    ((C.heatBathHamiltonianVacuumOrthogonalL2 f : C.VacuumOrthogonalL2) :
        Lp ℝ 2 C.gibbsMeasure) =
      C.heatBathHamiltonianL2 (f : Lp ℝ 2 C.gibbsMeasure) :=
  rfl

/-- Restricted random scan remains self-adjoint on the vacuum-orthogonal
Hilbert sector. -/
theorem continuous_compact_oriented_randomScanVacuumOrthogonalL2_inner_symm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f g : C.VacuumOrthogonalL2) :
    inner ℝ (C.randomScanVacuumOrthogonalL2 hEdge f) g =
      inner ℝ f (C.randomScanVacuumOrthogonalL2 hEdge g) := by
  change
    inner ℝ
        (C.randomScanHeatBathL2 (f : Lp ℝ 2 C.gibbsMeasure))
        (g : Lp ℝ 2 C.gibbsMeasure) =
      inner ℝ
        (f : Lp ℝ 2 C.gibbsMeasure)
        (C.randomScanHeatBathL2 (g : Lp ℝ 2 C.gibbsMeasure))
  exact continuous_compact_oriented_randomScanHeatBathL2_inner_symm
    C (f : Lp ℝ 2 C.gibbsMeasure) (g : Lp ℝ 2 C.gibbsMeasure)

/-- Restricted heat-bath Hamiltonian remains self-adjoint on the
vacuum-orthogonal Hilbert sector. -/
theorem continuous_compact_oriented_heatBathHamiltonianVacuumOrthogonalL2_inner_symm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f g : C.VacuumOrthogonalL2) :
    inner ℝ (C.heatBathHamiltonianVacuumOrthogonalL2 f) g =
      inner ℝ f (C.heatBathHamiltonianVacuumOrthogonalL2 g) := by
  change
    inner ℝ
        (C.heatBathHamiltonianL2 (f : Lp ℝ 2 C.gibbsMeasure))
        (g : Lp ℝ 2 C.gibbsMeasure) =
      inner ℝ
        (f : Lp ℝ 2 C.gibbsMeasure)
        (C.heatBathHamiltonianL2 (g : Lp ℝ 2 C.gibbsMeasure))
  exact continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
    C (f : Lp ℝ 2 C.gibbsMeasure) (g : Lp ℝ 2 C.gibbsMeasure)

/-- The strict Dobrushin random-scan quadratic enclosure descends to the
restricted vacuum-orthogonal operator without ambient-space side conditions. -/
theorem continuous_compact_oriented_randomScanVacuumOrthogonalL2_quadraticForm_bounds
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (f : C.VacuumOrthogonalL2) :
    0 ≤ inner ℝ (C.randomScanVacuumOrthogonalL2 D.edgeCard_pos f) f ∧
      inner ℝ (C.randomScanVacuumOrthogonalL2 D.edgeCard_pos f) f ≤
        continuousCompactOrientedDobrushinRandomScanRate C D.coefficient *
          ‖f‖ ^ 2 := by
  change
    0 ≤ inner ℝ
        (C.randomScanHeatBathL2 (f : Lp ℝ 2 C.gibbsMeasure))
        (f : Lp ℝ 2 C.gibbsMeasure) ∧
      inner ℝ
          (C.randomScanHeatBathL2 (f : Lp ℝ 2 C.gibbsMeasure))
          (f : Lp ℝ 2 C.gibbsMeasure) ≤
        continuousCompactOrientedDobrushinRandomScanRate C D.coefficient *
          ‖(f : Lp ℝ 2 C.gibbsMeasure)‖ ^ 2
  exact
    continuous_compact_oriented_randomScanDobrushin_quadraticForm_bounds_on_vacuumOrthogonal
      C D (f : Lp ℝ 2 C.gibbsMeasure) f.property

/-- The restricted heat-bath Hamiltonian has the explicit positive Dobrushin
lower bound and the edge-cardinality upper bound. -/
theorem continuous_compact_oriented_heatBathHamiltonianVacuumOrthogonalL2_quadraticForm_bounds
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (f : C.VacuumOrthogonalL2) :
    continuousCompactOrientedDobrushinHeatBathGap D.coefficient * ‖f‖ ^ 2 ≤
        inner ℝ (C.heatBathHamiltonianVacuumOrthogonalL2 f) f ∧
      inner ℝ (C.heatBathHamiltonianVacuumOrthogonalL2 f) f ≤
        (Fintype.card C.base.geometry.Edge : ℝ) * ‖f‖ ^ 2 := by
  change
    continuousCompactOrientedDobrushinHeatBathGap D.coefficient *
          ‖(f : Lp ℝ 2 C.gibbsMeasure)‖ ^ 2 ≤
        inner ℝ
          (C.heatBathHamiltonianL2 (f : Lp ℝ 2 C.gibbsMeasure))
          (f : Lp ℝ 2 C.gibbsMeasure) ∧
      inner ℝ
          (C.heatBathHamiltonianL2 (f : Lp ℝ 2 C.gibbsMeasure))
          (f : Lp ℝ 2 C.gibbsMeasure) ≤
        (Fintype.card C.base.geometry.Edge : ℝ) *
          ‖(f : Lp ℝ 2 C.gibbsMeasure)‖ ^ 2
  exact
    continuous_compact_oriented_randomScanDobrushinHamiltonianL2_quadraticForm_bounds_on_vacuumOrthogonal
      C D (f : Lp ℝ 2 C.gibbsMeasure) f.property

/-- The restricted heat-bath Hamiltonian has trivial kernel under a strict
Dobrushin random-scan certificate. -/
theorem continuous_compact_oriented_heatBathHamiltonianVacuumOrthogonalL2_eq_zero_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (f : C.VacuumOrthogonalL2) :
    C.heatBathHamiltonianVacuumOrthogonalL2 f = 0 ↔ f = 0 := by
  constructor
  · intro hZero
    have hAmbient :
        C.heatBathHamiltonianL2 (f : Lp ℝ 2 C.gibbsMeasure) = 0 :=
      congrArg
        (fun x : C.VacuumOrthogonalL2 =>
          (x : Lp ℝ 2 C.gibbsMeasure)) hZero
    have hfInner : inner ℝ C.gibbsVacuumL2
        (f : Lp ℝ 2 C.gibbsMeasure) = 0 :=
      (continuous_compact_oriented_mem_vacuumOrthogonalL2_iff
        C (f : Lp ℝ 2 C.gibbsMeasure)).mp f.property
    have hVacuumLine :=
      (continuous_compact_oriented_randomScanDobrushinHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum
        C D (f : Lp ℝ 2 C.gibbsMeasure)).mp hAmbient
    rw [hfInner, zero_smul] at hVacuumLine
    exact Subtype.ext hVacuumLine
  · rintro rfl
    exact map_zero _

/-- The restricted random-scan operator has no nonzero fixed vector under a
strict Dobrushin certificate. -/
theorem continuous_compact_oriented_randomScanVacuumOrthogonalL2_eq_self_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (f : C.VacuumOrthogonalL2) :
    C.randomScanVacuumOrthogonalL2 D.edgeCard_pos f = f ↔ f = 0 := by
  constructor
  · intro hFix
    have hAmbient :
        C.randomScanHeatBathL2 (f : Lp ℝ 2 C.gibbsMeasure) =
          (f : Lp ℝ 2 C.gibbsMeasure) :=
      congrArg
        (fun x : C.VacuumOrthogonalL2 =>
          (x : Lp ℝ 2 C.gibbsMeasure)) hFix
    exact Subtype.ext
      (continuous_compact_oriented_randomScanHeatBathL2_fixed_eq_zero_on_vacuumOrthogonal
        C D (f : Lp ℝ 2 C.gibbsMeasure) f.property hAmbient)
  · rintro rfl
    exact map_zero _

end

end MathlibAnalytic
end MGAP4D
