import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathHamiltonianKernelIdentification

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Sum of the exact one-link conditional-expectation projections on the
compact oriented Gibbs `L²` space. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.heatBathProjectionSumL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure :=
  ∑ target : C.base.geometry.Edge,
    C.singleLinkHeatBathProjectionL2 target

@[simp] theorem continuous_compact_oriented_heatBathProjectionSumL2_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathProjectionSumL2 f =
      ∑ target : C.base.geometry.Edge,
        C.singleLinkHeatBathProjectionL2 target f := by
  classical
  simp [ContinuousCompactOrientedGaugeWilsonSystem.heatBathProjectionSumL2]

/-- The native heat-bath Hamiltonian is the edge-cardinality multiple of the
identity minus the sum of the one-link conditional expectations. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_eq_card_smul_sub_projectionSum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 f =
      (Fintype.card C.base.geometry.Edge : ℝ) • f -
        C.heatBathProjectionSumL2 f := by
  classical
  rw [continuous_compact_oriented_heatBathHamiltonianL2_apply,
    continuous_compact_oriented_heatBathProjectionSumL2_apply]
  simp_rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [Finset.sum_const, Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℝ
    (Fintype.card C.base.geometry.Edge) f).symm

/-- Quadratic-form version of the random-scan defect identity. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm_eq_card_mul_sub_projectionSum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.heatBathHamiltonianL2 f) f =
      (Fintype.card C.base.geometry.Edge : ℝ) * ‖f‖ ^ 2 -
        inner ℝ (C.heatBathProjectionSumL2 f) f := by
  rw [continuous_compact_oriented_heatBathHamiltonianL2_eq_card_smul_sub_projectionSum,
    inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- Vacuum centering does not change the native compact heat-bath Hamiltonian. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_vacuumCentered
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 (C.vacuumCenteredL2 f) =
      C.heatBathHamiltonianL2 f := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2
  rw [map_sub, map_smul,
    continuous_compact_oriented_heatBathHamiltonianL2_vacuum,
    smul_zero, sub_zero]

/-- Vacuum centering also leaves the heat-bath quadratic form unchanged. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_vacuumCentered_quadraticForm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ
        (C.heatBathHamiltonianL2 (C.vacuumCenteredL2 f))
        (C.vacuumCenteredL2 f) =
      inner ℝ (C.heatBathHamiltonianL2 f) f := by
  rw [continuous_compact_oriented_heatBathHamiltonianL2_vacuumCentered]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2
  rw [inner_sub_right, real_inner_smul_right]
  have hVacuumOrthogonal :
      inner ℝ (C.heatBathHamiltonianL2 f) C.gibbsVacuumL2 = 0 := by
    calc
      inner ℝ (C.heatBathHamiltonianL2 f) C.gibbsVacuumL2 =
          inner ℝ f
            (C.heatBathHamiltonianL2 C.gibbsVacuumL2) :=
        continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
          C f C.gibbsVacuumL2
      _ = 0 := by
        rw [continuous_compact_oriented_heatBathHamiltonianL2_vacuum,
          inner_zero_right]
  rw [hVacuumOrthogonal, mul_zero, sub_zero]

/-- The unnormalized continuous-time heat-bath gap associated with a strict
Dobrushin coefficient. -/
def continuousCompactOrientedDobrushinHeatBathGap
    (coefficient : ℝ) : ℝ :=
  1 - coefficient

/-- Analytic certificate separating the strict Dobrushin coefficient from the
centered `L²` Rayleigh comparison.  The latter is the genuine analytic input;
a total-variation row-sum bound alone is not silently promoted to an `L²`
Poincaré theorem. -/
structure ContinuousCompactOrientedGaugeWilsonDobrushinRayleighCertificate
    (C : ContinuousCompactOrientedGaugeWilsonSystem) where
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  coefficient_lt_one : coefficient < 1
  centered_projectionSum_rayleigh_le :
    ∀ f : Lp ℝ 2 C.gibbsMeasure,
      inner ℝ
          (C.heatBathProjectionSumL2 (C.vacuumCenteredL2 f))
          (C.vacuumCenteredL2 f) ≤
        ((Fintype.card C.base.geometry.Edge : ℝ) -
          continuousCompactOrientedDobrushinHeatBathGap coefficient) *
            ‖C.vacuumCenteredL2 f‖ ^ 2

/-- Strict Dobrushin uniqueness gives a positive compact heat-bath gap. -/
theorem continuous_compact_oriented_dobrushinHeatBathGap_pos
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRayleighCertificate C) :
    0 < continuousCompactOrientedDobrushinHeatBathGap D.coefficient := by
  unfold continuousCompactOrientedDobrushinHeatBathGap
  exact sub_pos.mpr D.coefficient_lt_one

/-- A centered Dobrushin Rayleigh comparison yields the native compact
heat-bath Poincaré inequality with coefficient `1 - alpha`. -/
theorem continuous_compact_oriented_dobrushinHeatBathPoincareL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRayleighCertificate C) :
    C.HeatBathPoincareL2
      (continuousCompactOrientedDobrushinHeatBathGap D.coefficient) := by
  intro f
  let q : Lp ℝ 2 C.gibbsMeasure := C.vacuumCenteredL2 f
  have hRayleigh := D.centered_projectionSum_rayleigh_le f
  have hDefect :=
    continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm_eq_card_mul_sub_projectionSum
      C q
  have hCentered :=
    continuous_compact_oriented_heatBathHamiltonianL2_vacuumCentered_quadraticForm
      C f
  change
    continuousCompactOrientedDobrushinHeatBathGap D.coefficient * ‖q‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 f) f
  rw [← hCentered]
  change
    continuousCompactOrientedDobrushinHeatBathGap D.coefficient * ‖q‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 q) q
  rw [hDefect]
  change
    continuousCompactOrientedDobrushinHeatBathGap D.coefficient * ‖q‖ ^ 2 ≤
      (Fintype.card C.base.geometry.Edge : ℝ) * ‖q‖ ^ 2 -
        inner ℝ (C.heatBathProjectionSumL2 q) q
  change
    inner ℝ (C.heatBathProjectionSumL2 q) q ≤
      ((Fintype.card C.base.geometry.Edge : ℝ) -
        continuousCompactOrientedDobrushinHeatBathGap D.coefficient) *
          ‖q‖ ^ 2 at hRayleigh
  nlinarith [sq_nonneg ‖q‖]

/-- The same certificate gives coercivity on the Gibbs-vacuum orthogonal
sector with the explicit positive Dobrushin gap. -/
theorem continuous_compact_oriented_dobrushinHamiltonianL2_gap_on_vacuumOrthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRayleighCertificate C)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hf : inner ℝ C.gibbsVacuumL2 f = 0) :
    continuousCompactOrientedDobrushinHeatBathGap D.coefficient * ‖f‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 f) f :=
  continuous_compact_oriented_heatBathHamiltonianL2_gap_on_vacuumOrthogonal
    C _
    (continuous_compact_oriented_dobrushinHeatBathPoincareL2 C D)
    f hf

/-- Under a strict Dobrushin Rayleigh certificate, the native compact
heat-bath Hamiltonian has exactly the Gibbs-vacuum line as its zero eigenspace. -/
theorem continuous_compact_oriented_dobrushinHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRayleighCertificate C)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 f = 0 ↔
      f = inner ℝ C.gibbsVacuumL2 f • C.gibbsVacuumL2 :=
  continuous_compact_oriented_heatBathHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum
    C _
    (continuous_compact_oriented_dobrushinHeatBathGap_pos D)
    (continuous_compact_oriented_dobrushinHeatBathPoincareL2 C D)
    f

end

end MathlibAnalytic
end MGAP4D
