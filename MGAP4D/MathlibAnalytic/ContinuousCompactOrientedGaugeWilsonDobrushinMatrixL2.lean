import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Dobrushin influence data for exact compact Haar one-link conditional laws.
The conditional-law comparison is stated in the bounded-test dual form of
total variation, avoiding any dependence on a separate total-variation metric
API while preserving the standard factor-two normalization. -/
structure ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData
    (C : ContinuousCompactOrientedGaugeWilsonSystem) where
  influence : C.base.geometry.Edge → C.base.geometry.Edge → ℝ
  influence_nonneg :
    ∀ target source : C.base.geometry.Edge,
      0 ≤ influence target source
  influence_diagonal_zero :
    ∀ target : C.base.geometry.Edge,
      influence target target = 0
  conditionalIntegral_difference_abs_le :
    ∀ (target source : C.base.geometry.Edge)
      (A B : C.base.Configuration),
      C.base.AgreeOffLink A B source →
      ∀ (phi : C.base.Gauge → ℝ),
        StronglyMeasurable phi →
        (∀ g : C.base.Gauge, |phi g| ≤ 1) →
        |(∫ g, phi g ∂C.singleLinkConditionalMeasure A target) -
          (∫ g, phi g ∂C.singleLinkConditionalMeasure B target)| ≤
            2 * influence target source
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  rowSum_le_coefficient :
    ∀ target : C.base.geometry.Edge,
      ∑ source : C.base.geometry.Edge, influence target source ≤ coefficient
  coefficient_lt_one : coefficient < 1

/-- Exact compact Haar conditional laws agree whenever the two backgrounds
agree away from the resampled link. -/
theorem continuous_compact_oriented_conditionalIntegral_eq_of_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A B : C.base.Configuration)
    (hAgree : C.base.AgreeOffLink A B target)
    (phi : C.base.Gauge → ℝ) :
    (∫ g, phi g ∂C.singleLinkConditionalMeasure A target) =
      ∫ g, phi g ∂C.singleLinkConditionalMeasure B target := by
  rw [continuous_compact_oriented_singleLinkConditionalMeasure_eq_of_agreeOffLink
    C A B target hAgree]

/-- The diagonal bounded-test conditional-law difference is exactly the
prescribed zero self-influence. -/
theorem continuous_compact_oriented_dobrushin_diagonal_conditionalIntegral_difference_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (target : C.base.geometry.Edge)
    (A B : C.base.Configuration)
    (hAgree : C.base.AgreeOffLink A B target)
    (phi : C.base.Gauge → ℝ) :
    |(∫ g, phi g ∂C.singleLinkConditionalMeasure A target) -
      (∫ g, phi g ∂C.singleLinkConditionalMeasure B target)| =
        2 * D.influence target target := by
  rw [continuous_compact_oriented_conditionalIntegral_eq_of_agreeOffLink
    C target A B hAgree phi,
    D.influence_diagonal_zero]
  norm_num

/-- Every row sum of a strict compact Dobrushin matrix is below one. -/
theorem continuous_compact_oriented_dobrushin_rowSum_lt_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (target : C.base.geometry.Edge) :
    (∑ source : C.base.geometry.Edge,
      D.influence target source) < 1 :=
  lt_of_le_of_lt (D.rowSum_le_coefficient target) D.coefficient_lt_one

/-- Strict matrix data have a positive unnormalized heat-bath gap. -/
theorem continuous_compact_oriented_dobrushinMatrix_heatBathGap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C) :
    0 < continuousCompactOrientedDobrushinHeatBathGap D.coefficient := by
  unfold continuousCompactOrientedDobrushinHeatBathGap
  exact sub_pos.mpr D.coefficient_lt_one

/-- A compact conditional-law Dobrushin matrix together with the genuine
centered random-scan `L²` comparison.  The matrix controls local conditional
laws; the last field is kept explicit because passing from bounded-test
variation to a global Hilbert-space Rayleigh estimate is the remaining
analytic theorem, not a definitional consequence. -/
structure
    ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    extends ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C where
  edgeCard_pos : 0 < Fintype.card C.base.geometry.Edge
  centered_randomScan_rayleigh_le :
    ∀ f : Lp ℝ 2 C.gibbsMeasure,
      inner ℝ
          (C.randomScanHeatBathL2 (C.vacuumCenteredL2 f))
          (C.vacuumCenteredL2 f) ≤
        continuousCompactOrientedDobrushinRandomScanRate C coefficient *
          ‖C.vacuumCenteredL2 f‖ ^ 2

/-- Forgetting the bounded-test matrix layer produces the exact random-scan
Rayleigh certificate required by the compact Poincaré bridge. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate.toRandomScanCertificate
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate C) :
    ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C :=
  { coefficient := D.coefficient
    coefficient_nonneg := D.coefficient_nonneg
    coefficient_lt_one := D.coefficient_lt_one
    edgeCard_pos := D.edgeCard_pos
    centered_randomScan_rayleigh_le := D.centered_randomScan_rayleigh_le }

/-- A compact conditional-law Dobrushin matrix with its centered `L²`
comparison yields the native heat-bath Poincaré inequality. -/
theorem continuous_compact_oriented_dobrushinMatrixHeatBathPoincareL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate C) :
    C.HeatBathPoincareL2
      (continuousCompactOrientedDobrushinHeatBathGap D.coefficient) :=
  continuous_compact_oriented_randomScanDobrushinHeatBathPoincareL2 C
    D.toRandomScanCertificate

/-- The matrix-plus-Rayleigh certificate gives coercivity on the
Gibbs-vacuum orthogonal sector. -/
theorem continuous_compact_oriented_dobrushinMatrixHamiltonianL2_gap_on_vacuumOrthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate C)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hf : inner ℝ C.gibbsVacuumL2 f = 0) :
    continuousCompactOrientedDobrushinHeatBathGap D.coefficient * ‖f‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 f) f :=
  continuous_compact_oriented_randomScanDobrushinHamiltonianL2_gap_on_vacuumOrthogonal
    C D.toRandomScanCertificate f hf

/-- Under compact matrix-plus-Rayleigh Dobrushin data, the native heat-bath
Hamiltonian has precisely the normalized Gibbs-vacuum line as kernel. -/
theorem continuous_compact_oriented_dobrushinMatrixHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate C)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 f = 0 ↔
      f = inner ℝ C.gibbsVacuumL2 f • C.gibbsVacuumL2 :=
  continuous_compact_oriented_randomScanDobrushinHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum
    C D.toRandomScanCertificate f

end

end MathlibAnalytic
end MGAP4D
