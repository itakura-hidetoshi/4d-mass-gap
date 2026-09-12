import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinMatrixL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Replace the coefficient of a compact Wilson Dobrushin matrix/random-scan
certificate by any larger strict coefficient bound.

The matrix certificate first gives the projection-sum Rayleigh inequality with
its native coefficient `D.coefficient`.  If

`D.coefficient ≤ coefficientBound < 1`,

the same inequality remains valid with the weaker common gap
`1 - coefficientBound`.  This is the generic volume-uniformization step needed
when different finite lattices carry different Dobrushin coefficients. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate.toCoefficientBoundRayleighCertificate
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate C)
    (coefficientBound : ℝ)
    (coefficientBound_nonneg : 0 ≤ coefficientBound)
    (coefficientBound_lt_one : coefficientBound < 1)
    (coefficient_le_bound : D.coefficient ≤ coefficientBound) :
    ContinuousCompactOrientedGaugeWilsonDobrushinRayleighCertificate C := by
  let R : ContinuousCompactOrientedGaugeWilsonDobrushinRayleighCertificate C :=
    D.toRandomScanCertificate.toProjectionSumCertificate
  refine
    { coefficient := coefficientBound
      coefficient_nonneg := coefficientBound_nonneg
      coefficient_lt_one := coefficientBound_lt_one
      centered_projectionSum_rayleigh_le := ?_ }
  intro f
  let q : Lp ℝ 2 C.gibbsMeasure := C.vacuumCenteredL2 f
  have hLocal := R.centered_projectionSum_rayleigh_le f
  have hFactor :
      (Fintype.card C.base.geometry.Edge : ℝ) -
          continuousCompactOrientedDobrushinHeatBathGap D.coefficient ≤
        (Fintype.card C.base.geometry.Edge : ℝ) -
          continuousCompactOrientedDobrushinHeatBathGap coefficientBound := by
    unfold continuousCompactOrientedDobrushinHeatBathGap
    linarith
  have hScaled :=
    mul_le_mul_of_nonneg_right hFactor (sq_nonneg ‖q‖)
  change
    inner ℝ (C.heatBathProjectionSumL2 q) q ≤
      ((Fintype.card C.base.geometry.Edge : ℝ) -
        continuousCompactOrientedDobrushinHeatBathGap coefficientBound) *
          ‖q‖ ^ 2
  change
    inner ℝ (C.heatBathProjectionSumL2 q) q ≤
      ((Fintype.card C.base.geometry.Edge : ℝ) -
        continuousCompactOrientedDobrushinHeatBathGap D.coefficient) *
          ‖q‖ ^ 2 at hLocal
  exact hLocal.trans hScaled

/-- A scale-wise matrix/random-scan certificate controlled by a common strict
coefficient bound yields the native compact Wilson heat-bath Poincaré
inequality with the common gap `1 - coefficientBound`. -/
theorem continuous_compact_oriented_dobrushinCoefficientBoundHeatBathPoincareL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate C)
    (coefficientBound : ℝ)
    (coefficientBound_nonneg : 0 ≤ coefficientBound)
    (coefficientBound_lt_one : coefficientBound < 1)
    (coefficient_le_bound : D.coefficient ≤ coefficientBound) :
    C.HeatBathPoincareL2
      (continuousCompactOrientedDobrushinHeatBathGap coefficientBound) :=
  continuous_compact_oriented_dobrushinHeatBathPoincareL2 C
    (D.toCoefficientBoundRayleighCertificate coefficientBound
      coefficientBound_nonneg coefficientBound_lt_one coefficient_le_bound)

/-- The same common coefficient bound gives Gibbs-Hamiltonian coercivity on
the vacuum-orthogonal sector. -/
theorem continuous_compact_oriented_dobrushinCoefficientBoundHamiltonianL2_gap_on_vacuumOrthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate C)
    (coefficientBound : ℝ)
    (coefficientBound_nonneg : 0 ≤ coefficientBound)
    (coefficientBound_lt_one : coefficientBound < 1)
    (coefficient_le_bound : D.coefficient ≤ coefficientBound)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hf : inner ℝ C.gibbsVacuumL2 f = 0) :
    continuousCompactOrientedDobrushinHeatBathGap coefficientBound * ‖f‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 f) f :=
  continuous_compact_oriented_dobrushinHamiltonianL2_gap_on_vacuumOrthogonal
    C
    (D.toCoefficientBoundRayleighCertificate coefficientBound
      coefficientBound_nonneg coefficientBound_lt_one coefficient_le_bound)
    f hf

/-- Under a common strict coefficient bound, the native compact Gibbs
heat-bath Hamiltonian still has exactly the normalized Gibbs-vacuum line as
its kernel. -/
theorem continuous_compact_oriented_dobrushinCoefficientBoundHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate C)
    (coefficientBound : ℝ)
    (coefficientBound_nonneg : 0 ≤ coefficientBound)
    (coefficientBound_lt_one : coefficientBound < 1)
    (coefficient_le_bound : D.coefficient ≤ coefficientBound)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 f = 0 ↔
      f = inner ℝ C.gibbsVacuumL2 f • C.gibbsVacuumL2 :=
  continuous_compact_oriented_dobrushinHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum
    C
    (D.toCoefficientBoundRayleighCertificate coefficientBound
      coefficientBound_nonneg coefficientBound_lt_one coefficient_le_bound)
    f

end

end MathlibAnalytic
end MGAP4D
