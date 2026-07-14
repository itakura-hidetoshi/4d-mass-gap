import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathFluctuationL2Identification
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathPairing
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonHeatBathHamiltonianL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

private theorem continuous_compact_oriented_bcf_abs_le_norm
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    |O A| ≤ ‖O‖ := by
  simpa [Real.norm_eq_abs] using O.norm_coe_le_norm A

/-- Canonical Gibbs `L²` representative of a bounded continuous observable. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Lp ℝ 2 C.gibbsMeasure :=
  (continuous_compact_oriented_memLp_two_of_uniform_bound
    C O O.continuous.stronglyMeasurable ‖O‖ (norm_nonneg _)
    (continuous_compact_oriented_bcf_abs_le_norm O)).toLp O

/-- Exact one-link conditional variance of a bounded continuous observable,
computed in the native compact Haar conditional law. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalVarianceBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) : ℝ :=
  ∫ g : C.base.Gauge,
    (O (C.base.replaceLink A target g) -
      C.singleLinkHeatBathProjection target O A) ^ 2
      ∂C.singleLinkConditionalMeasure A target

/-- Fiber conditional variance is nonnegative. -/
theorem continuous_compact_oriented_singleLinkConditionalVarianceBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    0 ≤ C.singleLinkConditionalVarianceBCF target O A := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalVarianceBCF
  exact integral_nonneg fun _ => sq_nonneg _

/-- The fiber conditional variance is the exact heat-bath projection of the
squared concrete one-link fluctuation. -/
theorem continuous_compact_oriented_singleLinkConditionalVarianceBCF_eq_projection_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.singleLinkConditionalVarianceBCF target O A =
      C.singleLinkHeatBathProjection target
        (fun B => (C.singleLinkHeatBathFluctuation target O B) ^ 2) A := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalVarianceBCF
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjection
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
  apply integral_congr_ae
  filter_upwards [] with g
  have hProjection :
      C.singleLinkHeatBathProjection target O
          (C.base.replaceLink A target g) =
        C.singleLinkHeatBathProjection target O A := by
    change C.singleLinkConditionalExpectation O
        (C.base.replaceLink A target g) target =
      C.singleLinkConditionalExpectation O A target
    exact continuous_compact_oriented_singleLinkConditionalExpectation_replaceLink
      C O A target g
  simp only [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuation,
    Pi.sub_apply]
  rw [hProjection]
  rfl

/-- Gibbs stationarity of a one-link heat-bath projection, on strongly
measurable uniformly bounded real observables. -/
theorem continuous_compact_oriented_integral_singleLinkHeatBathProjection_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ A, |f A| ≤ M) :
    ∫ A, C.singleLinkHeatBathProjection target f A ∂C.gibbsMeasure =
      ∫ A, f A ∂C.gibbsMeasure := by
  have hPair :=
    continuous_compact_oriented_singleLinkHeatBathProjection_gibbsPairing_symm
      C target f (fun _ : C.base.Configuration => (1 : ℝ))
      hf stronglyMeasurable_const M 1 hM0 (by norm_num) hM (by simp)
  have hConst :
      C.singleLinkHeatBathProjection target
          (fun _ : C.base.Configuration => (1 : ℝ)) =
        fun _ : C.base.Configuration => (1 : ℝ) := by
    apply continuous_compact_oriented_singleLinkHeatBathProjection_fixes
    intro A B hAgree
    rfl
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.gibbsPairingReal, hConst]
    using hPair

/-- Gibbs average of the native fiber conditional variance is exactly the
squared Gibbs `L²` norm of the one-link projection defect. -/
theorem continuous_compact_oriented_integral_singleLinkConditionalVarianceBCF_eq_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    ∫ A, C.singleLinkConditionalVarianceBCF target O A ∂C.gibbsMeasure =
      ‖C.singleLinkHeatBathFluctuationL2 target
          (C.gibbsL2RepresentativeBCF O)‖ ^ 2 := by
  let M : ℝ := ‖O‖
  let q : C.base.Configuration → ℝ :=
    C.singleLinkHeatBathFluctuation target O
  let qsq : C.base.Configuration → ℝ := fun A => q A ^ 2
  have hOStrong : StronglyMeasurable
      (O : C.base.Configuration → ℝ) := O.continuous.stronglyMeasurable
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact norm_nonneg _
  have hOBound : ∀ A, |O A| ≤ M := by
    intro A
    exact continuous_compact_oriented_bcf_abs_le_norm O A
  have hQStrong : StronglyMeasurable q := by
    dsimp [q]
    exact
      continuous_compact_oriented_singleLinkHeatBathFluctuation_stronglyMeasurable
        C target O hOStrong
  have hQBound : ∀ A, |q A| ≤ 2 * M := by
    intro A
    dsimp [q]
    exact
      continuous_compact_oriented_singleLinkHeatBathFluctuation_abs_le
        C target O hOStrong M hM0 hOBound A
  have hQsqStrong : StronglyMeasurable qsq := by
    dsimp [qsq]
    simpa [pow_two] using hQStrong.mul hQStrong
  have hTwoM0 : 0 ≤ 2 * M := mul_nonneg (by norm_num) hM0
  have hQsqBound : ∀ A, |qsq A| ≤ (2 * M) ^ 2 := by
    intro A
    have hAbs0 : 0 ≤ |q A| := abs_nonneg _
    have hProd :
        0 ≤ (2 * M - |q A|) * (2 * M + |q A|) :=
      mul_nonneg (sub_nonneg.mpr (hQBound A)) (add_nonneg hTwoM0 hAbs0)
    dsimp [qsq]
    rw [abs_pow]
    nlinarith
  let hQLp : MemLp q 2 C.gibbsMeasure :=
    continuous_compact_oriented_memLp_two_of_uniform_bound
      C q hQStrong (2 * M) hTwoM0 hQBound
  have hFluctuation :=
    continuous_compact_oriented_singleLinkHeatBathFluctuationL2_toLp_eq
      C target O hOStrong M hM0 hOBound
  calc
    ∫ A, C.singleLinkConditionalVarianceBCF target O A ∂C.gibbsMeasure =
        ∫ A, C.singleLinkHeatBathProjection target qsq A ∂C.gibbsMeasure := by
      apply integral_congr_ae
      filter_upwards [] with A
      simpa [qsq, q] using
        continuous_compact_oriented_singleLinkConditionalVarianceBCF_eq_projection_sq
          C target O A
    _ = ∫ A, qsq A ∂C.gibbsMeasure :=
      continuous_compact_oriented_integral_singleLinkHeatBathProjection_eq
        C target qsq hQsqStrong ((2 * M) ^ 2) (sq_nonneg _) hQsqBound
    _ = inner ℝ (hQLp.toLp q) (hQLp.toLp q) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hQLp.coeFn_toLp] with A hA
      simp [qsq, hA, pow_two]
    _ = ‖hQLp.toLp q‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = ‖C.singleLinkHeatBathFluctuationL2 target
          (C.gibbsL2RepresentativeBCF O)‖ ^ 2 := by
      have hRep :
          C.gibbsL2RepresentativeBCF O =
            (continuous_compact_oriented_memLp_two_of_uniform_bound
              C O hOStrong M hM0 hOBound).toLp O := by
        rfl
      rw [hRep, hFluctuation]

/-- On the bounded-continuous observable core, the sum of native conditional
variances is exactly the quadratic form of the compact-Haar heat-bath
Hamiltonian. -/
theorem continuous_compact_oriented_sum_integral_singleLinkConditionalVarianceBCF_eq_hamiltonian
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∑ target : C.base.geometry.Edge,
      ∫ A, C.singleLinkConditionalVarianceBCF target O A ∂C.gibbsMeasure) =
      inner ℝ
        (C.heatBathHamiltonianL2 (C.gibbsL2RepresentativeBCF O))
        (C.gibbsL2RepresentativeBCF O) := by
  rw [continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm]
  apply Finset.sum_congr rfl
  intro target _
  exact
    continuous_compact_oriented_integral_singleLinkConditionalVarianceBCF_eq_norm_sq
      C target O

end

end MathlibAnalytic
end MGAP4D
