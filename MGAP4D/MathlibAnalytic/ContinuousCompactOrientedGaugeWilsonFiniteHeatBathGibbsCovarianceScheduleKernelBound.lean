import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonGibbsCovarianceLinkVariation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathGibbsCovariance
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathScheduleInfluenceKernel
import Mathlib.Tactic

/-!
# Finite heat-bath Gibbs covariance bound through the exact schedule kernel

The canonical finite-volume Gibbs covariance is invariant when a finite ordered
heat-bath schedule acts on the right and the left observable is constant on
each updated link fiber.  The resulting bounded-continuous observable carries
the recursively propagated centered variation profile.  Combining these facts
with the global telescoping covariance bound gives a direct estimate by the
total propagated variation.

The exact schedule influence-kernel representation then rewrites that estimate
as a finite double sum of the prescribed schedule kernel against the initial
centered variation profile.

This is still finite-volume heat-bath/Dobrushin algebra.  It does not identify
update count with Euclidean time and does not assert separated-support
exponential clustering, a continuum limit, or an OS Hamiltonian mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A finite ordered heat-bath schedule transfers the Gibbs covariance to the
propagated observable and hence bounds it by the total propagated centered
variation. -/
theorem
    continuous_compact_oriented_gibbsCovarianceReal_abs_le_norm_mul_sum_finiteHeatBathCenteredVariation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge)
    (F O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (hFiber : ∀ target ∈ targets,
      C.base.OffLinkFiberConstant target (fun A => F A)) :
    |C.gibbsCovarianceReal (fun A => F A) (fun A => O A)| ≤
      ‖F‖ * ∑ source : C.base.geometry.Edge,
        (P.finiteHeatBathCenteredVariationProfile D targets).variation source := by
  have hAction :
      (fun A : C.base.Configuration =>
        C.finiteSingleLinkHeatBathExpectationBCF targets O A) =
      (fun A : C.base.Configuration =>
        C.finiteSingleLinkHeatBathContinuousBCF targets O A) := by
    funext A
    exact
      (continuous_compact_oriented_finiteSingleLinkHeatBathContinuousBCF_eq_expectationBCF
        C targets O A).symm
  have hCov :=
    continuous_compact_oriented_gibbsCovarianceReal_finiteSingleLinkHeatBathExpectationBCF_eq_of_left_offLinkFiberConstant
      C targets F O hFiber
  calc
    |C.gibbsCovarianceReal (fun A => F A) (fun A => O A)| =
        |C.gibbsCovarianceReal (fun A => F A)
          (fun A => C.finiteSingleLinkHeatBathExpectationBCF targets O A)| := by
      rw [hCov]
    _ =
        |C.gibbsCovarianceReal (fun A => F A)
          (fun A => C.finiteSingleLinkHeatBathContinuousBCF targets O A)| := by
      rw [hAction]
    _ ≤ ‖F‖ * ∑ source : C.base.geometry.Edge,
          (P.finiteHeatBathCenteredVariationProfile D targets).variation source := by
      exact
        continuous_compact_oriented_gibbsCovarianceReal_abs_le_norm_mul_sum_centeredVariation
          C F (C.finiteSingleLinkHeatBathContinuousBCF targets O)
          (P.finiteHeatBathCenteredVariationProfile D targets)

/-- Expanding the propagated centered variation by the exact prescribed
schedule influence kernel gives a finite double-sum Gibbs covariance bound. -/
theorem
    continuous_compact_oriented_gibbsCovarianceReal_abs_le_norm_mul_sum_scheduleInfluenceKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge)
    (F O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (hFiber : ∀ target ∈ targets,
      C.base.OffLinkFiberConstant target (fun A => F A)) :
    |C.gibbsCovarianceReal (fun A => F A) (fun A => O A)| ≤
      ‖F‖ * ∑ source : C.base.geometry.Edge,
        ∑ initial : C.base.geometry.Edge,
          finiteHeatBathScheduleInfluenceKernel
              D.influence targets initial source * P.variation initial := by
  calc
    |C.gibbsCovarianceReal (fun A => F A) (fun A => O A)| ≤
        ‖F‖ * ∑ source : C.base.geometry.Edge,
          (P.finiteHeatBathCenteredVariationProfile D targets).variation source :=
      continuous_compact_oriented_gibbsCovarianceReal_abs_le_norm_mul_sum_finiteHeatBathCenteredVariation
        C targets F O P D hFiber
    _ = ‖F‖ * ∑ source : C.base.geometry.Edge,
          ∑ initial : C.base.geometry.Edge,
            finiteHeatBathScheduleInfluenceKernel
                D.influence targets initial source * P.variation initial := by
      congr 1
      apply Finset.sum_congr rfl
      intro source _
      exact
        continuous_compact_oriented_finiteHeatBathCenteredVariationProfile_variation_eq_sum_scheduleInfluenceKernel
          C O P D targets source

end

end MathlibAnalytic
end MGAP4D
