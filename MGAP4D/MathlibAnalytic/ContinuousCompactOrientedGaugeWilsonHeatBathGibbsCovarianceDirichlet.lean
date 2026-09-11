import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathGibbsCovarianceLocalVariation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathProjectionIdempotent
import Mathlib.Tactic

/-!
# One-link Gibbs covariance Dirichlet identity

For the exact compact Wilson one-link conditional expectation `P_e` and
fluctuation `Q_e = I - P_e`, self-adjointness and idempotence give the
projection identity

`Cov(F,G) - Cov(F,P_e G) = Cov(Q_e F, Q_e G)`.

Together with the local variation pairing already available for two
fluctuations, this yields

`|Cov(F,G) - Cov(F,P_e G)| ≤ δ_e(F) δ_e(G)`.

This is the linkwise Dirichlet carrier needed before averaging over links in a
random-scan defect and solving the resulting Poisson equation.  It introduces
no commutativity between different one-link updates and makes no spatial-decay,
continuum-clustering, or physical mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The bounded-continuous Feller representative of the one-link conditional
expectation inherits exact idempotence from the underlying heat-bath
projection. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_idempotent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkConditionalExpectationContinuousBCF target
        (C.singleLinkConditionalExpectationContinuousBCF target O) =
      C.singleLinkConditionalExpectationContinuousBCF target O := by
  ext A
  simp only [continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_apply]
  change
    C.singleLinkHeatBathProjection target
        (C.singleLinkHeatBathProjection target (fun B => O B)) A =
      C.singleLinkHeatBathProjection target (fun B => O B) A
  exact congrFun
    (continuous_compact_oriented_singleLinkHeatBathProjection_idempotent
      C target (fun B => O B)) A

/-- For one physical link, the covariance lost under conditional expectation on
the right is exactly the covariance pairing of the two corresponding
fluctuations. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_sub_singleLinkConditionalExpectation_eq_fluctuation_pairing
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (F G : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsCovarianceReal (fun A => F A) (fun A => G A) -
        C.gibbsCovarianceReal (fun A => F A)
          (fun A => C.singleLinkConditionalExpectationContinuousBCF target G A) =
      C.gibbsCovarianceReal
        (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target F A)
        (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target G A) := by
  let PF := C.singleLinkConditionalExpectationContinuousBCF target F
  let PG := C.singleLinkConditionalExpectationContinuousBCF target G
  have hPF_G :
      C.gibbsCovarianceReal (fun A => PF A) (fun A => G A) =
        C.gibbsCovarianceReal (fun A => F A) (fun A => PG A) := by
    simpa [PF, PG] using
      continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_gibbsCovariance_symm
        C target F G
  have hPF_PG :
      C.gibbsCovarianceReal (fun A => PF A) (fun A => PG A) =
        C.gibbsCovarianceReal (fun A => F A) (fun A => PG A) := by
    have h :=
      continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_gibbsCovariance_symm
        C target F PG
    rw [continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_idempotent
      C target G] at h
    simpa [PF, PG] using h
  symm
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuationContinuousBCF
  rw [continuous_compact_oriented_gibbsCovarianceReal_sub_left_bcf C F PF (G - PG),
    continuous_compact_oriented_gibbsCovarianceReal_sub_right_bcf C F G PG,
    continuous_compact_oriented_gibbsCovarianceReal_sub_right_bcf C PF G PG]
  rw [hPF_G, hPF_PG]
  ring

/-- Local two-sided variation control for the one-link covariance defect.  In
particular, the left/source observable enters through its variation at the same
physical link, not through a global norm. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_sub_singleLinkConditionalExpectation_abs_le_variation_mul_variation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (F G : BoundedContinuousFunction C.base.Configuration ℝ)
    (PF : ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (fun A => F A))
    (PG : ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (fun A => G A)) :
    |C.gibbsCovarianceReal (fun A => F A) (fun A => G A) -
        C.gibbsCovarianceReal (fun A => F A)
          (fun A => C.singleLinkConditionalExpectationContinuousBCF target G A)| ≤
      PF.variation target * PG.variation target := by
  rw [continuous_compact_oriented_gibbsCovarianceReal_sub_singleLinkConditionalExpectation_eq_fluctuation_pairing
    C target F G]
  exact
    continuous_compact_oriented_gibbsCovarianceReal_singleLinkHeatBathFluctuations_abs_le_variation_mul_variation
      C target F G PF PG

end

end MathlibAnalytic
end MGAP4D
