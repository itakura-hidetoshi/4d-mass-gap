import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenGibbsCovarianceSpatialGeometric
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteSupportVariation
import Mathlib.Tactic

/-!
# Periodic finite-support spatial covariance decay

The canonical finite-volume clustering theorem is intentionally formulated in
terms of proof-relevant link-variation profiles.  Local observables are more
naturally presented by a finite support and an exact support-dependence
statement.

This file combines the finite-support profile constructor with the periodic
`SU(N)` covariance theorem.  Thus bounded continuous observables supported on
plaquette-locally separated finite link sets satisfy the geometric covariance
bound directly, without exposing the auxiliary variation-profile structures to
the caller.

This is still a finite-volume theorem.  No continuum limit, infinite-volume
clustering, factorial-scale uniform Dobrushin threshold, or physical mass-gap
conclusion is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_finiteSupportCovarianceGeometric
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- Finite-support bounded continuous observables on the periodic compact
`SU(N)` Wilson system have geometrically decaying covariance whenever their
physical-link supports are plaquette-locally separated. -/
theorem periodicHypercubicEvenSpecialUnitary_gibbsCovarianceReal_abs_le_geometric_of_finiteSupportsSeparatedBy
    (H N D : ℕ) (hH : 0 < H) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (hThreshold : 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (F O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).base.Configuration ℝ)
    (hFDepends : ∀ A B, (∀ e, e ∈ T → A e = B e) → F A = F B)
    (hODepends : ∀ A B, (∀ e, e ∈ S → A e = B e) → O A = O B) :
    |(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).gibbsCovarianceReal
        (fun A => F A) (fun A => O A)| ≤
      ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
        (∑ e ∈ T, 2 * ‖F‖) * ∑ i ∈ S, 2 * ‖O‖ := by
  let C :=
    periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hBeta
  let PF :=
    ContinuousCompactOrientedGaugeWilsonLinkVariationBound.ofFiniteSupport
      F T hFDepends
  let P :=
    ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile.ofFiniteSupport
      O S hODepends
  have hPFSupport :
      ∀ e : PeriodicHypercubicEvenEdge H, e ∉ T → PF.variation e = 0 := by
    intro e he
    exact
      continuous_compact_oriented_ofFiniteSupport_variation_eq_zero_of_not_mem
        F T hFDepends he
  have hPSupport :
      ∀ e : PeriodicHypercubicEvenEdge H, e ∉ S → P.variation e = 0 := by
    intro e he
    exact
      continuous_compact_oriented_centeredOfFiniteSupport_variation_eq_zero_of_not_mem
        O S hODepends he
  have hSumF :
      (∑ e ∈ T, PF.variation e) = ∑ e ∈ T, 2 * ‖F‖ := by
    apply Finset.sum_congr rfl
    intro e he
    exact
      continuous_compact_oriented_ofFiniteSupport_variation_eq_two_mul_norm_of_mem
        F T hFDepends he
  have hSumO :
      (∑ e ∈ S, P.variation e) = ∑ e ∈ S, 2 * ‖O‖ := by
    apply Finset.sum_congr rfl
    intro e he
    exact
      continuous_compact_oriented_centeredOfFiniteSupport_variation_eq_two_mul_norm_of_mem
        O S hODepends he
  have hCov :=
    periodicHypercubicEvenSpecialUnitary_gibbsCovarianceReal_abs_le_geometric_of_supportsSeparatedBy
      H N D hH hN beta hBeta hThreshold S T hsep F O PF P hPFSupport hPSupport
  simpa only [hSumF, hSumO] using hCov

end

end MathlibAnalytic
end MGAP4D
