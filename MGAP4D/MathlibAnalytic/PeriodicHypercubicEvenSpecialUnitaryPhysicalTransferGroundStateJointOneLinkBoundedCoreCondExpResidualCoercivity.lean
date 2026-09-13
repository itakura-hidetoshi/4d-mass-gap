import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkBoundedCoreCondExpResidual
import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- Once an outer-context representative of the genuine one-link `condExpL2`
is fixed, the bounded-core centered residual functional is exactly the squared
real `L²` norm of the genuine conditional-expectation residual.

The proof only transports almost-everywhere representatives under the genuine
ground-state joint law.  It does not take pointwise sections of an arbitrary
`L²` quotient representative and makes no RCD or conditional-law claim. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional_eq_condExpL2_residual_norm_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (C :
      PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
        H N target → ℝ)
    (hC : StronglyMeasurable C)
    (hCJoint :
      (fun z =>
        C (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
          H N target z)) =ᵐ[
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta]
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta F hF bound hbound) :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional
        H N hN beta hbeta target F C =
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  let μJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
      H N hN beta hbeta F hF bound hbound
  let q :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta target f
  let r :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta :=
    f - q
  have hf : (fun z => f z) =ᵐ[μJ] F := by
    simpa [f, μJ] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
        H N hN beta hbeta F hF bound hbound)
  have hq :
      (fun z =>
        C (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
          H N target z)) =ᵐ[μJ] (fun z => q z) := by
    simpa [q, f, μJ] using hCJoint
  have hr :
      (fun z => r z) =ᵐ[μJ]
        (fun z =>
          F z -
            C (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
              H N target z)) := by
    filter_upwards [Lp.coeFn_sub f q, hf, hq] with z hsub hfz hqz
    calc
      r z = f z - q z := by simpa [r] using hsub
      _ = F z -
          C (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
            H N target z) := by
        rw [hfz, ← hqz]
  have hLin :
      (∫⁻ z,
        ENNReal.ofReal
          ((F z -
              C (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                H N target z)) ^ 2) ∂μJ) =
        ∫⁻ z, ENNReal.ofReal ((r z) ^ 2) ∂μJ := by
    apply lintegral_congr_ae
    filter_upwards [hr] with z hz
    rw [← hz]
  have hSq : Integrable (fun z => (r z) ^ 2) μJ := by
    simpa only [Pi.pow_apply] using (Lp.memLp r).integrable_sq
  have hNormIntegral :
      (∫ z, (r z) ^ 2 ∂μJ) = ‖r‖ ^ 2 := by
    calc
      (∫ z, (r z) ^ 2 ∂μJ) = ∫ z, ‖r z‖ ^ 2 ∂μJ := by
        apply integral_congr_ae
        filter_upwards with z
        simp [Real.norm_eq_abs, sq_abs]
      _ = ‖r‖ ^ 2 := (realL2_norm_sq_eq_integral_norm_sq r).symm
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional
        H N hN beta hbeta target F C =
      ∫⁻ z,
        ENNReal.ofReal
          ((F z -
              C (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                H N target z)) ^ 2) ∂μJ := by
      simpa [μJ] using
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional_eq_joint_lintegral
          H N hN beta hbeta target F hF C hC)
    _ = ∫⁻ z, ENNReal.ofReal ((r z) ^ 2) ∂μJ := hLin
    _ = ENNReal.ofReal (∫ z, (r z) ^ 2 ∂μJ) :=
      (ofReal_integral_eq_lintegral_ofReal hSq
        (ae_of_all μJ fun z => sq_nonneg (r z))).symm
    _ = ENNReal.ofReal (‖r‖ ^ 2) := by rw [hNormIntegral]
    _ = ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
      rfl

/-- Genuine bounded-core one-link conditional-expectation residual coercivity.
The exact sharp coefficient `exp (-16 * beta)` is already carried by the
left-hand sharp Haar variance functional.  This closes the bounded concrete
core before any density/truncation extension to arbitrary joint `L²`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreSharpHaarVarianceFunctional_le_condExpL2_residual_norm_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreSharpHaarVarianceFunctional
        H N hN beta hbeta target F ≤
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  obtain ⟨C, hC, hCJoint, _hCPair, hineq⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCore_exists_condExpOuter_centeredResidual
      H N hN beta hbeta target F hF bound hbound
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreSharpHaarVarianceFunctional
        H N hN beta hbeta target F ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional
        H N hN beta hbeta target F C := hineq
    _ = ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound)‖ ^ 2) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional_eq_condExpL2_residual_norm_sq
        H N hN beta hbeta target F hF bound hbound C hC hCJoint

end

end MathlibAnalytic
end MGAP4D
