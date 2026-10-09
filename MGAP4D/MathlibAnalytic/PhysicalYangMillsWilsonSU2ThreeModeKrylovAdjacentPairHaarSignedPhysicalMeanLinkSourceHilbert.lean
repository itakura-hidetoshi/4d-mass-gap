import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSignedPhysicalMeanLinkSourceL1
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-!
# P4-Q2-B: physical signed mean one-link Hilbert source bound

The verified #5329 original signed source-integral bound is strengthened
using the actual probability Haar law's canonical L2-to-L1 inequality.

  |M_f(B[e←g]) - M_f(B)|
    ≤ λ_beta⁻¹ * ((exp(8 beta)^2 - 1) / Ω_beta(B)) * ‖f‖_L2(Haar).

Here M_f is the ORIGINAL signed normalized SU(2) transfer mean, not a
positive approximation. The fine-right Krylov input is the actual
L² sum of beta(n+1)-evolved factors, with frozen beta(n) in the
transfer and continuous vacuum. The coefficient is independent of
the link cardinality but inverse vacuum and transfer norm still have
possible finite-volume dependence; this is NOT a uniform Q2-C bound.

No Dobrushin, sorry/admit or new axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4SignedHilbertHaarProbability (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

/-- Exact Haar probability L² → L¹ domination for a general signed
real Hilbert input. This is the mathlib comparison of Lᵖ exponents,
not a pointwise absolute-value bound assumed for the source. -/
theorem physicalHaarSignedSource_integral_norm_le_L2
    (H N : ℕ)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    (∫ A, ‖f A‖
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) ≤
      ‖f‖ := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hLp :
      eLpNorm (fun A => f A) (1 : ENNReal) μ ≤
        eLpNorm (fun A => f A) (2 : ENNReal) μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (μ := μ)
      (f := fun A => f A) (by norm_num)
  have hTop :
      eLpNorm (fun A => f A) (2 : ENNReal) μ ≠ ⊤ := by
    simpa [μ] using (Lp.eLpNorm_ne_top f)
  have hReal := ENNReal.toReal_mono hTop hLp
  calc
    (∫ A, ‖f A‖ ∂μ) =
        lpNorm (fun A => f A) 1 μ :=
      (lpNorm_one_eq_integral_norm (Lp.aestronglyMeasurable f)).symm
    _ = (eLpNorm (fun A => f A) (1 : ENNReal) μ).toReal :=
      (toReal_eLpNorm).symm
    _ ≤ (eLpNorm (fun A => f A) (2 : ENNReal) μ).toReal := hReal
    _ = ‖f‖ := (Lp.norm_def f).symm

/-- Actual normalized frozen Wilson transfer mean of any signed
physical Haar-L² source has a one-link variation bounded by the
Hilbert norm of precisely that original source. -/
theorem normalizedPhysicalOneSlabVacuumReceiverBCF_rightLinkDifference_abs_le_signedSourceL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f
        (Function.update B e g) -
      normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f B| ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        (((Real.exp (8 * beta)) ^ 2 - 1) /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta B) *
        ‖(f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ := by
  have hBeta : (0 : ℝ) ≤ 8 * beta := by nlinarith [hbeta]
  have hR : 1 ≤ Real.exp (8 * beta) := by
    simpa using
      (Real.exp_le_exp.mpr hBeta :
        Real.exp (0 : ℝ) ≤ Real.exp (8 * beta))
  have hD : 0 ≤ (Real.exp (8 * beta)) ^ 2 - 1 := by
    nlinarith [hR]
  have hOmega :
      0 <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta B
  have hlambda :
      0 <
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ :=
    inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta)
  have hc :
      0 ≤
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        (((Real.exp (8 * beta)) ^ 2 - 1) /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta B) :=
    mul_nonneg hlambda.le (div_nonneg hD hOmega.le)
  have hBase :=
    normalizedPhysicalOneSlabVacuumReceiverBCF_rightLinkDifference_abs_le_signedSourceL1
      H N hN beta hbeta f B e g
  have hHilbert :=
    physicalHaarSignedSource_integral_norm_le_L2 H N
      (f : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  exact hBase.trans (mul_le_mul_of_nonneg_left hHilbert hc)

/-- The genuine *uncentered* fine-right Krylov Hilbert sum remains intact.
Its orbit parameter is beta(n+1), while the physical transfer
and its one-link Wilson/vacuum estimate use beta(n). -/
theorem fineRightKrylovOriginalVacuumMeanJointBCF_rightLinkDifference_abs_le_signedSourceL2
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
        (halfExtent (n + 1)) 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
        (halfExtent (n + 1)) 2)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    |fineRightKrylovOriginalVacuumMeanJointBCF
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a (z.1, Function.update z.2 e g) -
      fineRightKrylovOriginalVacuumMeanJointBCF
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a z| ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n)‖⁻¹ *
        (((Real.exp (8 * beta n)) ^ 2 - 1) /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) z.2) *
        ‖(fineRightKrylovOriginalSignedPhysicalSource
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r a :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
            (halfExtent (n + 1)) 2))‖ := by
  simpa only [fineRightKrylovOriginalVacuumMeanJointBCF,
    fineRightKrylovOriginalSignedPhysicalSource,
    normalizedPhysicalOneSlabVacuumMeanJointBCF] using
    (normalizedPhysicalOneSlabVacuumReceiverBCF_rightLinkDifference_abs_le_signedSourceL2
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j •
        physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ)) z.2 e g)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
