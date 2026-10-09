import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalVacuumInverseJointL2Cancellation
import Mathlib.Tactic

/-!
# P4-Q2-C: original Wilson posterior signed physical-mean link L² energy

PR #5330 proves for any genuine signed physical Haar-L² source f,
with frozen beta and the actual normalized Wilson transfer receiver M_f:
  |M_f(B[e <- g]) - M_f(B)|
    <= lambda_beta^(-1) * (exp(8 beta)^2-1)
       * Omega_beta(B)^(-1) * ||f||_HaarL2.

PR #5332 proves the exact cancellation in the genuine Wilson joint law:
  integral Omega_beta(B)^(-2) dmu_joint(A,B) = 1.

Integrating the physical SIGNED source bound against the actual original
Wilson posterior resampling kernel and actual Wilson joint law gives

  posteriorResamplingEnergy_e(M_f)
    <= (lambda_beta^(-1) * (exp(8 beta)^2-1) * ||f||_HaarL2)^2.

Crucially, the inverse-vacuum SUP norm is absent. This is a genuine
linkwise posterior L² estimate; it does NOT yet sum over links with a
uniform bound or prove an operator-norm/continuum mass gap.
No new probability law, finite-range posterior, Dobrushin, or axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4MeanPosteriorL2TopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4MeanPosteriorL2CompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4MeanPosteriorL2SecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4MeanPosteriorL2MeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4MeanPosteriorL2BorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4MeanPosteriorL2LinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The ACTUAL original Wilson right-link posterior two-copy energy of
the signed normalized physical transfer-mean receiver is bounded by
the source Haar-L² norm with a volume-free inverse-vacuum cancellation,
although the true physical transfer normalization is still present. -/
theorem normalizedPhysicalOneSlabVacuumMeanJointBCF_posteriorResamplingEnergy_le_signedHilbert_noVacuumSup
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    posteriorResamplingEnergy H N hN beta hbeta e
      (normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f) ≤
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        ((Real.exp (8 * beta)) ^ 2 - 1) * ‖f‖) ^ 2 := by
  classical
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let ν := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
  let Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let V :=
    normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
  let M := normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f
  let l : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  let D : ℝ := (Real.exp (8 * beta)) ^ 2 - 1
  let c : ℝ := l * D * ‖f‖
  let B : BoundedContinuousFunction (Cfg × Cfg) ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun z => c * V z.2,
        continuous_const.mul (V.continuous.comp continuous_snd)⟩
  letI : IsProbabilityMeasure ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  have hInt : Integrable (fun z => (B z) ^ 2) ν := by
    apply Integrable.of_bound
      ((B.continuous.pow 2).aestronglyMeasurable)
      (‖B‖ ^ 2)
    filter_upwards with z
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (B.norm_coe_le_norm z) 2
  have hOsc (z : Cfg × Cfg) (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      |M z - M (z.1, Function.update z.2 e g)| ≤ B z := by
    have h :=
      normalizedPhysicalOneSlabVacuumReceiverBCF_rightLinkDifference_abs_le_signedSourceL2
        H N hN beta hbeta f z.2 e g
    change
      |M (z.1, Function.update z.2 e g) - M z| ≤
        l * (D / Ω z.2) * ‖f‖ at h
    calc
      |M z - M (z.1, Function.update z.2 e g)| =
          |M (z.1, Function.update z.2 e g) - M z| := abs_sub_comm _ _
      _ ≤ l * (D / Ω z.2) * ‖f‖ := h
      _ = B z := by
        change l * (D / Ω z.2) * ‖f‖ = c * (Ω z.2)⁻¹
        dsimp [c]
        ring
  have hIntegral :
      (∫ z, (B z) ^ 2 ∂ν) = c ^ 2 := by
    calc
      (∫ z, (B z) ^ 2 ∂ν) =
        ∫ z, c ^ 2 * ((Ω z.2)⁻¹) ^ 2 ∂ν := by
          apply integral_congr_ae
          filter_upwards with z
          change (c * (Ω z.2)⁻¹) ^ 2 =
            c ^ 2 * ((Ω z.2)⁻¹) ^ 2
          ring
      _ = c ^ 2 * (∫ z, ((Ω z.2)⁻¹) ^ 2 ∂ν) :=
        integral_const_mul _ _
      _ = c ^ 2 := by
        rw [show (∫ z, ((Ω z.2)⁻¹) ^ 2 ∂ν) = 1 from
          normalizedPhysicalOneSlabContinuousVacuumInverse_sq_integral_joint_eq_one
            H N hN beta hbeta]
        ring
  have hEnergy :=
    originalWilsonPosteriorResamplingEnergy_le_pointwiseLinkOscillation
      H N hN beta hbeta e M (fun z => B z) hInt hOsc
  change posteriorResamplingEnergy H N hN beta hbeta e M ≤ c ^ 2
  exact hEnergy.trans hIntegral.le

/-- Specialization to the genuine signed uncentered fine-right Krylov
combination evolved at beta(n+1), with the original posterior and final
normalized physical mean held at the distinct frozen beta(n). -/
theorem fineRightKrylovOriginalVacuumMeanJointBCF_posteriorResamplingEnergy_le_signedHilbert_noVacuumSup
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) :
    posteriorResamplingEnergy (halfExtent (n + 1)) 2
      specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e
      (fineRightKrylovOriginalVacuumMeanJointBCF
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a) ≤
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n)‖⁻¹ *
        ((Real.exp (8 * beta n)) ^ 2 - 1) *
        ‖fineRightKrylovOriginalSignedPhysicalSource
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a‖) ^ 2 := by
  simpa only [fineRightKrylovOriginalVacuumMeanJointBCF,
    fineRightKrylovOriginalSignedPhysicalSource] using
    (normalizedPhysicalOneSlabVacuumMeanJointBCF_posteriorResamplingEnergy_le_signedHilbert_noVacuumSup
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j •
        physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ)) e)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
