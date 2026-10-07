import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateDeweightedContrast
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorResponseCovarianceBridge
import Mathlib.Tactic

/-!
# Exact factorization of posterior local-factor covariance through the source tilt

The source multiplier used by the signed joint-kernel response is only the
source-dependent part of the full posterior right-target local factor. The
remaining factor depends on the fixed right boundary, target link and updated
value, but not on the posterior integration variable.

This file names that positive source-independent factor and proves

  L_full(A) = boundaryTilt * sourceTilt(A).

It then packages the source tilt as a bounded-continuous observable and pulls
the scalar factor exactly through posterior covariance:

  Cov(F, L_full) = boundaryTilt * Cov(F, sourceTilt).

No lower bound on boundaryTilt is used here. Consequently no covariance
constant is degraded in this layer.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp
    (-beta * (1 / 2 : ℝ) *
      ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
        (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
              (Function.update B target g) p) -
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p)))

theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt_pos
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
        H N beta B target g := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
  exact Real.exp_pos _

theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_eq_boundaryTilt_mul_sourceRightLinkTilt
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
          H N beta B target g *
        GroundStatePosteriorJoint.sourceRightLinkTilt
          N beta (A target) (B target) g := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
    GroundStatePosteriorJoint.sourceRightLinkTilt
  rw [← Real.exp_add]
  congr 1
  ring

noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabSourceRightLinkTiltBCF
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
      H N beta B target g)⁻¹ •
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B target g

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabSourceRightLinkTiltBCF_apply
    (H N : ℕ)
    (beta : ℝ)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabSourceRightLinkTiltBCF
        H N beta B target g A =
      GroundStatePosteriorJoint.sourceRightLinkTilt
        N beta (A target) (B target) g := by
  let c :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
      H N beta B target g
  have hc : c ≠ 0 :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt_pos
      H N beta B target g).ne'
  change c⁻¹ *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g =
    GroundStatePosteriorJoint.sourceRightLinkTilt
      N beta (A target) (B target) g
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_eq_boundaryTilt_mul_sourceRightLinkTilt
      H N beta A B target g
  ]
  change c⁻¹ *
      (c * GroundStatePosteriorJoint.sourceRightLinkTilt
        N beta (A target) (B target) g) =
    GroundStatePosteriorJoint.sourceRightLinkTilt
      N beta (A target) (B target) g
  field_simp [hc]

theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF_eq_boundaryTilt_smul_sourceRightLinkTiltBCF
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
        H N beta B target g =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
          H N beta B target g •
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabSourceRightLinkTiltBCF
          H N beta B target g := by
  ext A
  simp only [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF_apply,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabSourceRightLinkTiltBCF_apply,
    BoundedContinuousFunction.coe_smul,
    smul_eq_mul
  ]
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_eq_boundaryTilt_mul_sourceRightLinkTilt
      H N beta A B target g

theorem periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_localFactor_eq_boundaryTilt_mul_sourceRightLinkTilt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B F
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B target g) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
          H N beta B target g *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B F
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabSourceRightLinkTiltBCF
            H N beta B target g) := by
  let c :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
      H N beta B target g
  let G :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabSourceRightLinkTiltBCF
      H N beta B target g
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF_eq_boundaryTilt_smul_sourceRightLinkTiltBCF
      H N beta B target g
  ]
  unfold periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
  change
    (∫ A, F A * (c * G A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
          H N hN beta hbeta B) -
      (∫ A, F A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
            H N hN beta hbeta B) *
        (∫ A, c * G A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
            H N hN beta hbeta B) =
      c *
        ((∫ A, F A * G A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
              H N hN beta hbeta B) -
          (∫ A, F A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
              H N hN beta hbeta B) *
            (∫ A, G A
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
                H N hN beta hbeta B))
  have hProduct :
      (∫ A, F A * (c * G A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
            H N hN beta hbeta B) =
        c *
          ∫ A, F A * G A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
              H N hN beta hbeta B := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with A
    ring
  have hMean :
      (∫ A, c * G A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
            H N hN beta hbeta B) =
        c *
          ∫ A, G A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
              H N hN beta hbeta B := by
    rw [integral_const_mul]
  rw [hProduct, hMean]
  ring

end

end MGAP4D.MathlibAnalytic
