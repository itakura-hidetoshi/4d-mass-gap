import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorStrictTemporalOrderV5_JZ
import Mathlib.Tactic

/-!
# P4-Q2-KF — strict genuine Wilson posterior contrast at SU(2) extrema

Retain the actual two interacting Wilson conditional posterior densities,
the true SU(2) normalized Haar reference, and the original transfer/Perron
vacuum. The original temporal Wilson contrast has its minimum at identity
and maximum at the physical pi-rotation. JN/JX show that the original
two-posterior minor respects this order, and JN2 identifies the integral
of the same minor with the *original* posterior density contrast.

Using continuity and full support of SU(2) Haar, the true density
contrast is strictly positive at identity and strictly negative at the
pi-rotation, at every positive frozen b, all finite H and physical
right/link context. This is a concrete original-posterior noncancellation
statement; it does not yet imply spatial-source physical GI detection.
No independent-Haar posterior, source frame, Dobrushin, new axiom,
sorry/admit, continuum or H1-C3 theorem.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KF_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KF_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KF_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KF_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KF_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2KF_haarOpenPos :
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)).IsOpenPosMeasure := by
  unfold normalizedCompactHaar
  infer_instance

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "nu" => normalizedCompactHaar Gauge
local notation "D" => p4Q2FZ_originalSU2TemporalWilsonContrast
local notation "M" => p4Q2JN_originalPosteriorTwoPointMinor H

/-- Every authentic SU(2) temporal Wilson contrast is at least its
identity value -2, without a coupling or volume restriction. -/
theorem p4Q2KF_temporalWilsonContrast_one_le (g : Gauge) :
    D (1 : Gauge) ≤ D g := by
  rw [p4Q2FZ_originalSU2TemporalWilsonContrast_one]
  have h0 :
      0 ≤ specialUnitaryWilsonPlaquetteEnergy 2 g :=
    specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num) g
  have h2 :
      specialUnitaryWilsonPlaquetteEnergy 2
        ((specialUnitaryTwoRotation Real.pi)⁻¹ * g) ≤ 2 :=
    specialUnitaryWilsonPlaquetteEnergy_le_two (by norm_num) _
  change (-2 : ℝ) ≤
    specialUnitaryWilsonPlaquetteEnergy 2 g -
      specialUnitaryWilsonPlaquetteEnergy 2
        ((specialUnitaryTwoRotation Real.pi)⁻¹ * g)
  linarith

/-- Every genuine SU(2) temporal contrast is bounded above by its
physical pi-rotation value +2. -/
theorem p4Q2KF_temporalWilsonContrast_le_rotation (g : Gauge) :
    D g ≤ D (specialUnitaryTwoRotation Real.pi) := by
  rw [p4Q2FZ_originalSU2TemporalWilsonContrast_rotation]
  have h2 :
      specialUnitaryWilsonPlaquetteEnergy 2 g ≤ 2 :=
    specialUnitaryWilsonPlaquetteEnergy_le_two (by norm_num) g
  have h0 :
      0 ≤ specialUnitaryWilsonPlaquetteEnergy 2
        ((specialUnitaryTwoRotation Real.pi)⁻¹ * g) :=
    specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num) _
  change
    specialUnitaryWilsonPlaquetteEnergy 2 g -
      specialUnitaryWilsonPlaquetteEnergy 2
        ((specialUnitaryTwoRotation Real.pi)⁻¹ * g) ≤ (2 : ℝ)
  linarith

/-- The original *interacting* two-posterior minor is nonnegative at
its left SU(2) identity insertion, for every second insertion. -/
theorem p4Q2KF_originalPosteriorMinor_identity_nonneg
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link)
    (g : Gauge) :
    0 ≤ M b hb.le right e 1 g := by
  rcases (p4Q2KF_temporalWilsonContrast_one_le g).eq_or_lt with heq | hlt
  · rw [p4Q2JN_originalPosteriorMinor_exact_temporalFactor]
    rw [heq, sub_self]
    simp
  · exact (p4Q2JX_originalPosteriorMinor_pos_of_temporal_lt
      H b hb right e 1 g hlt).le

/-- The same original minor has the opposite sign at the genuine
pi-rotation maximum, for all SU(2) right insertions. -/
theorem p4Q2KF_originalPosteriorMinor_rotation_nonpos
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link)
    (g : Gauge) :
    M b hb.le right e (specialUnitaryTwoRotation Real.pi) g ≤ 0 := by
  rcases (p4Q2KF_temporalWilsonContrast_le_rotation g).eq_or_lt with heq | hlt
  · rw [p4Q2JN_originalPosteriorMinor_exact_temporalFactor]
    rw [heq, sub_self]
    simp
  · exact (p4Q2JX_originalPosteriorMinor_neg_of_temporal_gt
      H b hb right e (specialUnitaryTwoRotation Real.pi) g hlt).le

/-- The *literal original* normalized two-Wilson-posterior density
difference is strictly positive at identity. The proof uses the
already-verified JN2 reconstruction of the actual signed density
contrast from its genuine two-point minor; the strict witness is
the physical SU(2) pi-rotation and full-support Haar. -/
theorem p4Q2KF_originalPosteriorDensityContrast_identity_pos
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link) :
    0 < p4Q2GB_originalWilsonPosteriorLeftDensityContrast
      H b hb.le right e (1 : Gauge) := by
  let P0 := p4Q2JN2_originalPosteriorIdentityContinuous H b hb.le right e
  let P1 := p4Q2JN2_originalPosteriorPiContinuous H b hb.le right e
  let Q : Gauge → ℝ := fun g => M b hb.le right e 1 g
  have hQCont : Continuous Q := by
    change Continuous (fun g => P0 1 * P1 g - P0 g * P1 1)
    exact (continuous_const.mul P1.continuous).sub
      (P0.continuous.mul continuous_const)
  have hQI : Integrable Q nu :=
    hQCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hNonneg (g : Gauge) : 0 ≤ Q g :=
    p4Q2KF_originalPosteriorMinor_identity_nonneg H b hb right e g
  have hPos :
      0 < Q (specialUnitaryTwoRotation Real.pi) :=
    p4Q2JN_originalPosteriorMinor_one_pi_pos H b hb right e
  have hOpen : IsOpen (Function.support Q) := by
    change IsOpen (Q ⁻¹' ({0} : Set ℝ)ᶜ)
    exact (isClosed_singleton.isOpen_compl).preimage hQCont
  have hIntegral : 0 < ∫ g : Gauge, Q g ∂nu := by
    rw [integral_pos_iff_support_of_nonneg]
    · exact hOpen.measure_pos nu
        ⟨specialUnitaryTwoRotation Real.pi, (ne_of_gt hPos)⟩
    · exact hNonneg
    · exact hQI
  rw [p4Q2JN2_originalDensityContrast_eq_minorHaarIntegral]
  exact hIntegral

/-- The authentic identity/pi posterior contrast is also strictly
negative at the genuine SU(2) pi-rotation: no surrogate conditional law. -/
theorem p4Q2KF_originalPosteriorDensityContrast_rotation_neg
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link) :
    p4Q2GB_originalWilsonPosteriorLeftDensityContrast
      H b hb.le right e (specialUnitaryTwoRotation Real.pi) < 0 := by
  let P0 := p4Q2JN2_originalPosteriorIdentityContinuous H b hb.le right e
  let P1 := p4Q2JN2_originalPosteriorPiContinuous H b hb.le right e
  let Q : Gauge → ℝ := fun g => -(M b hb.le right e
      (specialUnitaryTwoRotation Real.pi) g)
  have hQCont : Continuous Q := by
    change Continuous (fun g => -(P0 (specialUnitaryTwoRotation Real.pi) * P1 g -
      P0 g * P1 (specialUnitaryTwoRotation Real.pi)))
    exact ((continuous_const.mul P1.continuous).sub
      (P0.continuous.mul continuous_const)).neg
  have hQI : Integrable Q nu :=
    hQCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hNonneg (g : Gauge) : 0 ≤ Q g :=
    neg_nonneg.mpr (p4Q2KF_originalPosteriorMinor_rotation_nonpos H b hb right e g)
  have hPos : 0 < Q (1 : Gauge) := by
    change 0 < -(M b hb.le right e
      (specialUnitaryTwoRotation Real.pi) 1)
    rw [p4Q2JY_originalPosteriorMinor_swap]
    simpa only [neg_neg] using
      (p4Q2JN_originalPosteriorMinor_one_pi_pos H b hb right e)
  have hOpen : IsOpen (Function.support Q) := by
    change IsOpen (Q ⁻¹' ({0} : Set ℝ)ᶜ)
    exact (isClosed_singleton.isOpen_compl).preimage hQCont
  have hIntegral : 0 < ∫ g : Gauge, Q g ∂nu := by
    rw [integral_pos_iff_support_of_nonneg]
    · exact hOpen.measure_pos nu ⟨1, (ne_of_gt hPos)⟩
    · exact hNonneg
    · exact hQI
  have hDensity :=
    p4Q2JN2_originalDensityContrast_eq_minorHaarIntegral H b hb.le right e
      (specialUnitaryTwoRotation Real.pi)
  change 0 < ∫ g : Gauge,
    -(M b hb.le right e (specialUnitaryTwoRotation Real.pi) g) ∂nu at hIntegral
  rw [integral_neg, ← hDensity] at hIntegral
  linarith

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KF_temporalWilsonContrast_one_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KF_temporalWilsonContrast_le_rotation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KF_originalPosteriorMinor_identity_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KF_originalPosteriorMinor_rotation_nonpos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KF_originalPosteriorDensityContrast_identity_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KF_originalPosteriorDensityContrast_rotation_neg
