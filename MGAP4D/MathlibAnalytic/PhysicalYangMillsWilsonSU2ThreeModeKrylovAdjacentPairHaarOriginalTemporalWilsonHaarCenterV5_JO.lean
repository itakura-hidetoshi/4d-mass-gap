import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorCenteredLogTangentV5_JM
import MGAP4D.MathlibAnalytic.CompactGaugeWilsonGaugeInvariance
import Mathlib.Tactic

/-!
# P4-Q2-JO: exact Haar centering of the TRUE SU(2) temporal Wilson contrast

The genuine temporal SU(2) Wilson-energy contrast appearing in FZ,
FR, GA and JM is

  D(g) = E_W(g) - E_W(Rπ⁻¹ * g).

The original normalized compact SU(2) Haar reference is left invariant.
Therefore the integral of D itself is EXACTLY ZERO: the centered
function in JM is equal to the literal, uncentered Wilson action
contrast, NOT just equivalent modulo constants.

Consequences:
  * The original FZ positive centered Haar variance equals ∫ D² dHaar.
  * The already-formalized JM genuine two-interacting-Wilson-posterior
    centered-log contrast is exactly -b times D, in C(SU2,ℝ).
  * No differentiability of the physical Perron vacuum or either
    separate Wilson posterior is presumed.

This is a theorem about the actual SU(2) Haar reference and Wilson
action; it is NOT a substitution of a conditional posterior by Haar
and does not assert GI spatial-action separation, H1-C3 or continuum
Yang–Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JO_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JO_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JO_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JO_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JO_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "nu" => normalizedCompactHaar Gauge
local notation "D" => p4Q2FZ_originalSU2TemporalWilsonContrast

/-- LEFT-HAAR TRANSLATION INVARIANCE forces the true FZ temporal
SU(2) Wilson crossing-energy difference to have exactly zero
normalized-Haar mean. The pi rotation is the actual SU(2) element. -/
theorem p4Q2JO_temporalWilsonContrast_HaarMean_zero :
    (∫ g : Gauge, D g ∂nu) = 0 := by
  let R : Gauge := specialUnitaryTwoRotation Real.pi
  let E : Gauge → ℝ := specialUnitaryWilsonPlaquetteEnergy 2
  have hE : Continuous E := continuous_specialUnitaryWilsonPlaquetteEnergy 2
  have hEI : Integrable E nu :=
    hE.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hShift : Continuous (fun g : Gauge => E (R⁻¹ * g)) :=
    hE.comp (continuous_const.mul continuous_id)
  have hShiftI : Integrable (fun g : Gauge => E (R⁻¹ * g)) nu :=
    hShift.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmp :
      MeasurePreserving (fun g : Gauge => R⁻¹ * g * 1) nu nu :=
    normalizedCompactHaar_measurePreserving_mul_left_right Gauge R⁻¹ 1
  have hHaar :
      (∫ g : Gauge, E (R⁻¹ * g) ∂nu) =
        ∫ g : Gauge, E g ∂nu := by
    simpa only [mul_one] using hmp.integral_comp' E
  change (∫ g : Gauge, E g - E (R⁻¹ * g) ∂nu) = 0
  rw [integral_sub hEI hShiftI, hHaar, sub_self]

/-- The physical Haar-centered SU(2) Wilson temporal action used
throughout JM is already centered: its Haar mean equals zero. -/
theorem p4Q2JO_temporalWilsonCentered_eq_original :
    p4Q2JM_temporalWilsonCentered =
      p4Q2JM_temporalWilsonContinuous := by
  have hMean :
      (∫ g : Gauge, p4Q2JM_temporalWilsonContinuous g ∂nu) = 0 :=
    p4Q2JO_temporalWilsonContrast_HaarMean_zero
  unfold p4Q2JM_temporalWilsonCentered
  rw [hMean, zero_smul, sub_zero]

/-- FZ's genuinely positive centered variance is literally the
Haar-L2 square of the ORIGINAL temporal crossing Wilson action. -/
theorem p4Q2JO_temporalWilsonHaarSquare_eq_variance :
    (∫ g : Gauge, (D g) ^ 2 ∂nu) =
      p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance := by
  change (∫ g : Gauge, (D g) ^ 2 ∂nu) =
    ∫ g : Gauge, (D g - ∫ h : Gauge, D h ∂nu) ^ 2 ∂nu
  rw [p4Q2JO_temporalWilsonContrast_HaarMean_zero]
  simp

/-- Stronger explicit form of JM: the actual ORIGINAL interacting
Wilson two-posterior centered logarithmic ratio is exactly -b times
the UNcentered SU(2) temporal Wilson action, with no unknown
additive Haar constant. The actual Perron vacuum stays inside
the unchanged original physical posterior laws. -/
theorem p4Q2JO_originalPosteriorLogCentered_eq_negBeta_originalTemporal
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2JM_originalPosteriorLogCentered H b hb right e =
      (-b) • p4Q2JM_temporalWilsonContinuous := by
  rw [p4Q2JM_originalPosteriorLogCentered_eq_negBeta_WilsonCentered,
    p4Q2JO_temporalWilsonCentered_eq_original]

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JO_temporalWilsonContrast_HaarMean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JO_temporalWilsonCentered_eq_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JO_temporalWilsonHaarSquare_eq_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JO_originalPosteriorLogCentered_eq_negBeta_originalTemporal
