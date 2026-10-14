import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTemporalWilsonCrossRatioV5_FP
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalPosteriorDensityFloorV5_FK
import Mathlib.Tactic

/-!
# P4-Q2-FR: exact posterior-normalization cancellation in Wilson cross log

FP proves an exact physical one-link temporal Wilson energy cross-log
formula for the ORIGINAL full one-slab positive-kernel times the actual
continuous Perron vacuum; FK identifies the same complete fiber with
the GENUINE interacting Wilson posterior normalized density.

This file promotes the FP identity from the unnormalized complete
weight to the logarithm of the NORMALIZED genuine Wilson conditional
probability density. At each left boundary A and selected right link e,

  log p_{A,B,e}(g) = log W_{A,B,e}(g) - log Z_{A,B,e}.

The partition function Z is positive and depends on the left
boundary, but it is constant in the inserted right value. It cancels
from the mixed four-corner difference, so the real TRUE normalized
conditional law retains EXACTLY the temporal one-link Wilson crossing
energy, with no vacuum or normalization artifact.

This is not a substitute for the original posterior by Haar; Haar
is solely the integration reference for normalization. No spectral
gap, positive per-link integrated RMS frame floor or continuum
Yang--Mills theorem is claimed here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1900000
set_option synthInstance.maxHeartbeats 750000

local instance p4Q2FR_topologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2FR_compactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2FR_secondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2FR_measurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2FR_borelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace GroundStatePosteriorJoint

/-- A positive continuous Haar partition normalizer produces an exact
log-density formula, with NO unverified a.e. quotient evaluation. -/
theorem p4Q2FR_log_continuousNormalizedExp_eq_logWeight_sub_logPartition
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (L : X → ℝ) (hL : Continuous L) (g : X) :
    Real.log (continuousNormalizedExp μ L g) =
      L g - Real.log (continuousExpPartition μ L) := by
  have hZ : 0 < continuousExpPartition μ L :=
    continuousExpPartition_pos μ L hL
  unfold continuousNormalizedExp
  rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]

/-- Genuine ORIGINAL Wilson POSTERIOR log density is its original
full complete fiber log weight minus its true local log partition mass. -/
theorem p4Q2FR_originalWilsonPosteriorLogDensity_eq_weight_sub_logMass
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.log
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H N hN beta hbeta left right e g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left right e g -
      Real.log
        (continuousExpPartition
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
            H N hN beta hbeta left right e)) := by
  let μ : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let L : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H N hN beta hbeta left right e
  have hCont : Continuous L :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H N hN beta hbeta left right e
  have hValue :
      L g =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
          H N hN beta hbeta left right e g :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_eq_groundStateCompleteLogWeight
      H N hN beta hbeta left right e g
  change Real.log (continuousNormalizedExp μ L g) =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
      H N hN beta hbeta left right e g -
    Real.log (continuousExpPartition μ L)
  rw [p4Q2FR_log_continuousNormalizedExp_eq_logWeight_sub_logPartition
    μ L hCont g, hValue]

/-- The ORIGINAL normalized physical Wilson one-link POSTERIOR density's
mixed four-corner logarithmic difference cancels all normalizing masses,
the spatial half action and the physical vacuum, leaving EXACTLY the
temporal SU(N) Wilson kernel energy. -/
theorem p4Q2FR_originalWilsonNormalizedPosteriorLogCrossing_eq_temporalEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left₁ left₂ right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (Real.log
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H N hN beta hbeta left₁ right e g) -
      Real.log
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H N hN beta hbeta left₁ right e h)) -
    (Real.log
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H N hN beta hbeta left₂ right e g) -
      Real.log
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H N hN beta hbeta left₂ right e h)) =
      -beta *
        ((specialUnitaryWilsonPlaquetteEnergy N ((left₁ e)⁻¹ * g) -
            specialUnitaryWilsonPlaquetteEnergy N ((left₁ e)⁻¹ * h)) -
          (specialUnitaryWilsonPlaquetteEnergy N ((left₂ e)⁻¹ * g) -
            specialUnitaryWilsonPlaquetteEnergy N ((left₂ e)⁻¹ * h))) := by
  let L₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H N hN beta hbeta left₁ right e
  let L₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H N hN beta hbeta left₂ right e
  let Z₁ := Real.log (continuousExpPartition
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) L₁)
  let Z₂ := Real.log (continuousExpPartition
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) L₂)
  let W₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
      H N hN beta hbeta left₁ right e
  let W₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
      H N hN beta hbeta left₂ right e
  have h₁g :
      Real.log
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H N hN beta hbeta left₁ right e g) = W₁ g - Z₁ :=
    p4Q2FR_originalWilsonPosteriorLogDensity_eq_weight_sub_logMass
      H N hN beta hbeta left₁ right e g
  have h₁h :
      Real.log
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H N hN beta hbeta left₁ right e h) = W₁ h - Z₁ :=
    p4Q2FR_originalWilsonPosteriorLogDensity_eq_weight_sub_logMass
      H N hN beta hbeta left₁ right e h
  have h₂g :
      Real.log
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H N hN beta hbeta left₂ right e g) = W₂ g - Z₂ :=
    p4Q2FR_originalWilsonPosteriorLogDensity_eq_weight_sub_logMass
      H N hN beta hbeta left₂ right e g
  have h₂h :
      Real.log
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H N hN beta hbeta left₂ right e h) = W₂ h - Z₂ :=
    p4Q2FR_originalWilsonPosteriorLogDensity_eq_weight_sub_logMass
      H N hN beta hbeta left₂ right e h
  rw [h₁g, h₁h, h₂g, h₂h]
  have hWilson :=
    p4Q2FP_actualWilsonCompleteFiberLog_crossDifference_eq_temporalEnergy
      H N hN beta hbeta left₁ left₂ right e g h
  change (W₁ g - Z₁ - (W₁ h - Z₁)) -
      (W₂ g - Z₂ - (W₂ h - Z₂)) = _
  nlinarith [hWilson]

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FR_log_continuousNormalizedExp_eq_logWeight_sub_logPartition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FR_originalWilsonPosteriorLogDensity_eq_weight_sub_logMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FR_originalWilsonNormalizedPosteriorLogCrossing_eq_temporalEnergy
