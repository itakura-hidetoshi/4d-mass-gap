import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointBCFApproximationMajorant
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGroundStateSweepStageProfileCoreMajorantTail

/-!
# Posterior BCF approximation bounds at the actual adjacent frozen vector

Apply the constructed continuous majorant to the pre-existing adjacent SU(2)
frozen Krylov vector, with its exact fine scale and frozen coupling. The
observable being approximated is not replaced by an arbitrary new L2 vector.

Only the approximating BCF needs pointwise initial variation. The actual
frozen vector is used in the L2 approximation error and is never assumed to
possess a bounded or continuous representative. The sharp coefficient-one
amplitude estimate preserves the existing normalized factor 1/6.

No small approximation or support-distance tail is asserted to exist here.
These remain quantitative model obligations, separately from physicality,
physical transfer/reconstruction commutation and physical-time scaling.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype

namespace GroundStatePosteriorJoint

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ) (k : Fin 3)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "ResponseData" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData Hn 2 Pos (beta n) (hbeta n)
local notation "Agree" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF Hn 2 Pos (beta n) (hbeta n)
local notation "OscEnergy" => periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy Hn
local notation "Frozen" => physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "FrozenProfile" => physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k

/-- Evaluate the explicitly constructed continuous scalar bound at the actual
frozen vector, without a dense-core or representative hypothesis on it. -/
theorem fineFrozenProfileEnergy_le_bcfApproximationMajorant
    (R : ResponseData) (O : BoundedContinuousFunction Joint ℝ)
    (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      Agree A C e → |O (B, A) - O (B, C)| ≤ v e) :
    FrozenProfile ≤ bcfApproximationMajorant Hn 2 Pos (beta n) (hbeta n) R O v Frozen := by
  rw [physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy]
  exact sixColorProfileEnergy_le_bcfApproximationMajorant
    Hn 2 Pos (beta n) (hbeta n) R O v hv hV Frozen

/-- The remaining two numerical estimates are the actual approximation error
and the energy propagated from the approximating observable's initial variation. -/
theorem fineFrozenProfileEnergy_le_of_bcfApproximation
    (R : ResponseData) (O : BoundedContinuousFunction Joint ℝ)
    (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      Agree A C e → |O (B, A) - O (B, C)| ≤ v e)
    (epsilon amplitude : ℝ) (hAmplitude : 0 ≤ amplitude)
    (hApprox : ‖Frozen - BCFRep O‖ ≤ epsilon)
    (hEnergy : OscEnergy
      (posteriorSixColorVariationProfile Hn 2 Pos (beta n) (hbeta n) R v) ≤ amplitude ^ 2) :
    FrozenProfile ≤ (epsilon + amplitude) ^ 2 := by
  rw [physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy]
  exact sixColorProfileEnergy_le_of_bcfApproximation
    Hn 2 Pos (beta n) (hbeta n) R O v hv hV Frozen
    epsilon amplitude hAmplitude hApprox hEnergy

/-- Use the actual canonical half-barrier response data at the same frozen
fine scale; no strict-Dobrushin or physicality premise is silently supplied. -/
theorem fineFrozenProfileEnergy_le_canonicalBCFApproximationMajorant
    (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta n ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      Agree A C e → |O (B, A) - O (B, C)| ≤ v e) :
    FrozenProfile ≤ (‖Frozen - BCFRep O‖ + Real.sqrt
      (OscEnergy (canonicalPosteriorSixColorVariation Hn 2 Pos (beta n) (hbeta n) s hs hcut v))) ^ 2 := by
  rw [physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy]
  exact sixColorProfileEnergy_le_canonicalBCFApproximationMajorant
    Hn 2 Pos (beta n) (hbeta n) s hs hcut O v hv hV Frozen

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
