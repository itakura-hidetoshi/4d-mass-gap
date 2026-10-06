import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointLeftQuotientMajorant
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorBCFApproximationMajorant

/-!
# Intrinsic left-corrected approximation on the actual frozen Krylov vector

The same-scale projection already living on genuine joint L2 removes the
irrelevant left-boundary part of the approximation error. The frozen vector,
fine extent halfExtent(n+1), and coupling beta(n) are unchanged. No bounded
representative of the frozen vector and no spatial locality estimate are assumed
by the operator statements. Small centered error and small propagated energy
remain quantitative model tasks, separate from common-marginal physicality.
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
local notation "Center" => posteriorLeftCenteredOperator Hn 2 Pos (beta n) (hbeta n)
local notation "OscEnergy" => periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy Hn
local notation "Frozen" => physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "FrozenProfile" => physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k

/-- A same-scale left-centered norm controls the actual frozen profile at all beta>=0. -/
theorem fineFrozenProfileEnergy_le_leftCenteredNormSq :
    FrozenProfile ≤ ‖Center Frozen‖ ^ 2 := by
  rw [physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy]
  exact sixColorProfileEnergy_le_leftCenteredNormSq Hn 2 Pos (beta n) (hbeta n) Frozen

/-- Constructed improved scalar bound evaluated on the actual frozen vector. -/
theorem fineFrozenProfileEnergy_le_leftQuotientMajorant
    (R : ResponseData) (O : BoundedContinuousFunction Joint ℝ)
    (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      Agree A C e → |O (B, A) - O (B, C)| ≤ v e) :
    FrozenProfile ≤ leftQuotientMajorant Hn 2 Pos (beta n) (hbeta n) R O v Frozen := by
  rw [physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy]
  exact sixColorProfileEnergy_le_leftQuotientMajorant Hn 2 Pos (beta n) (hbeta n) R O v hv hV Frozen

/-- The model only needs small error modulo left-boundary components. -/
theorem fineFrozenProfileEnergy_le_of_leftQuotientApproximation
    (R : ResponseData) (O : BoundedContinuousFunction Joint ℝ)
    (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      Agree A C e → |O (B, A) - O (B, C)| ≤ v e)
    (epsilon amplitude : ℝ) (hAmplitude : 0 ≤ amplitude)
    (hApprox : ‖Center (Frozen - BCFRep O)‖ ≤ epsilon)
    (hEnergy : OscEnergy
      (posteriorSixColorVariationProfile Hn 2 Pos (beta n) (hbeta n) R v) ≤ amplitude ^ 2) :
    FrozenProfile ≤ (epsilon + amplitude) ^ 2 := by
  rw [physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy]
  exact sixColorProfileEnergy_le_of_leftQuotientApproximation
    Hn 2 Pos (beta n) (hbeta n) R O v hv hV Frozen epsilon amplitude hAmplitude hApprox hEnergy

/-- Actual canonical half-barrier response data, without changing scale or coupling. -/
theorem fineFrozenProfileEnergy_le_canonicalLeftQuotientMajorant
    (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta n ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      Agree A C e → |O (B, A) - O (B, C)| ≤ v e) :
    FrozenProfile ≤ (‖Center (Frozen - BCFRep O)‖ + Real.sqrt
      (OscEnergy (canonicalPosteriorSixColorVariation Hn 2 Pos (beta n) (hbeta n) s hs hcut v))) ^ 2 := by
  exact fineFrozenProfileEnergy_le_leftQuotientMajorant n r k
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
      Hn 2 Pos s hs (beta n) (hbeta n) hcut) O v hv hV

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
