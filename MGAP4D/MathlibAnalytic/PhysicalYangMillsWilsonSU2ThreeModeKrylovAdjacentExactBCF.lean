import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointTransferExactBCF
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorLeftQuotientMajorant

/-!
# Actual frozen Krylov vectors have constructed exact joint BCF representatives

The final physical pair-transfer step regularizes every finite L2 orbit input.
The old frozen vector is NOT redefined: its fine scale halfExtent(n+1), orbit
coupling beta(n+1), and final frozen coupling beta(n) remain distinct and intact.

Consequently both full and left-centered BCF approximation errors are exactly
zero. The constructed right-anchored initial variation supplies a concrete
profile-energy bound without a new oscillation witness. Its smallness and
support-distance decay remain quantitative obligations; finite-volume
continuity and compactness do not provide volume-uniform norm estimates.
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
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF Hn 2 Pos (beta n) (hbeta n)
local notation "Center" => posteriorLeftCenteredOperator Hn 2 Pos (beta n) (hbeta n)
local notation "OscEnergy" => periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy Hn
local notation "Frozen" => physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "FrozenProfile" => physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k

/-- Concrete observable obtained from the actual final frozen-coupling transfer. -/
def fineFrozenBCF : BoundedContinuousFunction Joint ℝ :=
  jointTransferBCF Hn 2 Pos (beta n) (hbeta n)
    (physicalYangMillsSU2AdjacentFinePairOrbitVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)

/-- Equality with the pre-existing frozen vector, not a new vector definition. -/
theorem fineFrozenBCF_rep_eq : BCFRep (fineFrozenBCF (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k) = Frozen := by
  exact jointTransferBCF_rep_eq Hn 2 Pos (beta n) (hbeta n)
    (physicalYangMillsSU2AdjacentFinePairOrbitVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)

/-- The full BCF approximation error is zero, including the r=0 orbit. -/
theorem fineFrozenBCF_approximation_error :
    ‖Frozen - BCFRep (fineFrozenBCF (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)‖ = 0 := by
  rw [fineFrozenBCF_rep_eq, sub_self, norm_zero]

/-- The optimal left-centered approximation error is also exactly zero. -/
theorem fineFrozenBCF_leftCentered_error :
    ‖Center (Frozen - BCFRep (fineFrozenBCF (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k))‖ = 0 := by
  rw [fineFrozenBCF_rep_eq, sub_self, map_zero, norm_zero]

/-- Actual initial right-variation profile with unchanged left components removed. -/
def fineFrozenAnchoredInitialVariation : Link → ℝ :=
  rightAnchoredInitialVariation Hn 2
    (fineFrozenBCF (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)

/-- The previous general approximation majorant evaluates exactly to its
propagated energy at this constructed representative. -/
theorem fineFrozenLeftQuotientMajorant_eq_energy (R : ResponseData) (v : Link → ℝ) :
    leftQuotientMajorant Hn 2 Pos (beta n) (hbeta n) R
      (fineFrozenBCF (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k) v Frozen =
      OscEnergy (posteriorSixColorVariationProfile Hn 2 Pos (beta n) (hbeta n) R v) := by
  simp only [leftQuotientMajorant, fineFrozenBCF_rep_eq, sub_self, map_zero, norm_zero, zero_add]
  exact Real.sq_sqrt (posteriorSixColorVariationEnergy_nonneg Hn 2 Pos (beta n) (hbeta n) R v)

/-- A concrete bound on the old frozen profile: the initial width is constructed,
not assumed, and the approximation-error term has been discharged exactly. -/
theorem fineFrozenProfileEnergy_le_constructedAnchorEnergy (R : ResponseData) :
    FrozenProfile ≤ OscEnergy (posteriorSixColorVariationProfile Hn 2 Pos (beta n) (hbeta n) R
      (fineFrozenAnchoredInitialVariation (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)) := by
  rw [physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy]
  rw [← fineFrozenBCF_rep_eq (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k]
  apply sixColorProfileEnergy_le_variationOscillationEnergy Hn 2 Pos (beta n) (hbeta n) R
    (fineFrozenBCF (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)
    (fineFrozenAnchoredInitialVariation (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)
    (rightAnchoredInitialVariation_nonneg Hn 2 _)
  intro B e A C _hAgree
  exact rightAnchoredInitialVariation_bound Hn 2 _ B e A C

/-- The actual canonical half-barrier data supply the response matrix;
no smallness or growing-distance estimate is asserted by this specialization. -/
theorem fineFrozenProfileEnergy_le_canonicalAnchorEnergy
    (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta n ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s) :
    FrozenProfile ≤ OscEnergy (canonicalPosteriorSixColorVariation Hn 2 Pos (beta n) (hbeta n) s hs hcut
      (fineFrozenAnchoredInitialVariation (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)) :=
  fineFrozenProfileEnergy_le_constructedAnchorEnergy n r k
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
      Hn 2 Pos s hs (beta n) (hbeta n) hcut)

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
