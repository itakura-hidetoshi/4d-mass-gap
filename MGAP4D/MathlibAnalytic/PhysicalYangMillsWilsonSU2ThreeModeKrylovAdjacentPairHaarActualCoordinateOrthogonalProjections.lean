import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFiniteProductProjectionTensorization
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Tactic

/-!
# P4-Q2-CR: actual pair-Haar off-coordinate orthogonal projections

CQ proved finite Hilbert tensorization for commuting orthogonal projections.
Here the genuinely physical left/right joint pair-Haar measure is used
to construct an ACTUAL L² projection onto the sigma-algebra generated
by all coordinates except one chosen left/right spatial SU(N) link.

The projection is the Mathlib orthogonal projection onto the real L²
submodule lpMeas of the exact retained-coordinate sigma-algebra,
equivalently conditional expectation on the genuine independent Haar law.
We verify idempotence, real self-adjointness, norm contraction and fixed
space, and connect CJ's literal RIGHT Haar mean to its true sigma-algebra.

The coordinate projections are NOT interacting positive-beta Wilson
conditionals. Their pairwise commutation and the all-coordinate sweep
identity are next Fubini obligations, NOT assumed proved here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

local instance p4Q2CR_actualJointIndexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H) :=
  Fintype.ofFinite _

section ActualPairHaar
variable (H N : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "JH" => Lp ℝ 2 muPair

/-- Deleting literally one left-or-right spatial link from the exact
original pair-Haar joint coordinate product. -/
def p4Q2CR_actualPairHaarOffCoordinateSigma
    (i : I) : MeasurableSpace Joint :=
  MeasurableSpace.comap
    ((pairHaarPiRestriction (K := G) (fun j : I => j ≠ i)) ∘
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv H N)
    (inferInstance : MeasurableSpace ({j : I // j ≠ i} → G))

theorem p4Q2CR_actualPairHaarOffCoordinateSigma_le
    (i : I) :
    p4Q2CR_actualPairHaarOffCoordinateSigma H N i ≤
      (inferInstance : MeasurableSpace Joint) := by
  classical
  have hrestr :
      Measurable (pairHaarPiRestriction (K := G) (fun j : I => j ≠ i)) := by
    rw [measurable_pi_iff]
    intro j
    exact measurable_pi_apply j.1
  exact
    (hrestr.comp
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
        H N).measurable).comap_le

/-- Orthogonal conditional-expectation projection on the REAL independent
pair-Haar L² measure, conditioned on all coordinates except i. -/
noncomputable def p4Q2CR_actualPairHaarCoordinateProjection
    (i : I) : JH →L[ℝ] JH := by
  letI : Fact
      (p4Q2CR_actualPairHaarOffCoordinateSigma H N i ≤
        (inferInstance : MeasurableSpace Joint)) :=
    ⟨p4Q2CR_actualPairHaarOffCoordinateSigma_le H N i⟩
  exact
    (lpMeas ℝ ℝ (p4Q2CR_actualPairHaarOffCoordinateSigma H N i)
      2 muPair).starProjection

theorem p4Q2CR_actualPairHaarCoordinateProjection_idempotent
    (i : I) (x : JH) :
    p4Q2CR_actualPairHaarCoordinateProjection H N i
        (p4Q2CR_actualPairHaarCoordinateProjection H N i x) =
      p4Q2CR_actualPairHaarCoordinateProjection H N i x := by
  letI : Fact
      (p4Q2CR_actualPairHaarOffCoordinateSigma H N i ≤
        (inferInstance : MeasurableSpace Joint)) :=
    ⟨p4Q2CR_actualPairHaarOffCoordinateSigma_le H N i⟩
  let U : Submodule ℝ JH :=
    lpMeas ℝ ℝ (p4Q2CR_actualPairHaarOffCoordinateSigma H N i)
      2 muPair
  change U.starProjection (U.starProjection x) = U.starProjection x
  exact (U.starProjection_eq_self_iff).2 (U.starProjection_apply_mem x)

theorem p4Q2CR_actualPairHaarCoordinateProjection_symmetric
    (i : I) (x y : JH) :
    inner ℝ (p4Q2CR_actualPairHaarCoordinateProjection H N i x) y =
      inner ℝ x (p4Q2CR_actualPairHaarCoordinateProjection H N i y) := by
  letI : Fact
      (p4Q2CR_actualPairHaarOffCoordinateSigma H N i ≤
        (inferInstance : MeasurableSpace Joint)) :=
    ⟨p4Q2CR_actualPairHaarOffCoordinateSigma_le H N i⟩
  let U : Submodule ℝ JH :=
    lpMeas ℝ ℝ (p4Q2CR_actualPairHaarOffCoordinateSigma H N i)
      2 muPair
  change inner ℝ (U.starProjection x) y = inner ℝ x (U.starProjection y)
  exact U.inner_starProjection_left_eq_right x y

theorem p4Q2CR_actualPairHaarCoordinateProjection_norm_le
    (i : I) (x : JH) :
    ‖p4Q2CR_actualPairHaarCoordinateProjection H N i x‖ ≤ ‖x‖ := by
  letI : Fact
      (p4Q2CR_actualPairHaarOffCoordinateSigma H N i ≤
        (inferInstance : MeasurableSpace Joint)) :=
    ⟨p4Q2CR_actualPairHaarOffCoordinateSigma_le H N i⟩
  let U : Submodule ℝ JH :=
    lpMeas ℝ ℝ (p4Q2CR_actualPairHaarOffCoordinateSigma H N i)
      2 muPair
  change ‖U.starProjection x‖ ≤ ‖x‖
  exact U.norm_starProjection_apply_le x

/-- Exactly the retained-coordinate measurable real-L² submodule is fixed. -/
theorem p4Q2CR_actualPairHaarCoordinateProjection_fixed_iff
    (i : I) (x : JH) :
    p4Q2CR_actualPairHaarCoordinateProjection H N i x = x ↔
      AEStronglyMeasurable[p4Q2CR_actualPairHaarOffCoordinateSigma H N i]
        (x : Joint → ℝ) muPair := by
  letI : Fact
      (p4Q2CR_actualPairHaarOffCoordinateSigma H N i ≤
        (inferInstance : MeasurableSpace Joint)) :=
    ⟨p4Q2CR_actualPairHaarOffCoordinateSigma_le H N i⟩
  let U : Submodule ℝ JH :=
    lpMeas ℝ ℝ (p4Q2CR_actualPairHaarOffCoordinateSigma H N i)
      2 muPair
  change U.starProjection x = x ↔
      AEStronglyMeasurable[p4Q2CR_actualPairHaarOffCoordinateSigma H N i]
        (x : Joint → ℝ) muPair
  rw [U.starProjection_eq_self_iff]
  exact mem_lpMeas_iff_aestronglyMeasurable

/-- Identify deleting right target in the full disjoint-union carrier
with CK's actual retained left plus off-target right coordinates. -/
theorem p4Q2CR_actualRightLinkSigma_eq_CK
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2CR_actualPairHaarOffCoordinateSigma H N (Sum.inr target) =
      MeasurableSpace.comap
        ((pairHaarPiRestriction (K := G) (p4Q2CK_rightSupport H target)) ∘
          periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
            H N)
        (inferInstance : MeasurableSpace
          ({j : I // p4Q2CK_rightSupport H target j} → G)) := by
  have hp :
      (fun j : I => j ≠ Sum.inr target) =
        p4Q2CK_rightSupport H target := by
    funext j
    cases j with
    | inl e => simp [p4Q2CK_rightSupport]
    | inr e => simp [p4Q2CK_rightSupport]
  simp only [p4Q2CR_actualPairHaarOffCoordinateSigma, hp]

/-- CJ's literal original right-link Haar mean lies in the sigma-algebra
of exactly the same one-coordinate deletion on real pair-Haar L². -/
theorem p4Q2CR_actualRightLinkHaarMean_smallMeasurable
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    Measurable[p4Q2CR_actualPairHaarOffCoordinateSigma H N (Sum.inr target)]
      (p4Q2CJ_rightRetainedHaarMean H N target F) := by
  rw [p4Q2CR_actualRightLinkSigma_eq_CK H N target]
  exact p4Q2CK_rightRetainedHaarMean_smallMeasurable H N target F hF

/-- CQ for ACTUAL pair-Haar coordinate projections, conditional ONLY on
unproved independent-coordinate commutation. -/
theorem p4Q2CR_actualPairHaarProjectionSweep_tensorization_of_commuting
    (hComm : ∀ i j : I, ∀ x : JH,
      p4Q2CR_actualPairHaarCoordinateProjection H N i
        (p4Q2CR_actualPairHaarCoordinateProjection H N j x) =
      p4Q2CR_actualPairHaarCoordinateProjection H N j
        (p4Q2CR_actualPairHaarCoordinateProjection H N i x))
    (x : JH) :
    ‖x - p4Q2CQ_projectionSweep
      (p4Q2CR_actualPairHaarCoordinateProjection H N)
      (p4Q2CQ_finiteCoordinates I) x‖ ^ 2 ≤
      ∑ i : I, ‖x - p4Q2CR_actualPairHaarCoordinateProjection H N i x‖ ^ 2 := by
  exact
    p4Q2CQ_actualPairHaar_finiteProjectionTensorization
      H N
      (p4Q2CR_actualPairHaarCoordinateProjection H N)
      (p4Q2CR_actualPairHaarCoordinateProjection_idempotent H N)
      (p4Q2CR_actualPairHaarCoordinateProjection_symmetric H N)
      hComm
      (p4Q2CR_actualPairHaarCoordinateProjection_norm_le H N)
      x

end ActualPairHaar
end

end MathlibAnalytic
end MGAP4D
