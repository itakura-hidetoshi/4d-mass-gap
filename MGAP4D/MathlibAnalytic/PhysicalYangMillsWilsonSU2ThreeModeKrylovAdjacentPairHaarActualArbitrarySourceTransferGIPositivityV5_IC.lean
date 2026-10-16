import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarDepthZeroAllFineCouplingGISeparationV5_IB
import Mathlib.Tactic

/-!
# P4-Q2-IC: source-independent original Wilson link continuity and positive-transfer GI detection

HX established that the TRUE original Wilson one-slab transfer of the
zero-depth Krylov constant unit is continuous along a physical SU(2)
right-link insertion fiber. The proof uses GR's exact physical signed
receiver BCF and strictly positive normalized interacting Wilson
conditional density, rather than any independent Haar conditional.

The SAME proof in fact holds for EVERY actual gauge-invariant physical
Haar-L² source f, even signed inputs. Therefore HY's positive-transfer
Hellinger noncancellation theorem loses its previously explicit
transfer-continuity hypothesis without adding a new source axiom.

For any finite right-Krylov source S(a) at ANY depth r and ANY
nonnegative fine beta(n+1), if its ORIGINAL frozen Wilson transfer
is strictly positive along ONE actual target SU(2) link insertion
fiber, at frozen beta(n)>0, then:
  - at least ONE of the true interacting identity/pi-left posterior
    GI expectation gaps of S(a) is nonzero at that physical context;
  - a does not belong to the original all-context GI kernel K;
  - S(a) is a nonzero ACTUAL physical Haar-L² source;
  - the ORIGINAL spatial two-Wilson-posterior GL gap-square mass
    and the ORIGINAL pair-Haar residual Gram quadratic are positive.

The positive-transfer condition is explicitly retained as an
observable/source-specific criterion: it is not asserted for EVERY
signed fine-right source. No source-frame lower constant, higher-depth
positive-fine-beta injectivity, uniformity, H1-C3 or 4D continuum
Yang--Mills mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 950000

local instance p4Q2IC_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IC_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IC_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IC_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IC_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IC_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ArbitraryPhysicalInput

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- GR's exact relative original Wilson physical-source receiver
determines the frozen one-slab transfer continuously at every SU(2)
right-link fiber, for ANY actual gauge-invariant physical source.
No positivity of that source or transfer is required here. -/
theorem p4Q2IC_originalWilsonTransfer_rightLink_continuous
    (f : Phys) (right : Cfg) (e : Link) :
    Continuous (fun g : Gauge =>
      decomposableOneSliceTransferIntegral H 2 beta f
        (Function.update right e g)) := by
  let μ : Measure Gauge := normalizedCompactHaar Gauge
  let left : Cfg := originalWilsonExplicitIdentityBoundary H
  let L : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) beta hbeta‖⁻¹
  let T : Gauge → ℝ := fun g =>
    decomposableOneSliceTransferIntegral H 2 beta f
      (Function.update right e g)
  let P : Gauge → ℝ := fun g =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) beta hbeta left right e g
  let R : Gauge → ℝ := fun g =>
    p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      H 2 (by norm_num) beta hbeta f e ((left, right), g)
  have hR : Continuous R := by
    dsimp [R]
    exact (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      H 2 (by norm_num) beta hbeta f e).continuous.comp
        (continuous_const.prodMk continuous_id)
  have hP : Continuous P := by
    change Continuous
      (continuousNormalizedExp μ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
          H 2 (by norm_num) beta hbeta left right e))
    exact continuous_continuousNormalizedExp μ _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) beta hbeta left right e)
  have hPpos (g : Gauge) : 0 < P g :=
    p4Q2GQ_originalPosteriorDensity_pos
      H beta hbeta left right e g
  have hL : 0 < L := by
    dsimp [L]
    exact inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H 2 (by norm_num) beta hbeta)
  have hUpdate : Function.update right e (right e) = right :=
    Function.update_eq_self e right
  have hRelative (g : Gauge) :
      R g = L * (T (right e) -
        Real.sqrt (P (right e)) / Real.sqrt (P g) * T g) := by
    have hGR :=
      p4Q2GR_originalSignedResponse_at_inserted_right
        H beta hbeta f left right e g (right e)
    simpa only [hUpdate, R, L, P, T] using hGR
  exact p4Q2HX_transfer_continuous_of_positive_relative_receiver
    T R P L (right e) hR hP hPpos hL hRelative

/-- The GI noncancellation gate for an arbitrary ORIGINAL physical
source requires positivity only of its frozen Wilson transfer along
the chosen ACTUAL right-link fiber; continuity is now automatic.
The two expectations are under the original interacting Wilson
posteriors, not two alternative Haar conditionals. -/
theorem p4Q2IC_originalGI_detects_positive_originalWilsonTransfer
    (hFrozen : 0 < beta)
    (f : Phys) (right : Cfg) (e : Link)
    (hPos : ∀ g : Gauge,
      0 < decomposableOneSliceTransferIntegral H 2 beta f
        (Function.update right e g)) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H beta hbeta f e
        (originalWilsonExplicitIdentityBoundary H, right) ≠ 0 ∨
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H beta hbeta f e
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e, right) ≠ 0 := by
  exact p4Q2HY_originalWilsonGI_two_left_boundary_detects_positive_source
    H beta hbeta hFrozen f right e
    (p4Q2IC_originalWilsonTransfer_rightLink_continuous
      H beta hbeta f right e) hPos

end ArbitraryPhysicalInput

section FiniteSignedKrylov

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- This applies to any genuinely signed finite right-Krylov
combination, including positive fine beta(n+1); the fixed physical
positive-transfer test is a sufficient criterion, not a frame axiom. -/
theorem p4Q2IC_actualRight_positiveTransfer_trueGI_detected
    (hFrozen : 0 < beta n) (a : Coeff) (right : Cfg) (e : Link)
    (hPositive : ∀ g : Gauge,
      0 < decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Function.update right e g)) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e
      (originalWilsonExplicitIdentityBoundary Hn, right) ≠ 0 ∨
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e
      (p4Q2FQ_originalSU2LeftPiRotationAtLink Hn e, right) ≠ 0 := by
  exact p4Q2IC_originalGI_detects_positive_originalWilsonTransfer
    Hn (beta n) (hbeta n) hFrozen _ right e hPositive

/-- Strict positive true Wilson transfer makes the signed coefficient
detectable by the original all-physical-context GI kernel. -/
theorem p4Q2IC_actualRight_positiveTransfer_not_mem_originalGIJointKernel
    (hFrozen : 0 < beta n) (a : Coeff) (right : Cfg) (e : Link)
    (hPositive : ∀ g : Gauge,
      0 < decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Function.update right e g)) :
    a ∉ JointKernel := by
  have hOr :=
    p4Q2IC_actualRight_positiveTransfer_trueGI_detected
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen a right e hPositive
  intro hK
  have hAll :=
    (p4Q2HG_actualRightGIJointModalKernel_mem_iff
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a).mp hK
  rcases hOr with hIdentity | hPi
  · exact hIdentity (hAll e (originalWilsonExplicitIdentityBoundary Hn, right))
  · exact hPi (hAll e (p4Q2FQ_originalSU2LeftPiRotationAtLink Hn e, right))

/-- The same positive-transfer criterion proves the genuine signed
physical Haar-L² source is NONZERO, even with dependent Krylov modes. -/
theorem p4Q2IC_actualRight_positiveTransfer_physicalSource_ne_zero
    (hFrozen : 0 < beta n) (a : Coeff) (right : Cfg) (e : Link)
    (hPositive : ∀ g : Gauge,
      0 < decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Function.update right e g)) :
    (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) ≠ 0 := by
  intro hSource
  have hK :=
    p4Q2HG_actualSource_zero_mem_GIJointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a hSource
  exact (p4Q2IC_actualRight_positiveTransfer_not_mem_originalGIJointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a right e hPositive) hK

/-- Original GL spatial source mass is strictly positive whenever
the ACTUAL frozen positive-transfer test holds on ONE physical
right-link fiber, for any finite Krylov depth and fine coupling. -/
theorem p4Q2IC_actualRight_positiveTransfer_originalWilsonGLMass_pos
    (hFrozen : 0 < beta n) (a : Coeff) (right : Cfg) (e : Link)
    (hPositive : ∀ g : Gauge,
      0 < decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Function.update right e g)) :
    0 < p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      (Finset.univ : Finset Link) := by
  exact p4Q2HI_actualRightGLMass_pos_of_not_mem_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a
    (p4Q2IC_actualRight_positiveTransfer_not_mem_originalGIJointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen a right e hPositive)

/-- The independently defined original physical pair-Haar residual
Gram is positive on the SAME true positive-transfer region. -/
theorem p4Q2IC_actualRight_positiveTransfer_originalPhysicalGram_pos
    (hFrozen : 0 < beta n) (a : Coeff) (right : Cfg) (e : Link)
    (hPositive : ∀ g : Gauge,
      0 < decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Function.update right e g)) :
    0 < star a ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) := by
  exact p4Q2HI_actualRightGram_pos_of_not_mem_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a
    (p4Q2IC_actualRight_positiveTransfer_not_mem_originalGIJointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen a right e hPositive)

end FiniteSignedKrylov
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IC_originalWilsonTransfer_rightLink_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IC_originalGI_detects_positive_originalWilsonTransfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IC_actualRight_positiveTransfer_trueGI_detected
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IC_actualRight_positiveTransfer_not_mem_originalGIJointKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IC_actualRight_positiveTransfer_physicalSource_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IC_actualRight_positiveTransfer_originalWilsonGLMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IC_actualRight_positiveTransfer_originalPhysicalGram_pos
