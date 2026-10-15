import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualRightTransferSourceKernelV5_HA
import Mathlib.Tactic

/-!
# P4-Q2-HB: exact genuine Wilson posterior-mass zero kernel at fine beta=0

HA proved that for beta(n+1)=0, the signed actual physical right-Krylov
source vanishes iff its real coefficient sum is zero. HA also proved that
the ORIGINAL frozen Wilson transfer, and hence the genuine interacting
two-LEFT-boundary posterior squared response mass (at frozen beta(n)>0),
is strictly positive when that coefficient sum is nonzero.

This file proves the missing converse WITHOUT modifying the physical
posterior: the ORIGINAL Wilson source receiver is ZERO when the true
physical input is zero. Instead of unfolding the enormous continuous
receiver, use the already proved FF actual source-L2 norm upper bound.
Then the true SU(2) interacting-posterior squared contrast of the ZERO
source is exactly zero, and at fine beta=0 the genuine posterior mass
zero-locus coincides with the physical source synthesis kernel and the
zero-sum hyperplane.

No assertion about the distinct GI two-posterior EXPECTATION GAP, no
uniform source frame, no β>0 fine-source injectivity and no continuum
Yang--Mills mass gap is used or claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 700000

local instance p4Q2HB_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HB_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HB_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HB_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HB_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section ActualPhysicalZero

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- The TRUE original Wilson physical-source FF response is identically
zero for the zero Hilbert input: its genuine FF L²-to-BCF estimate has
right-hand side zero. -/
private theorem p4Q2HB_originalWilsonRelativeResponse_zero
    (e : Link) :
    p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      H 2 (by norm_num) beta hbeta (0 : Phys) e = 0 := by
  have hFF := p4Q2FF_originalWilsonRelativeSignedLinkResponse_norm_le_FC
    H 2 (by norm_num) beta hbeta (0 : Phys) e
  have hLe :
      ‖p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H 2 (by norm_num) beta hbeta (0 : Phys) e‖ ≤ 0 := by
    simpa only [norm_zero, mul_zero] using hFF
  have hNorm :
      ‖p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H 2 (by norm_num) beta hbeta (0 : Phys) e‖ = 0 :=
    le_antisymm hLe (norm_nonneg _)
  exact norm_eq_zero.mp hNorm

/-- If the original physical source actually vanishes, so does the
ORIGINAL interacting Wilson two-LEFT-boundary posterior response-square
mass. No Haar replacement: the zero integrand is integrated against
the genuine original Wilson conditional posterior. -/
theorem p4Q2HB_originalPhysicalPosteriorMass_zero_of_source_zero
    (f : Phys) (hf : f = 0)
    (right : Cfg) (e : Link) :
    p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      H beta hbeta f right e = 0 := by
  subst f
  have hR :
      p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H 2 (by norm_num) beta hbeta (0 : Phys) e = 0 :=
    p4Q2HB_originalWilsonRelativeResponse_zero H beta hbeta e
  have hD (g : Gauge) :
      p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
        H beta hbeta (0 : Phys) right e g = 0 := by
    simp [p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference, hR]
  unfold p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
  simp [hD]

end ActualPhysicalZero

section ActualFineZeroKrylov

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- At fine beta=0 a vanishing signed coefficient SUM forces the TRUE
original interacting Wilson posterior squared two-boundary mass to be
zero, because the genuine physical SOURCE is itself zero. -/
theorem p4Q2HB_fineZero_originalPosteriorMass_zero_of_sum_zero
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ)
    (hSum : (∑ j : Fin (r + 1), a j) = 0)
    (right : Cfg) (e : PeriodicHypercubicEvenSpatialSliceLink Hn) :
    p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      right e = 0 := by
  apply p4Q2HB_originalPhysicalPosteriorMass_zero_of_source_zero
    Hn (beta n) (hbeta n)
  exact (p4Q2HA_fineZero_actualSource_zero_iff_sum_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFineZero a).mpr hSum

/-- EXACT zero locus of the TRUE interacting Wilson posterior squared
two-LEFT-boundary response mass, at positive frozen beta and zero
fine beta: it is the REAL coefficient zero-sum hyperplane. -/
theorem p4Q2HB_fineZero_originalPosteriorMass_zero_iff_sum_zero
    (hFrozen : 0 < beta n)
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ)
    (right : Cfg) (e : PeriodicHypercubicEvenSpatialSliceLink Hn) :
    p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      right e = 0 ↔
        (∑ j : Fin (r + 1), a j) = 0 := by
  constructor
  · intro hMass
    by_contra hSum
    have hp := p4Q2HA_fineZero_originalPosteriorMass_pos_of_sum_ne
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen hFineZero a hSum right e
    exact (ne_of_gt hp) hMass
  · intro hSum
    exact p4Q2HB_fineZero_originalPosteriorMass_zero_of_sum_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFineZero a hSum right e

/-- The mass detector's null directions are EXACTLY the original
physical-source synthesis null directions at the fine-beta-zero endpoint.
No transfer injectivity or signed frame assumption is hidden here. -/
theorem p4Q2HB_fineZero_originalPosteriorMass_zero_iff_physicalSource_zero
    (hFrozen : 0 < beta n)
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ)
    (right : Cfg) (e : PeriodicHypercubicEvenSpatialSliceLink Hn) :
    p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      right e = 0 ↔
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) = 0 := by
  rw [p4Q2HB_fineZero_originalPosteriorMass_zero_iff_sum_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen hFineZero a right e]
  exact (p4Q2HA_fineZero_actualSource_zero_iff_sum_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFineZero a).symm

end ActualFineZeroKrylov
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HB_originalPhysicalPosteriorMass_zero_of_source_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HB_fineZero_originalPosteriorMass_zero_of_sum_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HB_fineZero_originalPosteriorMass_zero_iff_sum_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HB_fineZero_originalPosteriorMass_zero_iff_physicalSource_zero
