import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalJointPosteriorHalfDensityDescentV5_GQ
import Mathlib.Tactic

/-!
# P4-Q2-GR: exact original Wilson posterior / joint-half-density relative fiber ratio

GQ proves the joint/posterior square-root cross identity for actual physical
SU(2) insertion values. This file first converts it to the exact ratio
of positive half-densities. The identity is pointwise, has no a.e. or
Haar-atom assumption, and holds for BOTH original left Wilson boundaries.
Then transport it into the actual GN signed physical response with true
kernel-smoothed physical source and positive one-slab transfer constant.

No surrogate independent Haar posterior is used; no nondegeneracy of the
signed expectation gap, physical Krylov frame, volume-uniform signed
source mass, or continuum Yang--Mills mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1700000
set_option synthInstance.maxHeartbeats 700000

local instance p4Q2GR_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GR_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GR_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GR_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GR_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section Frozen

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "rho" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
    H 2 (by norm_num) beta hbeta
local notation "posterior" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
    H 2 (by norm_num) beta hbeta
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) beta hbeta
local notation "L" => ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta‖⁻¹

/-- Exact pointwise original Wilson half-density *relative* law: no
independent posterior, positivity witness at a Haar atom, or inferred
equality of left-row partition functions is assumed. -/
theorem p4Q2GR_originalJointPosteriorFiber_relative_sqrt
    (left right : Cfg) (e : Link) (g h : Gauge) :
    Real.sqrt (rho (left, Function.update right e g)) /
        Real.sqrt (rho (left, Function.update right e h)) =
      Real.sqrt (posterior left right e g) /
        Real.sqrt (posterior left right e h) := by
  have hRg : 0 < rho (left, Function.update right e g) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) beta hbeta (left, Function.update right e g)
  have hRh : 0 < rho (left, Function.update right e h) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) beta hbeta (left, Function.update right e h)
  have hPg : 0 < posterior left right e g :=
    p4Q2GQ_originalPosteriorDensity_pos H beta hbeta left right e g
  have hPh : 0 < posterior left right e h :=
    p4Q2GQ_originalPosteriorDensity_pos H beta hbeta left right e h
  apply (div_eq_div_iff (Real.sqrt_pos.mpr hRh).ne'
    (Real.sqrt_pos.mpr hPh).ne').2
  exact p4Q2GQ_originalJointPosteriorFiber_sqrt_cross
    H beta hbeta left right e g h

/-- Explicit relative Wilson physical-source response for any pair of
actual right insertion values; the response keeps the ORIGINAL fine
physical source integral and frozen Wilson transfer factor. -/
theorem p4Q2GR_originalSignedResponse_at_inserted_right
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (left right : Cfg) (e : Link) (g h : Gauge) :
    p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      H 2 (by norm_num) beta hbeta f e
        ((left, Function.update right e h),g) =
      L * (decomposableOneSliceTransferIntegral H 2 beta f
          (Function.update right e h) -
        (Real.sqrt (posterior left right e h) /
          Real.sqrt (posterior left right e g)) *
          decomposableOneSliceTransferIntegral H 2 beta f
            (Function.update right e g)) := by
  have hSqrt :
      s (left, Function.update right e h) /
        s (left, Function.update right e g) =
      Real.sqrt (posterior left right e h) /
        Real.sqrt (posterior left right e g) := by
    have h := p4Q2GR_originalJointPosteriorFiber_relative_sqrt
      H beta hbeta left right e h g
    exact h
  rw [p4Q2GN_originalSignedResponse_eq_transferDifference]
  simp only [Function.update_idem]
  rw [hSqrt]

/-- Both actual left boundaries independently satisfy the same true
posterior-relative half-density formula. -/
theorem p4Q2GR_originalTwoBoundaries_relative_sqrt
    (right : Cfg) (e : Link) (g h : Gauge) :
    (Real.sqrt (rho
          (originalWilsonExplicitIdentityBoundary H, Function.update right e g)) /
        Real.sqrt (rho
          (originalWilsonExplicitIdentityBoundary H, Function.update right e h)) =
      Real.sqrt (posterior (originalWilsonExplicitIdentityBoundary H) right e g) /
        Real.sqrt (posterior (originalWilsonExplicitIdentityBoundary H) right e h)) ∧
    (Real.sqrt (rho
          (p4Q2FQ_originalSU2LeftPiRotationAtLink H e, Function.update right e g)) /
        Real.sqrt (rho
          (p4Q2FQ_originalSU2LeftPiRotationAtLink H e, Function.update right e h)) =
      Real.sqrt (posterior
          (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g) /
        Real.sqrt (posterior
          (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e h)) := by
  exact ⟨p4Q2GR_originalJointPosteriorFiber_relative_sqrt H beta hbeta
    (originalWilsonExplicitIdentityBoundary H) right e g h,
    p4Q2GR_originalJointPosteriorFiber_relative_sqrt H beta hbeta
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g h⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GR_originalJointPosteriorFiber_relative_sqrt
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GR_originalSignedResponse_at_inserted_right
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GR_originalTwoBoundaries_relative_sqrt
