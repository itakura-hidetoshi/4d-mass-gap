import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalSourceHellingerUniformCertificateV5_GP
import Mathlib.Tactic

/-!
# P4-Q2-GQ: exact original Wilson joint/posterior half-density descent

The positive continuous joint Wilson ground-state density and the
genuine interacting single-link Wilson posterior are not independent
objects. At each fixed physical left boundary and real right-link
fiber, their unnormalized g-dependence is the SAME positive complete
Wilson weight K_beta(left,right[e:=g]) * Omega_beta(right[e:=g]).
Only positive left and normalization scalars differ.

This file proves the exact fully NORMALIZED original posterior density
identity and then the two-point joint/posterior fiber cross equality:

 rho(left,B_g) p(left,B,h) = rho(left,B_h) p(left,B,g).

Consequently the positive square roots satisfy the exact
half-density cross equality and their ratio is independent of the
updated right link value. Apply this to BOTH actual left physical
boundaries (identity and SU2 pi rotation) used in GI/GN/GO/GP.

These are pointwise true finite-volume Wilson relations, not merely
a.e. representative selections or independent Haar conditionals.
The original canonical continuous joint density represents the genuine
joint law, while Haar is only the reference for posterior normalization.

The source-dependent signed expectation-gap nondegeneracy remains OPEN:
a further bridge to GN's half-density response and real transfer
input is needed. No source-frame condition, uniform-in-beta constant,
H1-C3 closure, or continuum Yang--Mills mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1700000
set_option synthInstance.maxHeartbeats 720000

local instance p4Q2GQ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GQ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GQ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GQ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GQ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section Frozen

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar Gauge
local notation "rho" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
    H 2 (by norm_num) beta hbeta
local notation "weight" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
    H 2 (by norm_num) beta hbeta
local notation "posterior" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
    H 2 (by norm_num) beta hbeta
local notation "L" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta‖⁻¹
local notation "Omega" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H 2 (by norm_num) beta hbeta

/-- Original continuous ground-state joint density on a REAL physical
one-link insertion fiber equals the true complete Wilson target weight
times its exact left-vacuum and transfer normalization. -/
theorem p4Q2GQ_originalJointFiber_eq_leftFactor_mul_completeWeight
    (left right : Cfg) (e : Link) (g : Gauge) :
    rho (left, Function.update right e g) =
      (L * Omega left) * weight left right e g := by
  change
    L * (Omega left *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta left (Function.update right e g) *
      Omega (Function.update right e g)) =
    (L * Omega left) *
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta left (Function.update right e g) *
      Omega (Function.update right e g))
  ring

/-- Genuine ORIGINAL interacting conditional posterior normalized density
is the exact complete Wilson target-fiber weight divided by its actual
positive Haar partition. It is not the independent Haar density. -/
theorem p4Q2GQ_originalPosteriorDensity_eq_completeWeight_div
    (left right : Cfg) (e : Link) (g : Gauge) :
    posterior left right e g =
      weight left right e g /
        ∫ h : Gauge, weight left right e h ∂μ := by
  calc
    posterior left right e g =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity
          H 2 (by norm_num) beta hbeta left right e g :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_eq_groundStateNormalizedDensity
        H 2 (by norm_num) beta hbeta left right e g
    _ = weight left right e g /
        ∫ h : Gauge, weight left right e h ∂μ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_eq
        H 2 (by norm_num) beta hbeta left right e g

/-- The exact original Wilson one-link conditional density is
strictly positive, at every physical link value and right background. -/
theorem p4Q2GQ_originalPosteriorDensity_pos
    (left right : Cfg) (e : Link) (g : Gauge) :
    0 < posterior left right e g := by
  have hBound :=
    p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) beta hbeta left right e g
  exact (Real.exp_pos (-16 * beta)).trans_le hBound.1

/-- True original Wilson joint and conditional POSTERIOR carry identical
right-link dependence. Their exact cross product therefore cancels the
left-vacuum factor, transfer norm, and the true fiber partition. -/
theorem p4Q2GQ_originalJointPosteriorFiber_cross
    (left right : Cfg) (e : Link) (g h : Gauge) :
    rho (left, Function.update right e g) * posterior left right e h =
      rho (left, Function.update right e h) * posterior left right e g := by
  rw [p4Q2GQ_originalJointFiber_eq_leftFactor_mul_completeWeight,
      p4Q2GQ_originalJointFiber_eq_leftFactor_mul_completeWeight,
      p4Q2GQ_originalPosteriorDensity_eq_completeWeight_div,
      p4Q2GQ_originalPosteriorDensity_eq_completeWeight_div]
  ring

/-- Canonical joint physical density and genuine normalized posterior
have exactly compatible square-root fibers. This is the 2-point
half-density descent identity needed before signed-source detection. -/
theorem p4Q2GQ_originalJointPosteriorFiber_sqrt_cross
    (left right : Cfg) (e : Link) (g h : Gauge) :
    Real.sqrt (rho (left, Function.update right e g)) *
        Real.sqrt (posterior left right e h) =
      Real.sqrt (rho (left, Function.update right e h)) *
        Real.sqrt (posterior left right e g) := by
  have hRg :
      0 ≤ rho (left, Function.update right e g) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) beta hbeta (left, Function.update right e g)).le
  have hRh :
      0 ≤ rho (left, Function.update right e h) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) beta hbeta (left, Function.update right e h)).le
  have hPg : 0 ≤ posterior left right e g :=
    (p4Q2GQ_originalPosteriorDensity_pos H beta hbeta left right e g).le
  have hPh : 0 ≤ posterior left right e h :=
    (p4Q2GQ_originalPosteriorDensity_pos H beta hbeta left right e h).le
  have hCross :=
    p4Q2GQ_originalJointPosteriorFiber_cross H beta hbeta left right e g h
  have hSq :
      (Real.sqrt (rho (left, Function.update right e g)) *
        Real.sqrt (posterior left right e h)) ^ 2 =
      (Real.sqrt (rho (left, Function.update right e h)) *
        Real.sqrt (posterior left right e g)) ^ 2 := by
    calc
      _ = rho (left, Function.update right e g) *
            posterior left right e h := by
        rw [mul_pow, Real.sq_sqrt hRg, Real.sq_sqrt hPh]
      _ = rho (left, Function.update right e h) *
            posterior left right e g := hCross
      _ = (Real.sqrt (rho (left, Function.update right e h)) *
            Real.sqrt (posterior left right e g)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hRh, Real.sq_sqrt hPg]
  have hNonnegLeft : 0 ≤
      Real.sqrt (rho (left, Function.update right e g)) *
        Real.sqrt (posterior left right e h) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hNonnegRight : 0 ≤
      Real.sqrt (rho (left, Function.update right e h)) *
        Real.sqrt (posterior left right e g) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith

/-- The joint positive half-density divided by the positive square root
of its genuine Wilson conditional posterior is INVARIANT as the actual
inserted SU(2) physical-link value moves along the same right fiber. -/
theorem p4Q2GQ_originalJointPosteriorFiber_sqrt_ratio_invariant
    (left right : Cfg) (e : Link) (g h : Gauge) :
    Real.sqrt (rho (left, Function.update right e g)) /
        Real.sqrt (posterior left right e g) =
      Real.sqrt (rho (left, Function.update right e h)) /
        Real.sqrt (posterior left right e h) := by
  have hg :
      Real.sqrt (posterior left right e g) ≠ 0 :=
    (Real.sqrt_pos.mpr
      (p4Q2GQ_originalPosteriorDensity_pos H beta hbeta left right e g)).ne'
  have hh :
      Real.sqrt (posterior left right e h) ≠ 0 :=
    (Real.sqrt_pos.mpr
      (p4Q2GQ_originalPosteriorDensity_pos H beta hbeta left right e h)).ne'
  apply (div_eq_div_iff hg hh).2
  exact p4Q2GQ_originalJointPosteriorFiber_sqrt_cross
    H beta hbeta left right e g h

/-- The square-root joint/posterior compatibility applies independently
to BOTH genuine SU(2) left configurations that enter the signed GI/GN
two-posterior detector; no equality between the two row normalizers
is assumed or needed. -/
theorem p4Q2GQ_originalTwoWilsonBoundary_sqrt_ratio_invariant
    (right : Cfg) (e : Link) (g h : Gauge) :
    (Real.sqrt (rho
          (originalWilsonExplicitIdentityBoundary H, Function.update right e g)) /
        Real.sqrt (posterior (originalWilsonExplicitIdentityBoundary H) right e g) =
      Real.sqrt (rho
          (originalWilsonExplicitIdentityBoundary H, Function.update right e h)) /
        Real.sqrt (posterior (originalWilsonExplicitIdentityBoundary H) right e h)) ∧
    (Real.sqrt (rho
          (p4Q2FQ_originalSU2LeftPiRotationAtLink H e, Function.update right e g)) /
        Real.sqrt (posterior
          (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g) =
      Real.sqrt (rho
          (p4Q2FQ_originalSU2LeftPiRotationAtLink H e, Function.update right e h)) /
        Real.sqrt (posterior
          (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e h)) := by
  constructor
  · exact p4Q2GQ_originalJointPosteriorFiber_sqrt_ratio_invariant
      H beta hbeta (originalWilsonExplicitIdentityBoundary H) right e g h
  · exact p4Q2GQ_originalJointPosteriorFiber_sqrt_ratio_invariant
      H beta hbeta (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g h

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GQ_originalJointFiber_eq_leftFactor_mul_completeWeight
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GQ_originalPosteriorDensity_eq_completeWeight_div
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GQ_originalPosteriorDensity_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GQ_originalJointPosteriorFiber_cross
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GQ_originalJointPosteriorFiber_sqrt_cross
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GQ_originalJointPosteriorFiber_sqrt_ratio_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GQ_originalTwoWilsonBoundary_sqrt_ratio_invariant
