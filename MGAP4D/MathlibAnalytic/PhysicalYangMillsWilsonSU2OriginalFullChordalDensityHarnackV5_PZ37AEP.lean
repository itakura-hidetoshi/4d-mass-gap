import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullChordalTelescopingV5_PZ37AEP
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEP — original full two-boundary rho and q Harnack

AEO certified the SAME physical one-coordinate original rho and JQ
density Harnack factors exp(13*beta0*d_J(g,h)) on both boundaries.
Here the generic finite-coordinate telescoping is specialized to
the genuinely unchanged SU(2) pair boundary, and the finite sum is
definitionally IDENTICAL to the original ADL full chordal distance.

For arbitrary original boundary pairs z,w, with no link-size restriction,
  rho_H(z) <= exp(13*beta0*D_H(z,w)) * rho_H(w),
  q_H(z) <= exp(13*beta0*D_H(z,w)) * q_H(w),
and the symmetric reverse comparisons. The coefficient is uniform
over finite H while the distance D_H itself includes ALL true links.

The original JQ inverse-transfer density is symmetric because rho_H
and the exact numerator are symmetric; no independent or proxy
posterior is used. The AEK global ceilings convert the all-link
relative estimate to explicit H-dependent absolute variation.

This is not H-uniform coercivity, the GI 68 threshold, or the
continuum four-dimensional Yang--Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance

local instance p4Q2PZ37AEP_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEP_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEP_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEP_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEP_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "Omega" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H 2 (by norm_num) b0 hb0
local notation "rho" => continuousJointSqrtDensity H 2 (by norm_num) b0 hb0
local notation "q" => p4Q2JQ_originalPhysicalGIDensityWeight H
local notation "Tnorm" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b0 hb0‖
local notation "Replace" =>
  periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink H 2
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "Rfull" => fun z w : Pair => Real.exp ((13 * b0) * D z w)

local instance p4Q2PZ37AEP_links : Fintype Link := Fintype.ofFinite _

/-- The true canonical continuous Perron vacuum also telescopes
over the entire original spatial slice, without a global k_H floor. -/
theorem p4Q2PZ37AEP_originalContinuousVacuum_allLinkHarnack
    (A B : Cfg) :
    Omega A ≤
      Real.exp ((13 * b0) * ∑ e : Link, dJ (A e) (B e)) * Omega B := by
  classical
  apply p4Q2PZ37AEP_finiteCoordinateHarnack dJ (13 * b0) Omega
  intro u e g h
  have hx := p4Q2PZ37AEO_originalContinuousVacuum_oneLinkDistanceHarnack
    H u e g h
  simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink,
    mul_assoc, mul_left_comm, mul_comm] using hx

/-- Original JQ inverse-transfer density has the SAME exact
two-boundary symmetry as the original continuous joint half-density. -/
theorem p4Q2PZ37AEP_originalJQDensity_symm (A B : Cfg) :
    q b0 hb0 (A, B) = q b0 hb0 (B, A) := by
  calc
    q b0 hb0 (A, B) = Tnorm⁻¹ / rho (A, B) :=
      p4Q2PZ37AEG_originalDensity_exactVacuumCancellation H (A, B)
    _ = Tnorm⁻¹ / rho (B, A) := by
      rw [p4Q2PZ37AEL_originalSqrtDensity_symm H A B]
    _ = q b0 hb0 (B, A) :=
      (p4Q2PZ37AEG_originalDensity_exactVacuumCancellation H (B, A)).symm

/-- First-boundary one-link small-distance Harnack for original q:
obtained from its actual rho-derived symmetry, not from any
independence assumption. -/
theorem p4Q2PZ37AEP_originalJQDensity_firstBoundary_oneLinkHarnack
    (A B : Cfg) (e : Link) (g h : G) :
    q b0 hb0 (Replace A e g, B) ≤
      Real.exp (b0 * (13 * dJ g h)) *
        q b0 hb0 (Replace A e h, B) := by
  calc
    q b0 hb0 (Replace A e g, B) = q b0 hb0 (B, Replace A e g) :=
      p4Q2PZ37AEP_originalJQDensity_symm H _ _
    _ ≤ Real.exp (b0 * (13 * dJ g h)) *
          q b0 hb0 (B, Replace A e h) :=
      p4Q2PZ37AEO_originalPerronDensity_oneLinkDistanceHarnack H B A e g h
    _ = Real.exp (b0 * (13 * dJ g h)) *
          q b0 hb0 (Replace A e h, B) := by
      rw [p4Q2PZ37AEP_originalJQDensity_symm H B (Replace A e h)]

/-- UNCONDITIONAL two-boundary/all-link original joint sqrt-density
Harnack with original finite pair-Haar geometry D_H. -/
theorem p4Q2PZ37AEP_originalSqrtDensity_fullDistanceHarnack
    (z w : Pair) :
    rho z ≤ Rfull z w * rho w := by
  classical
  have hLeft :
      ∀ (A B : Cfg) (i : Link) (g h : G),
        rho (Function.update A i g, B) ≤
          Real.exp ((13 * b0) * dJ g h) *
            rho (Function.update A i h, B) := by
    intro A B i g h
    have hx :=
      p4Q2PZ37AEO_originalSqrtDensity_firstBoundary_oneLinkDistanceHarnack
        H A B i g h
    simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink,
      mul_assoc, mul_left_comm, mul_comm] using hx
  have hRight :
      ∀ (A B : Cfg) (i : Link) (g h : G),
        rho (A, Function.update B i g) ≤
          Real.exp ((13 * b0) * dJ g h) *
            rho (A, Function.update B i h) := by
    intro A B i g h
    have hx :=
      p4Q2PZ37AEO_originalSqrtDensity_oneLinkDistanceHarnack
        H A B i g h
    simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink,
      mul_assoc, mul_left_comm, mul_comm] using hx
  have h :=
    p4Q2PZ37AEP_finiteTwoBoundaryHarnack dJ (13 * b0) rho
      hLeft hRight z.1 z.2 w.1 w.2
  change rho z ≤
    Real.exp ((13 * b0) * D z w) * rho w
  simpa only [p4Q2PZ37ADL_originalFullBoundaryChordalDistance] using h

/-- Genuine reverse rho comparison at the same original D_H, by
the ALREADY proved metric symmetry. -/
theorem p4Q2PZ37AEP_originalSqrtDensity_fullDistanceReverse
    (z w : Pair) :
    rho w ≤ Rfull z w * rho z := by
  have hx := p4Q2PZ37AEP_originalSqrtDensity_fullDistanceHarnack H w z
  rw [p4Q2PZ37ADL_originalFullDistance_symm H w z] at hx
  exact hx

/-- UNCONDITIONAL two-boundary/all-link genuine JQ density Harnack,
retaining the original inverse-transfer cancellation formula. -/
theorem p4Q2PZ37AEP_originalJQDensity_fullDistanceHarnack
    (z w : Pair) :
    q b0 hb0 z ≤ Rfull z w * q b0 hb0 w := by
  classical
  have hLeft :
      ∀ (A B : Cfg) (i : Link) (g h : G),
        q b0 hb0 (Function.update A i g, B) ≤
          Real.exp ((13 * b0) * dJ g h) *
            q b0 hb0 (Function.update A i h, B) := by
    intro A B i g h
    have hx :=
      p4Q2PZ37AEP_originalJQDensity_firstBoundary_oneLinkHarnack
        H A B i g h
    simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink,
      mul_assoc, mul_left_comm, mul_comm] using hx
  have hRight :
      ∀ (A B : Cfg) (i : Link) (g h : G),
        q b0 hb0 (A, Function.update B i g) ≤
          Real.exp ((13 * b0) * dJ g h) *
            q b0 hb0 (A, Function.update B i h) := by
    intro A B i g h
    have hx :=
      p4Q2PZ37AEO_originalPerronDensity_oneLinkDistanceHarnack
        H A B i g h
    simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink,
      mul_assoc, mul_left_comm, mul_comm] using hx
  have hx :=
    p4Q2PZ37AEP_finiteTwoBoundaryHarnack dJ (13 * b0)
      (q b0 hb0) hLeft hRight z.1 z.2 w.1 w.2
  change q b0 hb0 z ≤
    Real.exp ((13 * b0) * D z w) * q b0 hb0 w
  simpa only [p4Q2PZ37ADL_originalFullBoundaryChordalDistance] using hx

/-- Reverse genuine JQ comparison at the identical full D_H distance. -/
theorem p4Q2PZ37AEP_originalJQDensity_fullDistanceReverse
    (z w : Pair) :
    q b0 hb0 w ≤ Rfull z w * q b0 hb0 z := by
  have hx := p4Q2PZ37AEP_originalJQDensity_fullDistanceHarnack H w z
  rw [p4Q2PZ37ADL_originalFullDistance_symm H w z] at hx
  exact hx

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEP_originalContinuousVacuum_allLinkHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEP_originalJQDensity_symm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEP_originalJQDensity_firstBoundary_oneLinkHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEP_originalSqrtDensity_fullDistanceHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEP_originalSqrtDensity_fullDistanceReverse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEP_originalJQDensity_fullDistanceHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEP_originalJQDensity_fullDistanceReverse
