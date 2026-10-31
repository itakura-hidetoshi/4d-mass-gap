import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullSignedTailV5_PZ37ABY
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTransferFiberDetectorKernelV5_GN
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABZ — exact transfer section behind the actual Wilson mismatch

Keep the original FF receiver, true physical source, right-link update,
transfer norm, and joint Perron half-density. GN's exact representation
gives F(g) = L I_f(B) - P(z) U(g), where
  L = ||T||^(-1), P(z) = L sqrtDensity(z) > 0,
  U(g) = I_f(B[e:=g]) / sqrtDensity(z.left,B[e:=g]).
Thus the original two-update response equals P(z) (U(h)-U(g)).
The SAME original crossing moment is exactly the energy-order mismatch
of this physical transfer section, with its actual positive prefactor.

The positive Perron factors cancel in GN only in the explicit receiver
product: the true joint half-density in U is retained. No monotonicity,
small mismatch, H-uniform prefactor, or physical coercivity is assumed.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local notation "nu" => Measure.prod mu mu
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local instance p4Q2PZ37ABZ_sectionGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABZ_sectionCompact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABZ_sectionCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABZ_sectionMeasurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABZ_sectionBorel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local instance p4Q2PZ37ABZ_sectionLinks : Fintype Link := Fintype.ofFinite _
local notation "sqrtD" => continuousJointSqrtDensity H 2 (by norm_num)
local notation "transfer" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
  H 2 (by norm_num)
local notation "I" => decomposableOneSliceTransferIntegral H 2
local notation "F" => p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF H 2 (by norm_num)
local notation "diff" => p4Q2PZ37ABX_originalReceiverDifference H
local notation "psi" => p4Q2PZ37ABY_originalCrossPair H
local notation "mass" => p4Q2PZ37ABY_originalCrossPartMass H

/-- The actual positive transfer/half-density factor in the original
physical two-update receiver. This is not a uniform constant. -/
noncomputable def p4Q2PZ37ABZ_originalTransferSectionPrefactor
    (b : ℝ) (hb : 0 ≤ b) (z : Cfg × Cfg) : ℝ :=
  ‖transfer b hb‖⁻¹ * sqrtD b hb z
local notation "P" => p4Q2PZ37ABZ_originalTransferSectionPrefactor H

/-- The true transfer integral of the same Gauss-law physical source,
divided by the original updated joint Perron half-density. -/
noncomputable def p4Q2PZ37ABZ_originalTransferSection
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (g : G) : ℝ :=
  I b f (Function.update z.2 e g) /
    sqrtD b hb (z.1, Function.update z.2 e g)
local notation "U" => p4Q2PZ37ABZ_originalTransferSection H

theorem p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos
    (b : ℝ) (hb : 0 ≤ b) (z : Cfg × Cfg) :
    0 < P b hb z := by
  exact mul_pos
    (inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H 2 (by norm_num) b hb))
    (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb z)

/-- Exact GN decomposition with the original positive prefactor exposed.
The unchanged unupdated source term cancels only on taking differences. -/
theorem p4Q2PZ37ABZ_originalResponse_eq_transferSection
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (g : G) :
    F b hb f e (z, g) =
      ‖transfer b hb‖⁻¹ * I b f z.2 - P b hb z * U b hb f e z g := by
  rw [p4Q2GN_originalSignedResponse_eq_transferDifference]
  unfold p4Q2PZ37ABZ_originalTransferSectionPrefactor
    p4Q2PZ37ABZ_originalTransferSection
  ring

/-- True two-update FF response, including the exact orientation reversal. -/
theorem p4Q2PZ37ABZ_originalDifference_eq_transferSection
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (g h : G) :
    diff b hb f e z g h = P b hb z * (U b hb f e z h - U b hb f e z g) := by
  unfold p4Q2PZ37ABX_originalReceiverDifference
  rw [p4Q2PZ37ABZ_originalResponse_eq_transferSection,
    p4Q2PZ37ABZ_originalResponse_eq_transferSection]
  ring

/-- Continuity follows from the actual FF continuous response and its
everywhere positive original prefactor; no new regularity is assumed. -/
theorem p4Q2PZ37ABZ_originalTransferSection_continuous
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Continuous (U b hb f e z) := by
  have hp : P b hb z ≠ 0 :=
    (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb z).ne'
  have hF : Continuous (fun g : G => F b hb f e (z, g)) :=
    (F b hb f e).continuous.comp (continuous_const.prodMk continuous_id)
  have heq : U b hb f e z = fun g : G =>
      (‖transfer b hb‖⁻¹ * I b f z.2 - F b hb f e (z, g)) / P b hb z := by
    funext g
    apply (eq_div_iff hp).2
    rw [p4Q2PZ37ABZ_originalResponse_eq_transferSection]
    ring
  rw [heq]
  exact (continuous_const.sub hF).div_const _

/-- The actual signed Wilson crossing is the physical transfer-section
energy-order product with its genuine positive normalization. -/
theorem p4Q2PZ37ABZ_originalCrossPair_eq_transferSectionEnergy
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (s : ℝ) (w : G × G) :
    psi b hb f e z s w = (2 * b * P b hb z) *
      (s * (U b hb f e z w.2 - U b hb f e z w.1) * (E w.2 - E w.1)) := by
  rw [p4Q2PZ37ABY_originalCrossPair_eq_energy,
    p4Q2PZ37ABZ_originalDifference_eq_transferSection]
  ring

/-- At positive coupling, the actual mismatch sign is exactly the sign
of the true transfer section against the original Wilson energy order. -/
theorem p4Q2PZ37ABZ_originalCrossPair_nonneg_iff_transferSectionEnergy
    (b : ℝ) (hb : 0 < b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (s : ℝ) (w : G × G) :
    0 ≤ psi b hb.le f e z s w ↔
      0 ≤ s * (U b hb.le f e z w.2 - U b hb.le f e z w.1) * (E w.2 - E w.1) := by
  rw [p4Q2PZ37ABZ_originalCrossPair_eq_transferSectionEnergy]
  have hp : 0 < 2 * b * P b hb.le z :=
    mul_pos (mul_pos (by norm_num) hb)
      (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb.le z)
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge h) (mul_neg_of_pos_of_neg hp (lt_of_not_ge hn))
  · intro h
    exact mul_nonneg hp.le h

private theorem p4Q2PZ37ABZ_section_max_mul (k a : ℝ) (hk : 0 ≤ k) :
    max (k * a) 0 = k * max a 0 := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha, max_eq_left (mul_nonneg hk ha)]
  · have ha0 : a ≤ 0 := (lt_of_not_ge ha).le
    rw [max_eq_right ha0, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hk ha0), mul_zero]

/-- Exact full mismatch moment of the original physical source, with all
updated half-densities retained. No negative region is discarded. -/
theorem p4Q2PZ37ABZ_originalMismatch_eq_transferSectionMoment
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (s : ℝ) :
    mass b hb f e z (-s) = (2 * b * P b hb z) *
      ∫ w : G × G,
        max ((-s) * (U b hb f e z w.2 - U b hb f e z w.1) * (E w.2 - E w.1)) 0 ∂nu := by
  have hp : 0 ≤ 2 * b * P b hb z :=
    mul_nonneg (mul_nonneg (by norm_num) hb)
      (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb z).le
  unfold p4Q2PZ37ABY_originalCrossPartMass
  simp_rw [p4Q2PZ37ABZ_originalCrossPair_eq_transferSectionEnergy,
    p4Q2PZ37ABZ_section_max_mul (2 * b * P b hb z) _ hp]
  rw [integral_const_mul]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_originalResponse_eq_transferSection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_originalDifference_eq_transferSection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_originalTransferSection_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_originalCrossPair_eq_transferSectionEnergy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_originalCrossPair_nonneg_iff_transferSectionEnergy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_originalMismatch_eq_transferSectionMoment
