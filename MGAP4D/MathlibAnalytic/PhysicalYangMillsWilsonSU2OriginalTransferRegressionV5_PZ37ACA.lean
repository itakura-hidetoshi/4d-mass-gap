import MGAP4D.MathlibAnalytic.CompactEnergyMismatchAffine
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalMismatchResidualVarianceV5_PZ37ABZ

/-!
# P4-Q2-PZ37ACA — actual Perron transfer-section regression moments

The original physical FF receiver satisfies F(g)-F(h)=-P(U(g)-U(h)),
where P>0 and U retain the true transfer norm, physical source, right-link
update, and updated joint Perron half-density. This exact identity transports
the receiver variance, standard deviation, energy covariance and regression
defect to the same physical transfer section. Affine-energy residuals also
transport with their exact rescaled slope and reversed orientation.

The existing FF/FC source estimate additionally bounds the receiver
variance and standard deviation explicitly. This is a coarse model upper
bound; the ABS obstruction remains. Centering in the original spatial
Haar-L2 physical Hilbert space is not identified with a zero mean on a
fixed link section.

These are unconditional finite-volume identities and bounds. No small residual,
monotonicity, lower bound, fixed support, or uniform-in-H prefactor is assumed.
MQ's locality of a different Riesz quotient is not imposed on U.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local instance p4Q2PZ37ACA_regressionGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACA_regressionCompact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACA_regressionCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACA_regressionMeasurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACA_regressionBorel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACA_regressionProbability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local instance p4Q2PZ37ACA_regressionLinks : Fintype Link := Fintype.ofFinite _
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "P" => p4Q2PZ37ABZ_originalTransferSectionPrefactor H
local notation "U" => p4Q2PZ37ABZ_originalTransferSection H

private theorem p4Q2PZ37ACA_receiver_continuous
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Continuous (F b hb f e z) :=
  (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF H 2 (by norm_num) b hb f e).continuous.comp
    (continuous_const.prodMk continuous_id)

private theorem p4Q2PZ37ACA_receiver_difference_eq_transfer
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (g h : G) :
    F b hb f e z g - F b hb f e z h =
      -(P b hb z) * (U b hb f e z g - U b hb f e z h) := by
  have hd := p4Q2PZ37ABZ_originalDifference_eq_transferSection H b hb f e z g h
  change F b hb f e z g - F b hb f e z h =
    P b hb z * (U b hb f e z h - U b hb f e z g) at hd
  rw [hd]
  ring

/-- Actual energy covariance changes sign and is scaled by the original
strictly positive Perron/transfer prefactor. -/
theorem p4Q2PZ37ACA_originalReceiver_covariance_eq_transfer
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    CompactEnergyMismatchMoment.covariance μ (F b hb f e z) E =
      -(P b hb z) * CompactEnergyMismatchMoment.covariance μ (U b hb f e z) E := by
  exact CompactEnergyMismatchMoment.covariance_of_difference_eq μ
    (F b hb f e z) (U b hb f e z) E (-(P b hb z))
    (p4Q2PZ37ACA_receiver_continuous H b hb f e z)
    (p4Q2PZ37ABZ_originalTransferSection_continuous H b hb f e z)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
    (p4Q2PZ37ACA_receiver_difference_eq_transfer H b hb f e z)

/-- The original physical receiver variance is exactly the original
transfer-section variance times P squared, with no uniform estimate inserted. -/
theorem p4Q2PZ37ACA_originalReceiver_variance_eq_transfer
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    CompactEnergyMismatchMoment.variance μ (F b hb f e z) =
      (P b hb z) ^ 2 * CompactEnergyMismatchMoment.variance μ (U b hb f e z) := by
  have h := CompactEnergyMismatchMoment.variance_of_difference_eq μ
    (F b hb f e z) (U b hb f e z) (-(P b hb z))
    (p4Q2PZ37ACA_receiver_continuous H b hb f e z)
    (p4Q2PZ37ABZ_originalTransferSection_continuous H b hb f e z)
    (p4Q2PZ37ACA_receiver_difference_eq_transfer H b hb f e z)
  simpa only [neg_sq] using h

/-- Positivity of the actual prefactor removes the absolute value in
the standard deviation identity. -/
theorem p4Q2PZ37ACA_originalReceiver_stddev_eq_transfer
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Real.sqrt (CompactEnergyMismatchMoment.variance μ (F b hb f e z)) =
      P b hb z * Real.sqrt (CompactEnergyMismatchMoment.variance μ (U b hb f e z)) := by
  rw [p4Q2PZ37ACA_originalReceiver_variance_eq_transfer,
    Real.sqrt_mul (sq_nonneg (P b hb z))
      (CompactEnergyMismatchMoment.variance μ (U b hb f e z)),
    Real.sqrt_sq (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb z).le]

/-- The true SU(2) energy regression defect transports exactly to U.
Its nonnegativity and smallness are not supplied as extra hypotheses. -/
theorem p4Q2PZ37ACA_originalRegressionDefect_eq_transfer
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    CompactEnergyMismatchMoment.variance μ (F b hb f e z) -
        4 * (CompactEnergyMismatchMoment.covariance μ (F b hb f e z) E) ^ 2 =
      (P b hb z) ^ 2 *
        (CompactEnergyMismatchMoment.variance μ (U b hb f e z) -
          4 * (CompactEnergyMismatchMoment.covariance μ (U b hb f e z) E) ^ 2) := by
  rw [p4Q2PZ37ACA_originalReceiver_variance_eq_transfer,
    p4Q2PZ37ACA_originalReceiver_covariance_eq_transfer]
  ring

/-- Every actual affine-energy residual transports with slope a/P and
opposite orientation. The updated Perron half-density is retained inside U. -/
theorem p4Q2PZ37ACA_originalResidualVariance_eq_transfer
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s a : ℝ) :
    p4Q2PZ37ABZ_originalResidualVariance H b hb f e z s a =
      (P b hb z) ^ 2 * CompactEnergyMismatchMoment.variance μ
        (CompactEnergyMismatchMoment.residual (-s) (a / P b hb z) (U b hb f e z) E) := by
  have hp : P b hb z ≠ 0 :=
    (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb z).ne'
  have hc : P b hb z * (a / P b hb z) = a := by field_simp [hp]
  have hF : Continuous (CompactEnergyMismatchMoment.residual s a (F b hb f e z) E) :=
    (p4Q2PZ37ACA_receiver_continuous H b hb f e z).add
      (continuous_const.mul (continuous_specialUnitaryWilsonPlaquetteEnergy 2))
  have hU : Continuous
      (CompactEnergyMismatchMoment.residual (-s) (a / P b hb z) (U b hb f e z) E) :=
    (p4Q2PZ37ABZ_originalTransferSection_continuous H b hb f e z).add
      (continuous_const.mul (continuous_specialUnitaryWilsonPlaquetteEnergy 2))
  have hDiff (g h : G) :
      CompactEnergyMismatchMoment.residual s a (F b hb f e z) E g -
        CompactEnergyMismatchMoment.residual s a (F b hb f e z) E h =
      -(P b hb z) *
        (CompactEnergyMismatchMoment.residual (-s) (a / P b hb z) (U b hb f e z) E g -
          CompactEnergyMismatchMoment.residual (-s) (a / P b hb z) (U b hb f e z) E h) := by
    have hd := p4Q2PZ37ACA_receiver_difference_eq_transfer H b hb f e z g h
    unfold CompactEnergyMismatchMoment.residual
    linear_combination hd - s * (E g - E h) * hc
  have hv := CompactEnergyMismatchMoment.variance_of_difference_eq μ
    (CompactEnergyMismatchMoment.residual s a (F b hb f e z) E)
    (CompactEnergyMismatchMoment.residual (-s) (a / P b hb z) (U b hb f e z) E)
    (-(P b hb z)) hF hU hDiff
  simpa only [p4Q2PZ37ABZ_originalResidualVariance, neg_sq] using hv

/-- Exact physical sign of the covariance obstruction: the positive
Perron prefactor cannot change the order direction in the transfer section. -/
theorem p4Q2PZ37ACA_covariance_obstruction_iff_transfer
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    0 ≤ s * CompactEnergyMismatchMoment.covariance μ (F b hb f e z) E ↔
      s * CompactEnergyMismatchMoment.covariance μ (U b hb f e z) E ≤ 0 := by
  have hp := p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb z
  rw [p4Q2PZ37ACA_originalReceiver_covariance_eq_transfer]
  constructor
  · intro h
    by_contra hn
    have ht := mul_pos hp (lt_of_not_ge hn)
    nlinarith [ht]
  · intro h
    have ht := mul_nonpos_of_nonneg_of_nonpos hp.le h
    nlinarith [ht]

/-- The original FF/FC source bound controls every genuine link-section
variance, retaining the true physical transfer norm and source norm. This
coarse upper bound supplies neither negative-tail smallness nor coercivity. -/
theorem p4Q2PZ37ACA_originalReceiver_variance_le_FC
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    CompactEnergyMismatchMoment.variance μ (F b hb f e z) ≤
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) b hb‖⁻¹ *
        (Real.exp (8 * b) ^ 3 - 1) * ‖f‖) ^ 2 := by
  let B := p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H 2 (by norm_num) b hb f e
  have hFC := p4Q2FF_originalWilsonRelativeSignedLinkResponse_norm_le_FC
    H 2 (by norm_num) b hb f e
  apply CompactEnergyMismatchMoment.variance_le_sq_of_abs_le μ
    (F b hb f e z) _ (p4Q2PZ37ACA_receiver_continuous H b hb f e z)
  intro g
  have hPoint : |F b hb f e z g| ≤ ‖B‖ := by
    change |B (z, g)| ≤ ‖B‖
    simpa only [Real.norm_eq_abs] using B.norm_coe_le_norm (z, g)
  exact hPoint.trans hFC

/-- Explicit original-model standard-deviation upper bound. It is valid
without a new source-profile assumption and keeps the H-dependent transfer
norm; it does not resolve the ABS coarse-error obstruction. -/
theorem p4Q2PZ37ACA_originalReceiver_stddev_le_FC
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Real.sqrt (CompactEnergyMismatchMoment.variance μ (F b hb f e z)) ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) b hb‖⁻¹ *
        (Real.exp (8 * b) ^ 3 - 1) * ‖f‖ := by
  have hFC := p4Q2FF_originalWilsonRelativeSignedLinkResponse_norm_le_FC
    H 2 (by norm_num) b hb f e
  apply Real.sqrt_le_iff.mpr
  exact ⟨(norm_nonneg _).trans hFC,
    p4Q2PZ37ACA_originalReceiver_variance_le_FC H b hb f e z⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalReceiver_covariance_eq_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalReceiver_variance_eq_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalReceiver_stddev_eq_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalRegressionDefect_eq_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalResidualVariance_eq_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_covariance_obstruction_iff_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalReceiver_variance_le_FC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalReceiver_stddev_le_FC
