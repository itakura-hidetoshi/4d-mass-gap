import MGAP4D.MathlibAnalytic.CompactEnergyMismatchRegressionThreshold
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOptimizedMismatchCertificateV5_PZ37ACA

/-!
# P4-Q2-PZ37ACB — actual physical transfer-section correlation certificate

The original centered Gauss-law source, its true interacting Wilson
transfer section U, positive Perron/transfer coefficient P, actual two
posteriors and original outer pair-Haar remain unchanged.

On the actual ABX aligned rectangle, Var(U)>0, so the signed energy
correlation is well-defined, bounded by one, and has exact regression
defect 1-rho^2 = D/Var(U). The ACA optimized mismatch is exactly
b*P*sqrt(Var U)*(1-rho). Favorable covariance and sufficiently small
true transfer regression defect provide a sufficient positive-margin
criterion; the opposite sign gives a necessary obstruction in a
specified numerical range. The complete negative tail is also
bounded directly by the true defect under favorable orientation.

No claim is made that the physical source satisfies the small-defect
condition, that the ABX region has volume-uniform mass, or that the
all-source/continuum mass-gap obligations are closed.
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
local notation "ν" => Measure.prod μ μ
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local instance p4Q2PZ37ACB_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACB_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACB_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACB_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACB_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACB_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local instance p4Q2PZ37ACB_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACB_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local notation "U" => p4Q2PZ37ABZ_originalTransferSection H
local notation "P" => p4Q2PZ37ABZ_originalTransferSectionPrefactor H
local notation "Var" => CompactEnergyMismatchMoment.variance μ
local notation "Cov" => CompactEnergyMismatchMoment.covariance μ
local notation "B" => p4Q2PZ37ACA_originalOptimizedMismatchBound H
local notation "T" => p4Q2PZ37ACA_originalRectangleThreshold H
local notation "L" => p4Q2PZ37ACA_originalRectangleOptimizedMargin H
local notation "gap" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H

private theorem p4Q2PZ37ACB_sign_sq (b : ℝ) (hb : 0 ≤ b)
    (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e) :
    R.sign ^ 2 = 1 := by
  rcases R.orientation with hs | hs <;> norm_num [hs]

private theorem p4Q2PZ37ACB_covariance_sq_le_variance
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    4 * (Cov (U b hb f e z) E) ^ 2 ≤ Var (U b hb f e z) :=
  CompactEnergyMismatchMoment.four_covariance_sq_le_variance μ (U b hb f e z) E
    (p4Q2PZ37ABZ_originalTransferSection_continuous H b hb f e z)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
    p4Q2PZ37ABZ_originalEnergy_Haar_variance

/-- An actual ABX aligned region has strictly positive variance of the
original Perron transfer section itself, not merely of its FF receiver. -/
theorem p4Q2PZ37ACB_rectangle_transferVariance_pos
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) :
    0 < Var (U b hb f e z) := by
  have hF := p4Q2PZ37ACA_rectangle_receiverVariance_pos H b hb f e R z hz
  rw [p4Q2PZ37ACA_originalReceiver_variance_eq_transfer] at hF
  have hU : 0 ≤ Var (U b hb f e z) :=
    CompactEnergyMismatchMoment.variance_nonneg μ _
      (p4Q2PZ37ABZ_originalTransferSection_continuous H b hb f e z)
  by_contra hn
  have hzero : Var (U b hb f e z) = 0 := le_antisymm (le_of_not_gt hn) hU
  rw [hzero, mul_zero] at hF
  norm_num at hF

/-- The signed Pearson coefficient is an actual quantity of the
unchanged Perron section, not an independently chosen test function. -/
def p4Q2PZ37ACB_originalTransferAlignmentRatio
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (s : ℝ) : ℝ :=
  CompactEnergyMismatchMoment.energyAlignmentRatio s
    (Var (U b hb f e z)) (Cov (U b hb f e z) E)
local notation "rho" => p4Q2PZ37ACB_originalTransferAlignmentRatio H

theorem p4Q2PZ37ACB_rectangle_alignmentRatio_bounds
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) :
    -1 ≤ rho b hb f e z R.sign ∧ rho b hb f e z R.sign ≤ 1 := by
  exact CompactEnergyMismatchMoment.energyAlignmentRatio_bounds R.sign
    (Var (U b hb f e z)) (Cov (U b hb f e z) E)
    (p4Q2PZ37ACB_sign_sq H b hb f e R)
    (p4Q2PZ37ACB_rectangle_transferVariance_pos H b hb f e R z hz)
    (p4Q2PZ37ACB_covariance_sq_le_variance H b hb f e z)

theorem p4Q2PZ37ACB_rectangle_alignmentRatio_defect
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) :
    1 - rho b hb f e z R.sign ^ 2 =
      (Var (U b hb f e z) - 4 * (Cov (U b hb f e z) E) ^ 2) /
        Var (U b hb f e z) := by
  exact CompactEnergyMismatchMoment.energyAlignmentRatio_defect_identity R.sign
    (Var (U b hb f e z)) (Cov (U b hb f e z) E)
    (p4Q2PZ37ACB_sign_sq H b hb f e R)
    (p4Q2PZ37ACB_rectangle_transferVariance_pos H b hb f e R z hz)

/-- Express the genuine ACA optimized mismatch in normalized Pearson
alignment coordinates, retaining the true positive P coefficient. -/
theorem p4Q2PZ37ACB_rectangle_optimizedBudget_eq_alignment
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) :
    B b hb f e z R.sign =
      b * P b hb z * Real.sqrt (Var (U b hb f e z)) *
        (1 - rho b hb f e z R.sign) := by
  rw [p4Q2PZ37ACA_originalOptimizedMismatchBound_eq_transfer]
  exact CompactEnergyMismatchMoment.optimizedTransferBudget_eq_alignment b
    (P b hb z) R.sign (Var (U b hb f e z)) (Cov (U b hb f e z) E)
    (p4Q2PZ37ACB_rectangle_transferVariance_pos H b hb f e R z hz)

/-- The original ACA condition is exactly an inequality on the
genuine signed energy correlation. Positivity of b is explicit. -/
theorem p4Q2PZ37ACB_rectangle_positiveCertificate_iff_alignment
    (b : ℝ) (hb : 0 ≤ b) (hbp : 0 < b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) :
    B b hb f e z R.sign < T b hb f e R ↔
      1 - rho b hb f e z R.sign <
        T b hb f e R /
          (b * P b hb z * Real.sqrt (Var (U b hb f e z))) := by
  rw [p4Q2PZ37ACA_originalOptimizedMismatchBound_eq_transfer]
  exact CompactEnergyMismatchMoment.optimizedTransferBudget_lt_iff_alignment b
    (P b hb z) R.sign (Var (U b hb f e z)) (Cov (U b hb f e z) E)
    (T b hb f e R) hbp
    (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb z)
    (p4Q2PZ37ACB_rectangle_transferVariance_pos H b hb f e R z hz)

/-- Favorable actual covariance converts the full optimized Wilson
mismatch into a quantitative bound by its actual regression defect. -/
theorem p4Q2PZ37ACB_rectangle_budget_mul_stddev_le_defect
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent)
    (hdir : 0 ≤ R.sign * Cov (U b hb f e z) E) :
    B b hb f e z R.sign * Real.sqrt (Var (U b hb f e z)) ≤
      b * P b hb z *
        (Var (U b hb f e z) - 4 * (Cov (U b hb f e z) E) ^ 2) := by
  rw [p4Q2PZ37ACA_originalOptimizedMismatchBound_eq_transfer]
  exact CompactEnergyMismatchMoment.optimizedTransferBudget_mul_stddev_le_defect b
    (P b hb z) R.sign (Var (U b hb f e z)) (Cov (U b hb f e z) E)
    hb (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb z).le
    (p4Q2PZ37ACB_rectangle_transferVariance_pos H b hb f e R z hz)
    (p4Q2PZ37ACB_sign_sq H b hb f e R)
    (p4Q2PZ37ACB_covariance_sq_le_variance H b hb f e z) hdir

/-- A favorable actual covariance and an independently proved small
true regression defect yield an actual ACA positive GI certificate. -/
theorem p4Q2PZ37ACB_rectangle_certificate_of_smallTransferDefect
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent)
    (hdir : 0 ≤ R.sign * Cov (U b hb f e z) E)
    (hsmall : b * P b hb z *
        (Var (U b hb f e z) - 4 * (Cov (U b hb f e z) E) ^ 2) <
          T b hb f e R * Real.sqrt (Var (U b hb f e z))) :
    B b hb f e z R.sign < T b hb f e R := by
  rw [p4Q2PZ37ACA_originalOptimizedMismatchBound_eq_transfer]
  exact CompactEnergyMismatchMoment.smallDefect_implies_optimizedTransferBudget_lt b
    (P b hb z) R.sign (Var (U b hb f e z)) (Cov (U b hb f e z) E)
    (T b hb f e R) hb
    (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb z).le
    (p4Q2PZ37ACB_rectangle_transferVariance_pos H b hb f e R z hz)
    (p4Q2PZ37ACB_sign_sq H b hb f e R)
    (p4Q2PZ37ACB_covariance_sq_le_variance H b hb f e z)
    hdir hsmall

/-- The SAME original physical GI response is positive if the true
transfer-section defect criterion is verified on the ABX region. -/
theorem p4Q2PZ37ACB_rectangle_GI_pos_of_smallTransferDefect
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent)
    (hdir : 0 ≤ R.sign * Cov (U b hb f e z) E)
    (hsmall : b * P b hb z *
        (Var (U b hb f e z) - 4 * (Cov (U b hb f e z) E) ^ 2) <
          T b hb f e R * Real.sqrt (Var (U b hb f e z))) :
    0 < R.sign * gap b hb f e z := by
  exact p4Q2PZ37ACA_rectangle_GI_pos_of_optimizedCertificate H b hb f e R z hz
    (p4Q2PZ37ACB_rectangle_certificate_of_smallTransferDefect
      H b hb f e R z hz hdir hsmall)

/-- No energy-slope parameter remains in this bound on the complete
original interacting-posterior negative tail, conditional only on the
measurable covariance orientation. -/
theorem p4Q2PZ37ACB_originalNegativeTail_le_transferDefect
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent)
    (hdir : 0 ≤ R.sign * Cov (U b hb f e z) E) :
    p4Q2PZ37ABY_originalNegativeTail H b hb f e z R.sign ≤
      Real.exp (32 * b) *
        (b * P b hb z *
          (Var (U b hb f e z) - 4 * (Cov (U b hb f e z) E) ^ 2) /
            Real.sqrt (Var (U b hb f e z))) := by
  have hσ : 0 < Real.sqrt (Var (U b hb f e z)) :=
    Real.sqrt_pos.mpr (p4Q2PZ37ACB_rectangle_transferVariance_pos H b hb f e R z hz)
  have hDef := p4Q2PZ37ACB_rectangle_budget_mul_stddev_le_defect
    H b hb f e R z hz hdir
  have hBudget : B b hb f e z R.sign ≤
      b * P b hb z *
        (Var (U b hb f e z) - 4 * (Cov (U b hb f e z) E) ^ 2) /
          Real.sqrt (Var (U b hb f e z)) :=
    (le_div_iff₀ hσ).mpr hDef
  exact (p4Q2PZ37ACA_originalNegativeTail_le_optimized H b hb f e z R.sign
    (p4Q2PZ37ACB_sign_sq H b hb f e R)).trans
    (mul_le_mul_of_nonneg_left hBudget (Real.exp_nonneg _))

/-- A wrong global covariance direction and a too-small ABX threshold
rule out any positive-slope certificate in the ACA residual family.
This is not a sign theorem about the genuine GI response itself. -/
theorem p4Q2PZ37ACB_rectangle_noCertificate_of_wrongOrientation
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (_hz : z ∈ R.outerEvent)
    (hdir : R.sign * Cov (U b hb f e z) E ≤ 0)
    (hscale : T b hb f e R ≤
      b * P b hb z * Real.sqrt (Var (U b hb f e z))) :
    ∀ a : ℝ, 0 < a →
      (R.eta * R.kappa * Real.exp (-32 * b) * Measure.real ν R.innerEvent -
        Real.exp (32 * b) *
          ((b / a) * p4Q2PZ37ABZ_originalResidualVariance H b hb f e z R.sign a)) /
        2 ≤ 0 := by
  have hwrong := CompactEnergyMismatchMoment.wrongOrientation_budget_ge_baseline b
    (P b hb z) R.sign (Var (U b hb f e z)) (Cov (U b hb f e z) E)
    hb (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb z).le hdir
  have hfail : T b hb f e R ≤ B b hb f e z R.sign := by
    rw [p4Q2PZ37ACA_originalOptimizedMismatchBound_eq_transfer]
    exact hscale.trans hwrong
  exact p4Q2PZ37ACA_rectangle_no_positiveResidualCertificate H b hb f e R z hfail

/-- A positive certificate under an independently verified low
positive-event threshold forces favorable *strict* physical covariance. -/
theorem p4Q2PZ37ACB_rectangle_positiveCertificate_forces_covariance
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg)
    (hscale : T b hb f e R ≤
      b * P b hb z * Real.sqrt (Var (U b hb f e z)))
    (hcert : B b hb f e z R.sign < T b hb f e R) :
    0 < R.sign * Cov (U b hb f e z) E := by
  rw [p4Q2PZ37ACA_originalOptimizedMismatchBound_eq_transfer] at hcert
  exact CompactEnergyMismatchMoment.positiveCertificate_forces_favorableOrientation b
    (P b hb z) R.sign (Var (U b hb f e z)) (Cov (U b hb f e z) E)
    (T b hb f e R) hb
    (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb z).le hscale hcert

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_rectangle_transferVariance_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_rectangle_alignmentRatio_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_rectangle_alignmentRatio_defect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_rectangle_optimizedBudget_eq_alignment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_rectangle_positiveCertificate_iff_alignment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_rectangle_budget_mul_stddev_le_defect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_rectangle_certificate_of_smallTransferDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_rectangle_GI_pos_of_smallTransferDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalNegativeTail_le_transferDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_rectangle_noCertificate_of_wrongOrientation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_rectangle_positiveCertificate_forces_covariance
