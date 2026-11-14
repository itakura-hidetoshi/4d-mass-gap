import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedWilsonWeakMarginalComparisonAuditV5_PZ37ALQ2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateConcreteEightColorFrameGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferRealSpectrumIsolation
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALR: concrete ground-state six-spatial/two-temporal Wilson frame

ALQ/ALQ2 established an improved *conditional* positive quadratic bridge
but did not construct their same-carrier local frame / Wilson marginal data.
The existing, independently checked original Wilson *ground-state joint*
construction already provides a different genuinely typed path:

  spatial Haar L2 (Gauss-law G_H)
      -> Haar-to-vacuum linear isometry U_H
      -> genuine ground-state one-slab joint L2;
  six ACTUAL joint spatial conditional expectations and two identity
  temporal slots, indexed by Fin 8;
  a proved physical squared-norm comparison on the UNCHANGED Wilson T_H.

This is NOT an identification with a global Gibbs L2 carrier. We use the
concrete ground-state comparison theorem as it stands, without fabricating
any absent Haar/Gibbs spatial isomorphism.

The existing ground-state frame theorem gives a gap >= kappa/2 under a
physical full-top-orthogonal frame hypothesis. The exact squared-defect
transport (with no loss) yields instead the STRICTLY SHARPER
  ||R_H|| <= sqrt(1-kappa),
  physical gap_H >= 1-sqrt(1-kappa).
For 0<kappa<=1, 1-sqrt(1-kappa) > kappa/2. This is sharp for the
squared-defect premise alone; it does NOT give the ALQ linear kappa gap
without a stronger first-order physical feature-energy comparison.

One common kappa chosen before all H gives one common positive sqrt-rate
and a finite-volume physical real-spectrum enclosure. The actual concrete
all-H ground-state frame kappa>0 is STILL UNPROVED; neither all-H gap nor
continuum 4d Yang-Mills mass gap is asserted unconditionally.

Only a new Lean4 leaf, append-only, all declarations axiom-audited.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000

namespace GroundStatePosteriorJoint

/-- For positive kappa the actual square-root conversion strictly improves
the previous kappa/2 bound. No calculus or limiting argument is used. -/
theorem p4Q2PZ37ALR_sqrt_one_sub_strictly_below_half_linear
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    Real.sqrt (1 - κ) < 1 - κ / 2 := by
  have hsub : 0 ≤ 1 - κ := by linarith
  have hsqrt : (Real.sqrt (1 - κ)) ^ 2 = 1 - κ :=
    Real.sq_sqrt hsub
  have hnonneg : 0 ≤ Real.sqrt (1 - κ) := Real.sqrt_nonneg _
  have hright : 0 ≤ 1 - κ / 2 := by linarith
  have hksq : 0 < κ ^ 2 := sq_pos_of_pos hκ
  nlinarith

theorem p4Q2PZ37ALR_sqrt_gap_strictly_improves_half_linear
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    κ / 2 < 1 - Real.sqrt (1 - κ) := by
  have h := p4Q2PZ37ALR_sqrt_one_sub_strictly_below_half_linear hκ hκ1
  linarith

section GeneralFinitePhysicalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "HaarL2" =>
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H N hN beta hbeta
local notation "T" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    H N hN beta hbeta
local notation "P8" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorCondExpL2
    H N hN beta hbeta
local notation "E8" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
    H N hN beta hbeta

/-- The actual and fully typed six-spatial/two-temporal ground-state
projection family gives the physical raw squared defect with coefficient
one. No WilsonMarginalCondExpComparisonData is introduced or assumed. -/
theorem p4Q2PZ37ALR_concreteGroundStateE8_le_rawPhysicalSquaredDefect
    (x : G) :
    E8 P8 (U (x : HaarL2)) * ‖T‖ ^ 2 ≤
      ‖T‖ ^ 2 * ‖x‖ ^ 2 - ‖T x‖ ^ 2 := by
  simpa using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorResidual_eta_mul_transferNormSq_le_rawPhysicalDefect
      H N hN beta hbeta 1 (by norm_num) (by norm_num) x

/-- One concrete physical frame bound supplies the normalized squared
defect with the SAME kappa, before any sqrt/half approximation. -/
theorem p4Q2PZ37ALR_concreteFrame_implies_exactNormalizedSquaredDefect
    (κ : ℝ)
    (hframe : ∀ x : K, κ * ‖(x : G)‖ ^ 2 ≤ E8 P8 (U ((x : G) : HaarL2)))
    (x : K) :
    κ * ‖(x : G)‖ ^ 2 ≤
      ‖(x : G)‖ ^ 2 - ‖S (x : G)‖ ^ 2 := by
  have hraw0 :=
    p4Q2PZ37ALR_concreteGroundStateE8_le_rawPhysicalSquaredDefect
      H N hN beta hbeta (x : G)
  have hscale :
      κ * ‖(x : G)‖ ^ 2 * ‖T‖ ^ 2 ≤
        E8 P8 (U ((x : G) : HaarL2)) * ‖T‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (hframe x) (sq_nonneg _)
  have hraw :
      κ * ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
          H N hN beta hbeta x := by
    calc
      κ * ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 =
          κ * ‖(x : G)‖ ^ 2 * ‖T‖ ^ 2 := by ring
      _ ≤ E8 P8 (U ((x : G) : HaarL2)) * ‖T‖ ^ 2 := hscale
      _ ≤ ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 - ‖T (x : G)‖ ^ 2 := hraw0
      _ = periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
          H N hN beta hbeta x := rfl
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_raw_sq_defect_to_normalized
    H N hN beta hbeta κ x hraw

/-- Exact original physical full-top-orthogonal transfer norm from the
concrete frame, with sqrt instead of the older kappa/2 loss. -/
theorem p4Q2PZ37ALR_concreteFrame_implies_sharpSqrtNorm
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hframe : ∀ x : K, κ * ‖(x : G)‖ ^ 2 ≤ E8 P8 (U ((x : G) : HaarL2))) :
    ‖R‖ ≤ Real.sqrt (1 - κ) := by
  have hSymm : (S : G →ₗ[ℝ] G).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H N hN beta hbeta
  have hDefect : ∀ y : (realHilbertTopEigenspace S)ᗮ,
      κ * ‖(y : G)‖ ^ 2 ≤
        ‖(y : G)‖ ^ 2 - ‖S (y : G)‖ ^ 2 := by
    intro y
    exact p4Q2PZ37ALR_concreteFrame_implies_exactNormalizedSquaredDefect
      H N hN beta hbeta κ hframe y
  have h :=
    realHilbertTopEigenspaceOrthogonalRestriction_norm_le_sqrt_of_sq_defect
      S hSymm κ hκ0 hκ1 hDefect
  change ‖R‖ ≤ Real.sqrt (1 - κ)
  exact h

/-- Certified sharp nonlinear gap lower bound for the genuine finite
positive compact Wilson physical transfer, conditional ONLY on the
concrete ground-state frame hframe, no extra abstract marginal D. -/
theorem p4Q2PZ37ALR_concreteFrame_implies_sharpSqrtGap
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hframe : ∀ x : K, κ * ‖(x : G)‖ ^ 2 ≤ E8 P8 (U ((x : G) : HaarL2))) :
    1 - Real.sqrt (1 - κ) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  have h :=
    p4Q2PZ37ALR_concreteFrame_implies_sharpSqrtNorm
      H N hN beta hbeta κ hκ0 hκ1 hframe
  change 1 - Real.sqrt (1 - κ) ≤ 1 - ‖R‖
  linarith

/-- For positive kappa the new genuine physical bound is strictly
better than the older concrete eight-color kappa/2 certificate. -/
theorem p4Q2PZ37ALR_concreteFrame_sharpSqrtGap_strictly_improves_half
    (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hframe : ∀ x : K, κ * ‖(x : G)‖ ^ 2 ≤ E8 P8 (U ((x : G) : HaarL2))) :
    κ / 2 < 1 - Real.sqrt (1 - κ) ∧
      1 - Real.sqrt (1 - κ) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
          H N hN beta hbeta := by
  exact ⟨p4Q2PZ37ALR_sqrt_gap_strictly_improves_half_linear hκ hκ1,
    p4Q2PZ37ALR_concreteFrame_implies_sharpSqrtGap
      H N hN beta hbeta κ hκ.le hκ1 hframe⟩

end GeneralFinitePhysicalWilson

variable (H : ℕ)
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "P8" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorCondExpL2
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "E8" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le

/-- Actual original fixed SU(2) beta0 full-top sector: the concrete
ground-state frame coefficient yields a sharp sqrt rate. -/
theorem p4Q2PZ37ALR_originalFixedConcreteFrame_implies_sharpGap
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        E8 P8 (U ((x : G) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)))) :
    1 - Real.sqrt (1 - κ) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le := by
  exact p4Q2PZ37ALR_concreteFrame_implies_sharpSqrtGap
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
    κ hκ0 hκ1 hframe

/-- The concrete physical beta0 real spectrum is in an explicit interval
below the top 1; this is conditional only on the same actual joint frame. -/
theorem p4Q2PZ37ALR_originalFixedConcreteFrame_implies_spectralEnclosure
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        E8 P8 (U ((x : G) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)))) :
    spectrum ℝ S ⊆ Set.Icc 0 (Real.sqrt (1 - κ)) ∪ ({1} : Set ℝ) := by
  have hNorm :=
    p4Q2PZ37ALR_concreteFrame_implies_sharpSqrtNorm
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
      κ hκ0 hκ1 hframe
  have hSpectrum :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_real_spectrum_subset_excitedInterval_union_one
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
  intro μ hμ
  rcases hSpectrum hμ with hExcited | hTop
  · exact Or.inl ⟨hExcited.1, hExcited.2.trans hNorm⟩
  · exact Or.inr hTop

/-- The FULL existing model-specific 8-color frame *proposition*
already quantifies the single kappa before all H. If it is discharged
by a genuine Wilson estimate, the physically actual constant sqrt-rate
follows with no extra same-carrier assumptions. -/
theorem p4Q2PZ37ALR_originalFixedUniformConcreteFrame_implies_sharpUniformGap
    (hframe :
      PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateConcreteEightColorFrame
        (fun H : ℕ => H) 2 (by norm_num)
        (fun _ : ℕ => beta0)
        (fun _ : ℕ => p4Q2PZ37ADC_fixedCoupling_pos.le)) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
      ∀ H : ℕ,
        1 - Real.sqrt (1 - κ) ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
            H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le := by
  rcases hframe with ⟨κ, hκ, hκ1, hFrameAll⟩
  refine ⟨κ, hκ, hκ1, ?_⟩
  intro H
  exact p4Q2PZ37ALR_originalFixedConcreteFrame_implies_sharpGap
    H κ hκ.le hκ1 (hFrameAll H)

/-- The witness in the preceding theorem is genuinely positive and
STRICTLY improves the earlier concrete ground-state kappa/2 bound,
but its EXISTENCE still depends on proving the actual physical frame. -/
theorem p4Q2PZ37ALR_originalFixedUniformConcreteFrame_implies_strictImprovement
    (hframe :
      PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateConcreteEightColorFrame
        (fun H : ℕ => H) 2 (by norm_num)
        (fun _ : ℕ => beta0)
        (fun _ : ℕ => p4Q2PZ37ADC_fixedCoupling_pos.le)) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
      κ / 2 < 1 - Real.sqrt (1 - κ) ∧
      ∀ H : ℕ,
        1 - Real.sqrt (1 - κ) ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
            H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le := by
  rcases p4Q2PZ37ALR_originalFixedUniformConcreteFrame_implies_sharpUniformGap
      hframe with ⟨κ, hκ, hκ1, hGap⟩
  exact ⟨κ, hκ, hκ1,
    p4Q2PZ37ALR_sqrt_gap_strictly_improves_half_linear hκ hκ1, hGap⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALR_sqrt_one_sub_strictly_below_half_linear
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALR_sqrt_gap_strictly_improves_half_linear
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALR_concreteGroundStateE8_le_rawPhysicalSquaredDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALR_concreteFrame_implies_exactNormalizedSquaredDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALR_concreteFrame_implies_sharpSqrtNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALR_concreteFrame_implies_sharpSqrtGap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALR_concreteFrame_sharpSqrtGap_strictly_improves_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALR_originalFixedConcreteFrame_implies_sharpGap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALR_originalFixedConcreteFrame_implies_spectralEnclosure
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALR_originalFixedUniformConcreteFrame_implies_sharpUniformGap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALR_originalFixedUniformConcreteFrame_implies_strictImprovement
