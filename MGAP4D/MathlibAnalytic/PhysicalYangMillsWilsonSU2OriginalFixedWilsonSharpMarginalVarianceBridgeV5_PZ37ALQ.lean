import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedWilsonQuadraticRayleighCriterionV5_PZ37ALP
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonMarginalCondExpComparison
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferRealSpectrumIsolation
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALQ: sharp Wilson marginal-variance bridge

The independently certified ALP exact physical SU(2) fixed-beta0
positive quadratic-form criterion identifies the genuinely missing model
input: ||A_H x||² <= q ||A_H||² ||x||² on the entire full-top-orthogonal
K_H, with ONE q<1 selected before all finite H.

This new append-only leaf connects ALP to the existing genuine physical
Wilson marginal conditional-expectation *comparison data*.  Instead of
transporting the marginal/frame estimate through the squared raw norm
defect of P_H=A_H† A_H and paying the old δ/2 conversion, we apply the
ALP positive Rayleigh bound directly to the ORIGINAL analysis energy:
  ||A_H||² * E_color,H(x)
    <= ||A_H||² ||x||² - ||A_H x||².
Together with kappa ||x||² <= E_color,H(x), the sharp conclusion is
  ||R_H|| <= 1-kappa, gap_H >= kappa,
for 0 <= kappa <= 1.  No compactness argument or unnecessary sqrt/2
loss appears in this conditional bridge.

The requisite physical WilsonMarginalCondExpComparisonData (including
Wilson-marginal lift/intertwining and coarse sigma-algebra compatibility)
and any H-independent positive frame kappa are NOT constructed here.
The comparison is a *premise*, not an invented identification.
If the local family has a nonzero common fixed vector in K_H, positive
frame coercivity is obstructed: the common-fixed/frame intersection must
be zero.

For one fixed color type and one kappa>0 valid at ALL H, the same
conditional route certifies an H-uniform top-orthogonal gap, the entire
physical real spectral interval [0,1-kappa] U {1}, and a common q=1-kappa.
No unproved existence claim, replacement Wilson kernel, modified
Haar/source/AJA, or continuum Yang-Mills mass-gap claim is made.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000

namespace GroundStatePosteriorJoint

/-- Exact unsquared marginal-variance transport, with no spurious 1/2
loss. The model-facing work is the actual marginal comparison D and
the actual local/frame estimate hframe, not the operator algebra. -/
theorem p4Q2PZ37ALQ_genericMarginalFrameToFeatureEnergy
    {E F C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    [CompleteSpace E]
    [CompleteSpace F]
    [Fintype C]
    [Nonempty C]
    (localP : C → E →L[ℝ] E)
    (A : E →L[ℝ] F)
    (D : WilsonMarginalCondExpComparisonData localP A)
    (κ : ℝ) (x : E)
    (hframe : κ * ‖x‖ ^ 2 ≤ boundedColorNormalizedResidualEnergy localP x) :
    ‖A x‖ ^ 2 ≤ (1 - κ) * ‖A‖ ^ 2 * ‖x‖ ^ 2 := by
  have hComparison :=
    D.analysisNormSq_mul_residual_le_analysisDefect localP A x
  have hScaled :=
    mul_le_mul_of_nonneg_left hframe (sq_nonneg ‖A‖)
  have hDeficit :
      ‖A‖ ^ 2 * (κ * ‖x‖ ^ 2) ≤
        ‖A‖ ^ 2 * ‖x‖ ^ 2 - ‖A x‖ ^ 2 :=
    hScaled.trans hComparison
  calc
    ‖A x‖ ^ 2 ≤
        ‖A‖ ^ 2 * ‖x‖ ^ 2 - ‖A‖ ^ 2 * (κ * ‖x‖ ^ 2) := by
          linarith
    _ = (1 - κ) * ‖A‖ ^ 2 * ‖x‖ ^ 2 := by ring

/-- Frame obstruction: any strictly positive residual-energy lower bound
excludes nonzero vectors fixed by ALL local operators. This is only a
necessary condition for coercivity, not a proof of uniform coercivity. -/
theorem p4Q2PZ37ALQ_genericPositiveFrameForbidsNonzeroCommonFixed
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (localP : C → E →L[ℝ] E)
    (κ : ℝ) (hκ : 0 < κ)
    (x : E)
    (hframe : κ * ‖x‖ ^ 2 ≤ boundedColorNormalizedResidualEnergy localP x)
    (hfixed : x ∈ boundedColorCommonFixedSpace localP) :
    x = 0 := by
  have hResidualZero :
      boundedColorNormalizedResidualEnergy localP x = 0 :=
    boundedColorNormalizedResidualEnergy_eq_zero_of_mem_commonFixedSpace
      localP x hfixed
  rw [hResidualZero] at hframe
  by_contra hx
  have hNormPos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hImpossible : 0 < κ * ‖x‖ ^ 2 :=
    mul_pos hκ (sq_pos_of_pos hNormPos)
  linarith

local instance p4Q2PZ37ALQ_physicalCompleteSpace (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

variable (H : ℕ)

local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "P" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "A" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le

/-- The exact Wilson-marginal data, if physically realized at beta0,
controls the unmodified feature-analysis deficit WITHOUT squaring P. -/
theorem p4Q2PZ37ALQ_originalFixedMarginalAnalysisDefect
    {C : Type*} [Fintype C] [Nonempty C]
    (localP : C → G →L[ℝ] G)
    (D : WilsonMarginalCondExpComparisonData localP A)
    (x : K) :
    ‖A‖ ^ 2 * boundedColorNormalizedResidualEnergy localP (x : G) ≤
      ‖A‖ ^ 2 * ‖(x : G)‖ ^ 2 - ‖A (x : G)‖ ^ 2 := by
  exact D.analysisNormSq_mul_residual_le_analysisDefect localP A (x : G)

/-- Local frame coercivity plus ACTUAL Wilson marginal compatibility yields
the full unmodified physical feature-energy estimate at the original beta0. -/
theorem p4Q2PZ37ALQ_originalFixedMarginalFrameToFeatureEnergy
    {C : Type*} [Fintype C] [Nonempty C]
    (localP : C → G →L[ℝ] G)
    (D : WilsonMarginalCondExpComparisonData localP A)
    (κ : ℝ)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy localP (x : G))
    (x : K) :
    ‖A (x : G)‖ ^ 2 ≤
      (1 - κ) * ‖A‖ ^ 2 * ‖(x : G)‖ ^ 2 := by
  exact p4Q2PZ37ALQ_genericMarginalFrameToFeatureEnergy
    localP A D κ (x : G) (hframe x)

/-- Sharp new physical Wilson excited-norm bound: the original
positive quadratic-form ALP criterion replaces the older squared-defect
loss by a direct coefficient 1-kappa. -/
theorem p4Q2PZ37ALQ_originalFixedNorm_le_of_marginalFrame
    {C : Type*} [Fintype C] [Nonempty C]
    (localP : C → G →L[ℝ] G)
    (D : WilsonMarginalCondExpComparisonData localP A)
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy localP (x : G)) :
    ‖R‖ ≤ 1 - κ := by
  apply (p4Q2PZ37ALP_originalFixedNorm_le_iff_featureEnergy
    H (1 - κ) (by linarith)).mpr
  intro x
  have hEnergy :=
    p4Q2PZ37ALQ_originalFixedMarginalFrameToFeatureEnergy
      H localP D κ hframe x
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_eq_analysis_sq
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le]
  exact hEnergy

/-- The conditional exact gap lower bound is kappa, NOT the kappa/2
lower bound of the earlier squared-Wilson-defect route. -/
theorem p4Q2PZ37ALQ_originalFixedGap_ge_of_marginalFrame
    {C : Type*} [Fintype C] [Nonempty C]
    (localP : C → G →L[ℝ] G)
    (D : WilsonMarginalCondExpComparisonData localP A)
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy localP (x : G)) :
    κ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le := by
  have hNorm :=
    p4Q2PZ37ALQ_originalFixedNorm_le_of_marginalFrame
      H localP D κ hκ0 hκ1 hframe
  change κ ≤ 1 - ‖R‖
  linarith

/-- The unmodified physical spectrum isolates the FULL top eigenspace:
the entire excited real spectrum is in [0,1-kappa], conditional on the
precise same Wilson marginal/frame hypotheses. -/
theorem p4Q2PZ37ALQ_originalFixedSpectrum_subset_of_marginalFrame
    {C : Type*} [Fintype C] [Nonempty C]
    (localP : C → G →L[ℝ] G)
    (D : WilsonMarginalCondExpComparisonData localP A)
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy localP (x : G)) :
    spectrum ℝ S ⊆
      Set.Icc 0 (1 - κ) ∪ ({1} : Set ℝ) := by
  have hSpectrum :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_real_spectrum_subset_excitedInterval_union_one
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
  have hNorm :=
    p4Q2PZ37ALQ_originalFixedNorm_le_of_marginalFrame
      H localP D κ hκ0 hκ1 hframe
  intro mu hmu
  rcases hSpectrum hmu with hExcited | hTop
  · exact Or.inl ⟨hExcited.1, hExcited.2.trans hNorm⟩
  · exact Or.inr hTop

/-- A strong physical frame implies that the original full-top-orthogonal
sector contains NO nonzero common fixed vector of the local color family.
The converse is not claimed; the precise coefficient is still necessary. -/
theorem p4Q2PZ37ALQ_originalFixedNoNonzeroCommonColorFixed
    {C : Type*} [Fintype C]
    (localP : C → G →L[ℝ] G)
    (κ : ℝ) (hκ : 0 < κ)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy localP (x : G))
    (x : K)
    (hfixed : (x : G) ∈ boundedColorCommonFixedSpace localP) :
    x = 0 := by
  have hzero : (x : G) = 0 :=
    p4Q2PZ37ALQ_genericPositiveFrameForbidsNonzeroCommonFixed
      localP κ hκ (x : G) (hframe x) hfixed
  exact Subtype.ext hzero

/-- A concrete nonzero common fixed excited vector is a strict obstruction
to ANY positive frame coefficient for that local family. -/
theorem p4Q2PZ37ALQ_originalFixedCommonFixedObstructsPositiveFrame
    {C : Type*} [Fintype C]
    (localP : C → G →L[ℝ] G)
    (κ : ℝ) (hκ : 0 < κ)
    (x : K)
    (hx : (x : G) ≠ 0)
    (hfixed : (x : G) ∈ boundedColorCommonFixedSpace localP) :
    ¬ ∀ y : K,
      κ * ‖(y : G)‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy localP (y : G) := by
  intro hframe
  have hzero :=
    p4Q2PZ37ALQ_originalFixedNoNonzeroCommonColorFixed
      H localP κ hκ hframe x hfixed
  exact hx (congrArg (fun y : K => (y : G)) hzero)

/-- ONE fixed color type and ONE frame kappa chosen before every finite H
yields the exact sharp uniform physical Wilson gap. The dependent D H
hypothesis is deliberately explicit: no unverified marginal realization
is being asserted by this theorem. -/
theorem p4Q2PZ37ALQ_allH_gap_ge_of_uniformMarginalFrame
    {C : Type*} [Fintype C] [Nonempty C]
    (localP : ∀ H : ℕ,
      C →
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (D : ∀ H : ℕ,
      WilsonMarginalCondExpComparisonData
        (localP H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le))
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hframe : ∀ (H : ℕ)
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le),
      κ * ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy (localP H)
          (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)) :
    ∀ H : ℕ,
      κ ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le := by
  intro H
  exact p4Q2PZ37ALQ_originalFixedGap_ge_of_marginalFrame
    H (localP H) (D H) κ hκ0 hκ1 (hframe H)

/-- The conditional all-H Wilson marginal theorem certifies a true common
positive transfer-gap coefficient IF, AND ONLY IF USED WITH, its physical
marginal comparison and uniform frame witnesses. -/
theorem p4Q2PZ37ALQ_allH_uniformGap_of_uniformMarginalFrame
    {C : Type*} [Fintype C] [Nonempty C]
    (localP : ∀ H : ℕ,
      C →
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (D : ∀ H : ℕ,
      WilsonMarginalCondExpComparisonData
        (localP H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le))
    (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hframe : ∀ (H : ℕ)
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le),
      κ * ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy (localP H)
          (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)) :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
      (fun H : ℕ => H) 2 (by norm_num) (fun _ : ℕ => beta0)
      (fun _ : ℕ => p4Q2PZ37ADC_fixedCoupling_pos.le) := by
  refine ⟨κ, hκ, ?_⟩
  exact p4Q2PZ37ALQ_allH_gap_ge_of_uniformMarginalFrame
    localP D κ hκ.le hκ1 hframe

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ_genericMarginalFrameToFeatureEnergy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ_genericPositiveFrameForbidsNonzeroCommonFixed
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ_originalFixedMarginalAnalysisDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ_originalFixedMarginalFrameToFeatureEnergy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ_originalFixedNorm_le_of_marginalFrame
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ_originalFixedGap_ge_of_marginalFrame
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ_originalFixedSpectrum_subset_of_marginalFrame
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ_originalFixedNoNonzeroCommonColorFixed
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ_originalFixedCommonFixedObstructsPositiveFrame
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ_allH_gap_ge_of_uniformMarginalFrame
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ_allH_uniformGap_of_uniformMarginalFrame
