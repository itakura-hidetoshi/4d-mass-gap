import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarTopProjectionFrozenInnovation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveFineOpenWindow
import Mathlib.Tactic

/-!
# P4-Q2-Z2: genuine finite-volume positive-fine top innovation via rank-one anchoring

Rather than imposing a uniform fine spectral gap (1-q_beta), compare
the ACTUAL normalized physical Wilson S_beta directly with its exactly
rank-one physical beta-zero reference Q_0 = rankOne(u_H,u_H).
A rank-free Hilbert geometric lemma shows that if S_beta has a fixed
normalized vector Omega_beta, then

  ‖u_H - P_beta u_H‖ <= ‖S_beta - Q_0‖,

where P_beta is the canonical projection onto its ENTIRE fixed space.

The already-proven raw Wilson beta-Lipschitz and positive-normalization
floor give ‖S_beta-Q_0‖ <= B_H(beta), the ORIGINAL physical constant-step
beta budget. Thus one gets nonvanishing of an authentic frozen positive-
beta posterior signed link innovation on P_beta u_H for EVERY sufficiently
small nonnegative fine beta, including STRICTLY positive fine beta.
Both couplings and true finite spatial links are kept distinct.

This establishes a local positive-fine sector, NOT global positive-beta
nonvanishing, a volume-uniform window or continuum Yang--Mills mass gap.
No surrogate, Dobrushin, axioms, sorry, or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 850000

/-- For two real-Hilbert unit vectors the residual distances to one
another's one-dimensional span are equal (equality of squared sines).
This elementary lemma avoids choosing the sign of the physical vacuum. -/
theorem p4Q2Z_unit_span_residual_symmetry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - (inner ℝ u v) • v‖ = ‖v - (inner ℝ u v) • u‖ := by
  let c : ℝ := inner ℝ u v
  have hOne : ‖u - c • v‖ ^ 2 = 1 - c ^ 2 := by
    calc
      ‖u - c • v‖ ^ 2 =
          ‖u‖ ^ 2 - 2 * inner ℝ u (c • v) + ‖c • v‖ ^ 2 :=
        norm_sub_sq_real _ _
      _ = 1 - c ^ 2 := by
        rw [hu, real_inner_smul_right, norm_smul, hv]
        simp only [mul_one, Real.norm_eq_abs, sq_abs]
        dsimp [c]
        ring
  have hTwo : ‖v - c • u‖ ^ 2 = 1 - c ^ 2 := by
    calc
      ‖v - c • u‖ ^ 2 =
          ‖v‖ ^ 2 - 2 * inner ℝ v (c • u) + ‖c • u‖ ^ 2 :=
        norm_sub_sq_real _ _
      _ = 1 - c ^ 2 := by
        rw [hv, real_inner_smul_right, norm_smul, hu]
        rw [real_inner_comm v u]
        simp only [mul_one, Real.norm_eq_abs, sq_abs]
        dsimp [c]
        ring
  have hSq : ‖u - c • v‖ ^ 2 = ‖v - c • u‖ ^ 2 := hOne.trans hTwo.symm
  have hEq : ‖u - c • v‖ = ‖v - c • u‖ := by
    nlinarith [norm_nonneg (u - c • v), norm_nonneg (v - c • u)]
  exact hEq

/-- Physical top projection stability from an *operator-norm* perturbation
of the rank-one unit reference. Only a genuine unit fixed vector is
required; the full top eigenspace need NOT be assumed rank-one. -/
theorem p4Q2Z_realHilbert_topProjection_unit_le_rankOneDifference
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) (u omega : E)
    (hu : ‖u‖ = 1) (hOmega : ‖omega‖ = 1)
    (hFixed : S omega = omega) :
    ‖u - realHilbertTopEigenspaceProjection S u‖ ≤
      ‖S - InnerProductSpace.rankOne ℝ u u‖ := by
  let F : Submodule ℝ E := realHilbertTopEigenspace S
  letI : CompleteSpace F :=
    (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  have hOmegaF : omega ∈ F :=
    (realHilbertTopEigenspace_mem S omega).mpr hFixed
  let y : F := ⟨(inner ℝ u omega) • omega, F.smul_mem _ hOmegaF⟩
  have hBdd : BddBelow (Set.range (fun x : F => ‖u - (x : E)‖)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact norm_nonneg _
  have hMinimal :
      ‖u - realHilbertTopEigenspaceProjection S u‖ ≤
        ‖u - (inner ℝ u omega) • omega‖ := by
    change ‖u - F.starProjection u‖ ≤ ‖u - (y : E)‖
    rw [F.starProjection_minimal u]
    exact ciInf_le hBdd y
  have hRank :
      (InnerProductSpace.rankOne ℝ u u) omega =
        (inner ℝ u omega) • u := by
    exact InnerProductSpace.rankOne_apply ℝ u u omega
  have hNormOmega :
      ‖omega - (InnerProductSpace.rankOne ℝ u u) omega‖ ≤
        ‖S - InnerProductSpace.rankOne ℝ u u‖ := by
    calc
      ‖omega - (InnerProductSpace.rankOne ℝ u u) omega‖ =
          ‖(S - InnerProductSpace.rankOne ℝ u u) omega‖ := by
        rw [ContinuousLinearMap.sub_apply, hFixed]
      _ ≤ ‖S - InnerProductSpace.rankOne ℝ u u‖ * ‖omega‖ :=
        ContinuousLinearMap.le_opNorm _ omega
      _ = ‖S - InnerProductSpace.rankOne ℝ u u‖ := by
        rw [hOmega, mul_one]
  calc
    ‖u - realHilbertTopEigenspaceProjection S u‖ ≤
        ‖u - (inner ℝ u omega) • omega‖ := hMinimal
    _ = ‖omega - (inner ℝ u omega) • u‖ :=
      p4Q2Z_unit_span_residual_symmetry u omega hu hOmega
    _ = ‖omega - (InnerProductSpace.rankOne ℝ u u) omega‖ := by
      rw [hRank]
    _ ≤ ‖S - InnerProductSpace.rankOne ℝ u u‖ := hNormOmega

/-- Normalization around any norm-one reference transfers the raw
operator-norm perturbation with factor 2/‖T‖. No selected unit vector
or pointwise substitution is used in the bound. -/
theorem p4Q2Z_normalized_clm_sub_normOneReference_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T Tzero : E →L[ℝ] E)
    (hT : 0 < ‖T‖) (hZero : ‖Tzero‖ = 1) :
    ‖‖T‖⁻¹ • T - Tzero‖ ≤
      2 * ‖T‖⁻¹ * ‖T - Tzero‖ := by
  let a : ℝ := ‖T‖⁻¹
  have ha : 0 ≤ a := le_of_lt (inv_pos.mpr hT)
  have hrec : a * ‖T‖ = 1 := inv_mul_cancel₀ hT.ne'
  have hrepr : a • T - Tzero = a • (T - ‖T‖ • Tzero) := by
    rw [smul_sub, smul_smul, hrec, one_smul]
  have hvariation : ‖(1 : ℝ) - ‖T‖‖ ≤ ‖T - Tzero‖ := by
    have h := abs_norm_sub_norm_le Tzero T
    rw [hZero] at h
    calc
      ‖(1 : ℝ) - ‖T‖‖ = |(1 : ℝ) - ‖T‖| := by rw [Real.norm_eq_abs]
      _ ≤ ‖Tzero - T‖ := h
      _ = ‖T - Tzero‖ := norm_sub_rev _ _
  have hsplit : T - ‖T‖ • Tzero =
        (T - Tzero) + ((1 : ℝ) - ‖T‖) • Tzero := by
    rw [sub_smul, one_smul]
    abel
  have hmiddle : ‖T - ‖T‖ • Tzero‖ ≤ 2 * ‖T - Tzero‖ := by
    calc
      ‖T - ‖T‖ • Tzero‖ =
          ‖(T - Tzero) + ((1 : ℝ) - ‖T‖) • Tzero‖ := by rw [hsplit]
      _ ≤ ‖T - Tzero‖ + ‖((1 : ℝ) - ‖T‖) • Tzero‖ :=
        norm_add_le _ _
      _ = ‖T - Tzero‖ + ‖(1 : ℝ) - ‖T‖‖ := by
        rw [norm_smul, hZero, mul_one]
      _ ≤ ‖T - Tzero‖ + ‖T - Tzero‖ :=
        add_le_add_left hvariation _
      _ = 2 * ‖T - Tzero‖ := by ring
  change ‖a • T - Tzero‖ ≤ 2 * a * ‖T - Tzero‖
  calc
    ‖a • T - Tzero‖ = a * ‖T - ‖T‖ • Tzero‖ := by
      rw [hrepr, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ a * (2 * ‖T - Tzero‖) :=
      mul_le_mul_of_nonneg_left hmiddle ha
    _ = 2 * a * ‖T - Tzero‖ := by ring

local instance p4Z2TopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Z2Compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Z2SecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Z2Measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Z2Borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Z2SpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Z2RealHilbertComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- The ACTUAL normalized Wilson fine one-slab transfer is within its
previously established physical beta-step budget B_H(fine) in OPERATOR
norm of its rank-one fine-zero reference. -/
theorem physicalOriginalNormalizedFineTransfer_sub_fineZero_norm_le_betaBudget
    (H : ℕ) (fine : ℝ) (hFine : 0 ≤ fine) :
    ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive fine hFine -
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num)‖ ≤
      physicalOriginalNormalizedTransferConstantStepBetaBudget H fine := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  let Tzero := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num)
  let m := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H fine
  let A := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hT : 0 < ‖T‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  have hTzero : ‖Tzero‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_norm
      H 2 specialUnitaryTwoWilsonRankPositive
  have hInv : ‖T‖⁻¹ ≤ m⁻¹ := by
    simpa only [T, m] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferNorm_inv_le_globalMinorizationFloor_inv
        H 2 specialUnitaryTwoWilsonRankPositive fine hFine)
  have hRaw : ‖T - Tzero‖ ≤ A * fine := by
    simpa [T, Tzero, A, Real.norm_eq_abs, abs_of_nonneg hFine] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sub_le_beta
        H 2 specialUnitaryTwoWilsonRankPositive 0 fine (by norm_num) hFine)
  have hm : 0 < m :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos H fine
  have hScale : 2 * ‖T‖⁻¹ ≤ 2 * m⁻¹ :=
    mul_le_mul_of_nonneg_left hInv (by norm_num)
  have hRawNonneg : 0 ≤ ‖T - Tzero‖ := norm_nonneg _
  change ‖‖T‖⁻¹ • T - Tzero‖ ≤
    physicalOriginalNormalizedTransferConstantStepBetaBudget H fine
  calc
    ‖‖T‖⁻¹ • T - Tzero‖ ≤ 2 * ‖T‖⁻¹ * ‖T - Tzero‖ :=
      p4Q2Z_normalized_clm_sub_normOneReference_le T Tzero hT hTzero
    _ ≤ (2 * m⁻¹) * ‖T - Tzero‖ :=
      mul_le_mul_of_nonneg_right hScale hRawNonneg
    _ ≤ (2 * m⁻¹) * (A * fine) :=
      mul_le_mul_of_nonneg_left hRaw (by positivity)
    _ = physicalOriginalNormalizedTransferConstantStepBetaBudget H fine := by
      dsimp [physicalOriginalNormalizedTransferConstantStepBetaBudget, m, A]
      ring

/-- Stronger than the Z1 gap-dependent estimate: the true physical
top spectral component of Haar unit is B_H(fine)-close to the Haar unit
for EVERY nonnegative fine beta, by rank-one anchoring at beta=0. -/
theorem physicalOriginalFineTopProjection_constantUnit_norm_sub_le_betaBudget
    (H : ℕ) (fine : ℝ) (hFine : 0 ≤ fine) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H 2 specialUnitaryTwoWilsonRankPositive fine hFine
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) -
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2‖ ≤
      physicalOriginalNormalizedTransferConstantStepBetaBudget H fine := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  let omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
    H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  have hUnit : ‖u‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  have hOmega : ‖omega‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
      H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  have hFixed : S omega = omega :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
      H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  have hRank :
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num) =
        InnerProductSpace.rankOne ℝ u u := by
    exact periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_zero_eq_rankOne
      H 2 specialUnitaryTwoWilsonRankPositive
  have hPerturb :
      ‖S - InnerProductSpace.rankOne ℝ u u‖ ≤
        physicalOriginalNormalizedTransferConstantStepBetaBudget H fine := by
    rw [← hRank]
    exact physicalOriginalNormalizedFineTransfer_sub_fineZero_norm_le_betaBudget H fine hFine
  have hProj :=
    p4Q2Z_realHilbert_topProjection_unit_le_rankOneDifference
      S u omega hUnit hOmega hFixed
  change ‖realHilbertTopEigenspaceProjection S u - u‖ ≤
    physicalOriginalNormalizedTransferConstantStepBetaBudget H fine
  rw [norm_sub_rev]
  exact hProj.trans hPerturb

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
