import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalNormalizedMarginCouplingWindowV5_PZ37AIX

/-!
# P4-Q2-PZ37AIY — true Haar-L² nonvanishing of the normalized original source

The ORIGINAL finite-volume SU(2) Wilson one-slab physical transfer P, its
original centered signed ZW Gauss-law physical source f0, both endpoint
spatial halfweights, genuine Haar probability and the EXISTING normalized
physical operator N = P / ||P|| are kept exactly unchanged.

AIX established that the original AIG *margin certificate*, when normalized
by the genuine physical norm, can shrink with volume. This new leaf tests
the ACTUAL image in the original physical L² space, without identifying
its norm with the pointwise certificate or with a spectral gap.

The original AIT full-margin negative region has genuine Haar mass >= 1/2
for 0 < beta <= 1 + p_H/4. By AIW, the original continuous normalized
transfer integral is Haar-a.e. the EXISTING normalized physical operator
applied to the same ZW source. Were that L² output zero, the continuous
representative would vanish a.e.; a positive-measure strict negative
region would be impossible. This proves a true finite-volume nonzero
physical L² amplitude, NOT a uniform positive lower bound.

Additionally, the exact norm ratio ||N f0|| = ||P f0||/||P|| and the
norm-one L² contraction ||N f0|| <= ||f0|| hold for all beta>=0.
The original physical Hilbert spaces continue to depend on H.

We neither assume that the original ZW source lies in the top-eigenspace
orthogonal complement nor claim an excitation-sector spectral statement,
a uniform L² amplitude floor, a Hamiltonian gap or a continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped Topology Classical InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIY_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIY_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIY_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIY_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIY_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "CfgY" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muY" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "PhysY" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "fY" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "PY" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "NY" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "uY" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mY" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H

/-- True Hilbert-space norm of the original normalized ZW source image
is exactly the true unnormalized physical-source image norm divided by the
existing physical operator norm; no replacement operator is introduced. -/
theorem p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_eq_ratio
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖NY beta hbeta fY‖ =
      ‖PY beta hbeta fY‖ / ‖PY beta hbeta‖ := by
  let P := PY beta hbeta
  let f := fY
  change ‖‖P‖⁻¹ • P f‖ = ‖P f‖ / ‖P‖
  calc
    ‖‖P‖⁻¹ • P f‖ = ‖(‖P‖⁻¹ : ℝ)‖ * ‖P f‖ := norm_smul _ _
    _ = ‖P f‖ / ‖P‖ := by
      rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg P)]
      ring

/-- Norm-one of the EXISTING normalized physical operator provides a
real Haar-L² amplitude upper bound in terms of the unchanged source norm. -/
theorem p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_le_input
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖NY beta hbeta fY‖ ≤ ‖fY‖ := by
  calc
    ‖NY beta hbeta fY‖ ≤ ‖NY beta hbeta‖ * ‖fY‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖fY‖ := by
      rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
        H 2 (by norm_num) beta hbeta]
      ring

/-- A positive-measure strict negative region for the ORIGINAL continuous
normalized transfer representative prohibits the ACTUAL normalized physical
Haar-L² image from being the zero L² class. This is the a.e.-to-L² descent
condition, not a pointwise assertion about arbitrary L² representatives. -/
theorem p4Q2PZ37AIY_originalNormalizedPhysicalSource_ne_zero_of_regionMeasure
    (beta : ℝ) (hbeta : 0 < beta)
    (hmeasure : muY {B : CfgY | uY beta hbeta.le B < -(mY beta hbeta.le)} ≠ 0) :
    NY beta hbeta.le fY ≠ 0 := by
  intro hzero
  have hLpZero : ((NY beta hbeta.le fY : PhysY) : Lp ℝ 2 muY) = 0 := by
    exact congrArg (fun g : PhysY => (g : Lp ℝ 2 muY)) hzero
  have hAEzero :
      (fun B : CfgY => (((NY beta hbeta.le fY : PhysY) : Lp ℝ 2 muY) B)) =ᵐ[muY]
        (fun _ => (0 : ℝ)) :=
    (Lp.eq_zero_iff_ae_eq_zero).mp hLpZero
  have hBridge :=
    p4Q2PZ37AIW_originalNormalizedSourceTransfer_coeFn H beta hbeta.le
  have hAEsource :
      uY beta hbeta.le =ᵐ[muY] (fun _ : CfgY => (0 : ℝ)) :=
    hBridge.symm.trans hAEzero
  have hMargin : 0 < mY beta hbeta.le :=
    p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos H beta hbeta
  have hAEoutside :
      ∀ᵐ B : CfgY ∂muY, B ∉ {B : CfgY |
        uY beta hbeta.le B < -(mY beta hbeta.le)} := by
    filter_upwards [hAEsource] with B hB
    rw [hB]
    linarith
  exact hmeasure ((measure_eq_zero_iff_ae_notMem).2 hAEoutside)

/-- The AIT half-Haar theorem for every finite original H and each
0<beta<=1+p_H/4 supplies the required genuinely non-null negative set.
This proves nonzero L² output without an externally postulated witness. -/
theorem p4Q2PZ37AIY_originalNormalizedPhysicalSource_ne_zero_of_halfHaar
    (beta : ℝ) (hbeta : 0 < beta)
    (hEnd : beta ≤ p4Q2PZ37AIT_volumeGrowingCouplingCutoff H) :
    NY beta hbeta.le fY ≠ 0 := by
  have hHalf :
      (1 / 2 : ℝ) ≤ Measure.real muY
        {B : CfgY | uY beta hbeta.le B < -(mY beta hbeta.le)} := by
    rw [p4Q2PZ37AIW_originalNormalizedNegativeRegion_eq_original H beta hbeta.le]
    exact p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half
      H beta hbeta hEnd
  have hmeasure :
      muY {B : CfgY | uY beta hbeta.le B < -(mY beta hbeta.le)} ≠ 0 := by
    intro hz
    have hr : Measure.real muY
        {B : CfgY | uY beta hbeta.le B < -(mY beta hbeta.le)} = 0 := by
      simp [Measure.real, hz]
    linarith
  exact p4Q2PZ37AIY_originalNormalizedPhysicalSource_ne_zero_of_regionMeasure
    H beta hbeta hmeasure

/-- The actual physical Haar-L² image is strictly nonzero in norm in the
entire original finite-volume certified coupling interval. The interval
endpoint depends on H; no common Hilbert space is assumed. -/
theorem p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_of_halfHaar
    (beta : ℝ) (hbeta : 0 < beta)
    (hEnd : beta ≤ p4Q2PZ37AIT_volumeGrowingCouplingCutoff H) :
    0 < ‖NY beta hbeta.le fY‖ :=
  norm_pos_iff.mpr
    (p4Q2PZ37AIY_originalNormalizedPhysicalSource_ne_zero_of_halfHaar
      H beta hbeta hEnd)

/-- A common finite-volume interval 0<beta<=7 of genuinely nonzero normalized
physical ZW-source L² images, with no condition on sufficiently large H. -/
theorem p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_le_seven
    (beta : ℝ) (hbeta : 0 < beta) (hSeven : beta ≤ 7) :
    0 < ‖NY beta hbeta.le fY‖ :=
  p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_of_halfHaar
    H beta hbeta
    (hSeven.trans (p4Q2PZ37AIT_volumeGrowingCutoff_ge_seven H))

/-- The true normalized source L² norm is positive at the ACTUAL
volume-growing AIT endpoint, for every original finite H. -/
theorem p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_at_cutoff :
    0 < ‖NY (p4Q2PZ37AIT_volumeGrowingCouplingCutoff H)
        (p4Q2PZ37AIT_volumeGrowingCouplingCutoff_pos H).le fY‖ :=
  p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_of_halfHaar
    H (p4Q2PZ37AIT_volumeGrowingCouplingCutoff H)
    (p4Q2PZ37AIT_volumeGrowingCouplingCutoff_pos H) le_rfl

/-- For any fixed positive coupling, eventually every original finite-volume
normalized ZW physical source has genuine nonzero L² output. This concerns
nonzeroness, not a volume-uniform lower amplitude floor. -/
theorem p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_eventually
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ N : ℕ, ∀ K : ℕ, N ≤ K →
      0 < ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        K 2 (by norm_num) beta hbeta.le
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection K)‖ := by
  obtain ⟨N, hN⟩ := p4Q2PZ37AIT_eventually_le_volumeGrowingCutoff beta
  exact ⟨N, fun K hK =>
    p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_of_halfHaar
      K beta hbeta (hN K hK)⟩

/-- At every certified finite-volume coupling, the ACTUAL normalized ZW
L² amplitude is positive but does not exceed the original physical source
L² norm. No lower bound independent of H is asserted. -/
theorem p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_le_source
    (beta : ℝ) (hbeta : 0 < beta)
    (hEnd : beta ≤ p4Q2PZ37AIT_volumeGrowingCouplingCutoff H) :
    0 < ‖NY beta hbeta.le fY‖ ∧
      ‖NY beta hbeta.le fY‖ ≤ ‖fY‖ :=
  ⟨p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_of_halfHaar
      H beta hbeta hEnd,
   p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_le_input
      H beta hbeta.le⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Every one of the nine new theorems has an independent actual axiom print. -/
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_eq_ratio
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_le_input
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIY_originalNormalizedPhysicalSource_ne_zero_of_regionMeasure
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIY_originalNormalizedPhysicalSource_ne_zero_of_halfHaar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_of_halfHaar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_le_seven
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_at_cutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_eventually
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_le_source
