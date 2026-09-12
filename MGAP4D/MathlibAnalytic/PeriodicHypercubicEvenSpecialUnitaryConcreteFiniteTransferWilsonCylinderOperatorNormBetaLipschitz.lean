import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderOperatorNormBetaDifferentiability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section

set_option maxHeartbeats 2000000

local instance wilsonCylinderOperatorNormBetaLipschitzSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance wilsonCylinderOperatorNormBetaLipschitzSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance wilsonCylinderOperatorNormBetaLipschitzSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance wilsonCylinderOperatorNormBetaLipschitzSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance wilsonCylinderOperatorNormBetaLipschitzSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance wilsonCylinderOperatorNormBetaLipschitzSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance wilsonCylinderOperatorNormBetaLipschitzSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

private theorem wilsonCylinderOperatorNormBetaLipschitz_endpointProduct_integrable
    (H N : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let n := periodicHypercubicEvenPositiveHalfCylinderSlabCount H
  have hzero : MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        path (0 : Fin (n + 1))) pathMu mu := by
    simpa [pathMu, mu, n,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (n + 1) => mu) (0 : Fin (n + 1)))
  have hlast : MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        path (Fin.last n)) pathMu mu := by
    simpa [pathMu, mu, n,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (n + 1) => mu) (Fin.last n))
  have hf2 : MemLp
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0)) 2 pathMu := by
    simpa [Function.comp_def, n] using
      (Lp.memLp (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)).comp_measurePreserving
        hzero
  have hg2 : MemLp
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last n))) 2 pathMu := by
    simpa [Function.comp_def, n] using
      (Lp.memLp (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)).comp_measurePreserving
        hlast
  rw [← memLp_one_iff_integrable]
  simpa [n] using hg2.mul' hf2

private theorem wilsonCylinderOperatorNormBetaLipschitz_endpointIntegrand_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  have hbase : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathMu := by
    simpa [pathMu] using
      wilsonCylinderOperatorNormBetaLipschitz_endpointProduct_integrable H N f g
  have hKmeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta)
      pathMu :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable
      H N beta).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathMu := by
    have hm := hbase.aestronglyMeasurable.mul hKmeas
    simpa [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using hm
  apply hbase.mono hmeas
  filter_upwards with path
  rw [show
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) =
      ((f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path by ring,
    norm_mul]
  have hKnorm :
      ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path‖ ≤ 1 := by
    simpa [Real.norm_eq_abs] using
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
        H N hN beta hbeta path)
  exact mul_le_of_le_one_right (norm_nonneg _) hKnorm

/-- Uniform matrix-coefficient Lipschitz estimate for the complete positive-half
physical transfer operator on the nonnegative Wilson-coupling half-line. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator_sub_inner_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    ‖inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
            H N hN gamma hgamma -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
            H N hN beta hbeta) f) g‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N * ‖gamma - beta‖ * ‖f‖ * ‖g‖ := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let B := C * ‖gamma - beta‖
  let base := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  let F := fun t : ℝ =>
    fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N t path *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  let D := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    F gamma path - F beta path
  have hFgamma : Integrable (F gamma) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderOperatorNormBetaLipschitz_endpointIntegrand_integrable
        H N hN gamma hgamma f g
  have hFbeta : Integrable (F beta) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderOperatorNormBetaLipschitz_endpointIntegrand_integrable
        H N hN beta hbeta f g
  have hD : Integrable D pathMu := by
    simpa [D] using hFgamma.sub hFbeta
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderOperatorNormBetaLipschitz_endpointProduct_integrable H N f g
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg
        H N
  have hB : 0 ≤ B := by
    simpa [B] using mul_nonneg hC (norm_nonneg (gamma - beta))
  have hdom : Integrable (fun path => B * |base path|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul B
  have hpoint : ∀ path, ‖D path‖ ≤ B * |base path| := by
    intro path
    have hK :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_norm_sub_le
        H N hN beta gamma hbeta hgamma path
    change
      |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) -
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))| ≤
        B * |base path|
    rw [show
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) -
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) =
        base path *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path -
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path) by
          simp [base]
          ring,
      abs_mul]
    have hK' :
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path -
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path| ≤ B := by
      simpa [Real.norm_eq_abs, B, C] using hK
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left hK' (abs_nonneg (base path))
  change
    ‖inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN gamma hgamma f -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta f) g‖ ≤ _
  rw [show
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN gamma hgamma f -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta f) g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN gamma hgamma f) g -
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta f) g from
    inner_sub_left (𝕜 := ℝ) _ _ _]
  rw [← periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude_eq_physicalTransfer_inner
      H N hN gamma hgamma f g]
  rw [← periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude_eq_physicalTransfer_inner
      H N hN beta hbeta f g]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude
  change ‖(∫ path, F gamma path ∂pathMu) - (∫ path, F beta path ∂pathMu)‖ ≤ _
  rw [← integral_sub hFgamma hFbeta]
  change ‖∫ path, D path ∂pathMu‖ ≤ _
  have hint := norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall hpoint)
  calc
    ‖∫ path, D path ∂pathMu‖ ≤ ∫ path, B * |base path| ∂pathMu := hint
    _ = B * (∫ path, |base path| ∂pathMu) := by
      exact integral_const_mul B (fun path => |base path|)
    _ ≤ B * (‖f‖ * ‖g‖) := by
      apply mul_le_mul_of_nonneg_left _ hB
      simpa [base, pathMu] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderEndpointProduct_integral_abs_le
          H N f g
    _ = periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N * ‖gamma - beta‖ * ‖f‖ * ‖g‖ := by
      simp [B, C]
      ring

/-- Pointwise operator Lipschitz estimate obtained from the matrix-coefficient
bound by testing against the image vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator_sub_apply_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    ‖(periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta) f‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N * ‖gamma - beta‖) * ‖f‖ := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
        H N hN gamma hgamma -
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
        H N hN beta hbeta
  let B :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
      H N * ‖gamma - beta‖
  have hC : 0 ≤ periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hB : 0 ≤ B := by
    simpa [B] using mul_nonneg hC (norm_nonneg (gamma - beta))
  have hinner :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator_sub_inner_norm_le
      H N hN beta hbeta gamma hgamma f (D f)
  have hsq : ‖D f‖ ^ 2 ≤ B * ‖f‖ * ‖D f‖ := by
    rw [← real_inner_self_eq_norm_sq]
    exact (le_abs_self _).trans (by simpa [D, B, mul_assoc] using hinner)
  change ‖D f‖ ≤ B * ‖f‖
  by_cases hz : ‖D f‖ = 0
  · rw [hz]
    exact mul_nonneg hB (norm_nonneg f)
  have hpos : 0 < ‖D f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have hfnonneg : 0 ≤ ‖f‖ := norm_nonneg _
  nlinarith

/-- Global operator-norm Lipschitz estimate for the complete positive-half
physical transfer operator on all nonnegative Wilson couplings. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator_norm_sub_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N * ‖gamma - beta‖ := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
        H N hN gamma hgamma -
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
        H N hN beta hbeta
  let B :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
      H N * ‖gamma - beta‖
  have hC : 0 ≤ periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hB : 0 ≤ B := by
    simpa [B] using mul_nonneg hC (norm_nonneg (gamma - beta))
  change ‖D‖ ≤ B
  apply ContinuousLinearMap.opNorm_le_bound D hB
  intro f
  simpa [D, B] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator_sub_apply_norm_le
      H N hN beta hbeta gamma hgamma f

/-- The same global Lipschitz estimate expressed on the genuine nonnegative
Wilson-coupling subtype used by the differentiability layer. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily_norm_sub_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN gamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN beta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N * ‖gamma.1 - beta.1‖ := by
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator_norm_sub_le
      H N hN beta.1 beta.2 gamma.1 gamma.2

/-- Operator-norm continuity of the physical transfer family, stated as
convergence of the scalar operator-norm difference so no extra topology on the
operator carrier is needed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily_operatorNormDifference_tendsto_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    Tendsto
      (fun gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling =>
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN gamma -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN beta‖)
      (𝓝 beta)
      (𝓝 0) := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  rw [Metric.tendsto_nhds_nhds]
  intro epsilon hepsilon
  by_cases hCzero : C = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro gamma hdist
    have hbound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily_norm_sub_le
        H N hN beta gamma
    change
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN gamma -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN beta‖ ≤
        C * ‖gamma.1 - beta.1‖ at hbound
    rw [hCzero, zero_mul] at hbound
    have hnonneg := ContinuousLinearMap.opNorm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN gamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN beta)
    have hzero :
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN gamma -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN beta‖ = 0 :=
      le_antisymm hbound hnonneg
    rw [hzero]
    simpa using hepsilon
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    refine ⟨epsilon / C, div_pos hepsilon hCpos, ?_⟩
    intro gamma hdist
    have hdist' : ‖gamma.1 - beta.1‖ < epsilon / C := by
      simpa [Real.dist_eq] using hdist
    have hbound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily_norm_sub_le
        H N hN beta gamma
    change
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN gamma -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN beta‖ ≤
        C * ‖gamma.1 - beta.1‖ at hbound
    have hmul : C * ‖gamma.1 - beta.1‖ < C * (epsilon / C) :=
      mul_lt_mul_of_pos_left hdist' hCpos
    have hcancel : C * (epsilon / C) = epsilon := by
      field_simp [ne_of_gt hCpos]
    have hlt :
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN gamma -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN beta‖ < epsilon :=
      hbound.trans_lt (by simpa [hcancel] using hmul)
    have hnonneg := ContinuousLinearMap.opNorm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN gamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN beta)
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hlt

end

end MathlibAnalytic
end MGAP4D