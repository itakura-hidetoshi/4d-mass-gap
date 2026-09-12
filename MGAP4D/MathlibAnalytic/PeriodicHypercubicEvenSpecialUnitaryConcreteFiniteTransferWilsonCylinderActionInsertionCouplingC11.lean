import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderOperatorNormBetaLipschitz
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section

set_option maxHeartbeats 2000000

local instance wilsonCylinderActionInsertionCouplingC11SpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance wilsonCylinderActionInsertionCouplingC11SpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance wilsonCylinderActionInsertionCouplingC11SpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance wilsonCylinderActionInsertionCouplingC11SpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance wilsonCylinderActionInsertionCouplingC11SpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance wilsonCylinderActionInsertionCouplingC11SpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance wilsonCylinderActionInsertionCouplingC11SpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

private theorem wilsonCylinderActionInsertionCouplingC11_endpointProduct_integrable
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

private theorem wilsonCylinderActionInsertionCouplingC11_actionIntegrand_integrable
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
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
            H N path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  have hbase : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathMu := by
    simpa [pathMu] using
      wilsonCylinderActionInsertionCouplingC11_endpointProduct_integrable H N f g
  have hKmeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta)
      pathMu :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable
      H N beta).aestronglyMeasurable
  have hSmeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N)
      pathMu :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_measurable
      H N).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
            H N path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathMu := by
    have h := (hbase.aestronglyMeasurable.mul hKmeas).mul hSmeas
    simpa [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using h
  have hdom : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        C * |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul C
  apply hdom.mono' hmeas
  filter_upwards with path
  have hK :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
      H N hN beta hbeta path
  have hS :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound
      H N path
  change
    |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))| ≤
      C * |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))|
  rw [show
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) =
      ((f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) *
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path) by ring,
    abs_mul, abs_mul]
  have hKS :
      |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path| *
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ≤ C := by
    calc
      _ ≤ 1 * C := mul_le_mul hK (by simpa [Real.norm_eq_abs, C] using hS)
        (abs_nonneg _) (by positivity)
      _ = C := by ring
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left hKS
      (abs_nonneg
        ((f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))))

/-- Sharp matrix-coefficient Lipschitz estimate for the complete physical
Wilson-action insertion operator.  The coefficient is C^2 because the kernel
variation contributes one factor C and the inserted path action contributes the
second factor C. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_sub_inner_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    ‖inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
            H N hN gamma hgamma -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
            H N hN beta hbeta) f) g‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ 2 * ‖gamma - beta‖ * ‖f‖ * ‖g‖ := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let B := C ^ 2 * ‖gamma - beta‖
  let base := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  let F := fun t : ℝ =>
    fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N t path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  let D := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    F gamma path - F beta path
  have hFgamma : Integrable (F gamma) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderActionInsertionCouplingC11_actionIntegrand_integrable
        H N hN gamma hgamma f g
  have hFbeta : Integrable (F beta) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderActionInsertionCouplingC11_actionIntegrand_integrable
        H N hN beta hbeta f g
  have hD : Integrable D pathMu := by
    simpa [D] using hFgamma.sub hFbeta
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderActionInsertionCouplingC11_endpointProduct_integrable H N f g
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg
        H N
  have hB : 0 ≤ B := by
    simpa [B] using mul_nonneg (sq_nonneg C) (norm_nonneg (gamma - beta))
  have hdom : Integrable (fun path => B * |base path|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul B
  have hpoint : ∀ path, ‖D path‖ ≤ B * |base path| := by
    intro path
    have hK :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_norm_sub_le
        H N hN beta gamma hbeta hgamma path
    have hS :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound
        H N path
    have hK' :
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path -
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path| ≤
        C * ‖gamma - beta‖ := by
      simpa [Real.norm_eq_abs, C] using hK
    have hS' :
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ≤ C := by
      simpa [Real.norm_eq_abs, C] using hS
    change |F gamma path - F beta path| ≤ B * |base path|
    rw [show
      F gamma path - F beta path =
        base path *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path -
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path by
        simp [F, base]
        ring,
      abs_mul, abs_mul]
    calc
      |base path| *
          |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path -
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path| *
          |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ≤
        |base path| * (C * ‖gamma - beta‖) *
          |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hK' (abs_nonneg (base path)))
          (abs_nonneg _)
      _ ≤ |base path| * (C * ‖gamma - beta‖) * C := by
        exact mul_le_mul_of_nonneg_left hS'
          (mul_nonneg (abs_nonneg (base path))
            (mul_nonneg hC (norm_nonneg (gamma - beta))))
      _ = B * |base path| := by
        simp [B]
        ring
  change
    ‖inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN gamma hgamma f -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN beta hbeta f) g‖ ≤ _
  rw [show
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN gamma hgamma f -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN beta hbeta f) g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN gamma hgamma f) g -
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN beta hbeta f) g from
    inner_sub_left (𝕜 := ℝ) _ _ _]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_inner_eq_pathActionIntegral
      H N hN gamma hgamma f g]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_inner_eq_pathActionIntegral
      H N hN beta hbeta f g]
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
          H N ^ 2 * ‖gamma - beta‖ * ‖f‖ * ‖g‖ := by
      simp [B, C]
      ring

/-- Pointwise Lipschitz estimate for the complete physical Wilson-action
insertion operator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_sub_apply_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    ‖(periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN beta hbeta) f‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ 2 * ‖gamma - beta‖) * ‖f‖ := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
        H N hN gamma hgamma -
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
        H N hN beta hbeta
  let B :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
      H N ^ 2 * ‖gamma - beta‖
  have hB : 0 ≤ B := by
    exact mul_nonneg (sq_nonneg _) (norm_nonneg _)
  have hinner :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_sub_inner_norm_le
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

/-- Sharp global operator-norm Lipschitz estimate for the complete physical
Wilson-action insertion operator on all nonnegative couplings. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_norm_sub_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ 2 * ‖gamma - beta‖ := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
        H N hN gamma hgamma -
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
        H N hN beta hbeta
  let B :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
      H N ^ 2 * ‖gamma - beta‖
  have hB : 0 ≤ B := by
    exact mul_nonneg (sq_nonneg _) (norm_nonneg _)
  change ‖D‖ ≤ B
  apply ContinuousLinearMap.opNorm_le_bound D hB
  intro f
  simpa [D, B] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_sub_apply_norm_le
      H N hN beta hbeta gamma hgamma f

/-- The same insertion-operator Lipschitz estimate on the genuine nonnegative
Wilson-coupling subtype. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily_norm_sub_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily H N hN gamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily H N hN beta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ 2 * ‖gamma.1 - beta.1‖ := by
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_norm_sub_le
      H N hN beta.1 beta.2 gamma.1 gamma.2

/-- Operator-norm C^{1,1} certificate for the physical transfer family on the
genuine nonnegative Wilson-coupling half-line.  The first conjunct is the
already-established operator-norm derivative statement with derivative
`-O_cyl,beta`, expressed by convergence of the scalar difference-quotient error.
The second conjunct proves that this derivative field is globally Lipschitz,
with sharp coefficient C^2; changing O to -O does not change the norm distance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily_operatorNorm_C1_1_certificate
    (H N : ℕ)
    (hN : 0 < N) :
    (∀ beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling,
      Tendsto
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm
          H N hN beta)
        (𝓝 beta)
        (𝓝 0)) ∧
    (∀ beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily H N hN gamma -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily H N hN beta‖ ≤
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 2 * ‖gamma.1 - beta.1‖) := by
  constructor
  · intro beta
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm_tendsto_zero
        H N hN beta
  · intro beta gamma
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily_norm_sub_le
        H N hN beta gamma

end

end MathlibAnalytic
end MGAP4D
