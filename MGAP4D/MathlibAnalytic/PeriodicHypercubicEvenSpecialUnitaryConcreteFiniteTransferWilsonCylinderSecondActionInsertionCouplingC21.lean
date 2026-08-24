import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderActionInsertionCouplingC11
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section

set_option maxHeartbeats 2000000

local instance wilsonCylinderSecondActionInsertionCouplingC21SpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance wilsonCylinderSecondActionInsertionCouplingC21SpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance wilsonCylinderSecondActionInsertionCouplingC21SpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance wilsonCylinderSecondActionInsertionCouplingC21SpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance wilsonCylinderSecondActionInsertionCouplingC21SpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance wilsonCylinderSecondActionInsertionCouplingC21SpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance wilsonCylinderSecondActionInsertionCouplingC21SpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

private theorem wilsonCylinderSecondActionInsertionCouplingC21_endpointProduct_integrable
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

private theorem wilsonCylinderSecondActionInsertionCouplingC21_kernel_action_sq_abs_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2| ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ 2 := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let S := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hK :
      |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path| ≤ 1 :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
      H N hN beta hbeta path
  have hS : |S| ≤ C := by
    simpa [S, C, Real.norm_eq_abs] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound
        H N path
  have hSsq : |S| ^ 2 ≤ C ^ 2 := by
    nlinarith [abs_nonneg S]
  rw [abs_mul, abs_pow]
  calc
    |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta path| * |S| ^ 2 ≤ 1 * C ^ 2 :=
      mul_le_mul hK hSsq (sq_nonneg _) zero_le_one
    _ = C ^ 2 := by ring

private theorem wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable
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
            H N path ^ 2 *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let base := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_endpointProduct_integrable H N f g
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
            H N path ^ 2 *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathMu := by
    have h := ((hbase.aestronglyMeasurable.mul hKmeas).mul hSmeas).mul hSmeas
    simpa [base, pow_two, Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using h
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hdom : Integrable (fun path => C ^ 2 * |base path|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul (C ^ 2)
  apply hdom.mono' hmeas
  filter_upwards with path
  have hfac := wilsonCylinderSecondActionInsertionCouplingC21_kernel_action_sq_abs_le
    H N hN beta hbeta path
  change
    |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))| ≤
      C ^ 2 * |base path|
  rw [show
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) =
      base path *
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2) by
          simp [base]
          ring,
    abs_mul]
  have hfac' :
      |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2| ≤
        C ^ 2 := by
    simpa [C] using hfac
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left hfac' (abs_nonneg (base path))

/-- Literal second Wilson-action insertion on the common positive-half path carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
    (H N : ℕ)
    (beta : ℝ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) : ℝ :=
  ∫ path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N,
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta path *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
        H N path ^ 2 *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
    ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)

/-- The literal second-insertion bilinear form is uniformly bounded by C^2. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude_abs_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
        H N beta f g| ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 2 * ‖f‖ * ‖g‖ := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let base := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  let F := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_endpointProduct_integrable H N f g
  have hF : Integrable F pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable
        H N hN beta hbeta f g
  have hdom : Integrable (fun path => C ^ 2 * |base path|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul (C ^ 2)
  have hpoint : ∀ path, ‖F path‖ ≤ C ^ 2 * |base path| := by
    intro path
    have hfac := wilsonCylinderSecondActionInsertionCouplingC21_kernel_action_sq_abs_le
      H N hN beta hbeta path
    change
      |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))| ≤
        C ^ 2 * |base path|
    rw [show
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) =
        base path *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2) by
            simp [base]
            ring,
      abs_mul]
    have hfac' :
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2| ≤
          C ^ 2 := by
      simpa [C] using hfac
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left hfac' (abs_nonneg (base path))
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
  change |∫ path, F path ∂pathMu| ≤ _
  have hint := norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall hpoint)
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ path, F path ∂pathMu‖ ≤ ∫ path, C ^ 2 * |base path| ∂pathMu := hint
    _ = C ^ 2 * (∫ path, |base path| ∂pathMu) := by
      exact integral_const_mul (C ^ 2) (fun path => |base path|)
    _ ≤ C ^ 2 * (‖f‖ * ‖g‖) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      simpa [base, pathMu] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderEndpointProduct_integral_abs_le
          H N f g
    _ = periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 2 * ‖f‖ * ‖g‖ := by
      simp [C]
      ring

private noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionLinearBilin
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    LinearMap.BilinForm ℝ
      (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
  LinearMap.mk₂ ℝ
    (fun f g =>
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
        H N beta f g)
    (by
      intro f₁ f₂ g
      let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
      let F := fun f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N =>
        fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      have h1 : Integrable (F f₁) pathMu := by
        simpa [F, pathMu] using
          wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable
            H N hN beta hbeta f₁ g
      have h2 : Integrable (F f₂) pathMu := by
        simpa [F, pathMu] using
          wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable
            H N hN beta hbeta f₂ g
      unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
      change (∫ path, F (f₁ + f₂) path ∂pathMu) =
        (∫ path, F f₁ path ∂pathMu) + (∫ path, F f₂ path ∂pathMu)
      rw [← integral_add h1 h2]
      apply integral_congr_ae
      filter_upwards with path
      simp [F]
      ring)
    (by
      intro r f g
      let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
      let F := fun f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N =>
        fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
      change (∫ path, F (r • f) path ∂pathMu) = r • (∫ path, F f path ∂pathMu)
      rw [show (fun path => F (r • f) path) = fun path => r * F f path by
        funext path
        simp [F]
        ring]
      simpa [smul_eq_mul] using integral_const_mul r (F f))
    (by
      intro f g₁ g₂
      let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
      let F := fun g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N =>
        fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      have h1 : Integrable (F g₁) pathMu := by
        simpa [F, pathMu] using
          wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable
            H N hN beta hbeta f g₁
      have h2 : Integrable (F g₂) pathMu := by
        simpa [F, pathMu] using
          wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable
            H N hN beta hbeta f g₂
      unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
      change (∫ path, F (g₁ + g₂) path ∂pathMu) =
        (∫ path, F g₁ path ∂pathMu) + (∫ path, F g₂ path ∂pathMu)
      rw [← integral_add h1 h2]
      apply integral_congr_ae
      filter_upwards with path
      simp [F]
      ring)
    (by
      intro r f g
      let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
      let F := fun g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N =>
        fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
      change (∫ path, F (r • g) path ∂pathMu) = r • (∫ path, F g path ∂pathMu)
      rw [show (fun path => F (r • g) path) = fun path => r * F g path by
        funext path
        simp [F]
        ring]
      simpa [smul_eq_mul] using integral_const_mul r (F g))

/-- Continuous real bilinear form represented by the literal K_beta S_path^2 insertion. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionBilin
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ] ℝ :=
  (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionLinearBilin
    H N hN beta hbeta).mkContinuous₂
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ 2)
      (by
        intro f g
        simpa [Real.norm_eq_abs, mul_assoc] using
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude_abs_le
            H N hN beta hbeta f g)

/-- Genuine second Wilson-action insertion operator on the physical Gauss-law Hilbert space. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  InnerProductSpace.continuousLinearMapOfBilin
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionBilin
      H N hN beta hbeta)

/-- Matrix coefficients of the second physical insertion operator are exactly the literal
positive-half product-Haar integral with S_path^2 inserted. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_inner_eq_pathActionSquareIntegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN beta hbeta f) g =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
        H N beta f g := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

/-- Pointwise norm control for the genuine second-insertion operator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_apply_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
        H N hN beta hbeta f‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ 2 * ‖f‖ := by
  let O2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
      H N hN beta hbeta
  let B :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ 2
  have hB : 0 ≤ B := by positivity
  have hinner :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude_abs_le
      H N hN beta hbeta f (O2 f)
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_inner_eq_pathActionSquareIntegral
      H N hN beta hbeta f (O2 f)] at hinner
  have hsq : ‖O2 f‖ ^ 2 ≤ B * ‖f‖ * ‖O2 f‖ := by
    rw [← real_inner_self_eq_norm_sq]
    exact (le_abs_self _).trans (by simpa [O2, B, mul_assoc] using hinner)
  change ‖O2 f‖ ≤ B * ‖f‖
  by_cases hz : ‖O2 f‖ = 0
  · rw [hz]
    exact mul_nonneg hB (norm_nonneg f)
  have hpos : 0 < ‖O2 f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have hfnonneg : 0 ≤ ‖f‖ := norm_nonneg _
  nlinarith

/-- Uniform operator norm bound for the second physical Wilson-action insertion. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
        H N hN beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ 2 := by
  let O2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
      H N hN beta hbeta
  let B :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ 2
  change ‖O2‖ ≤ B
  apply ContinuousLinearMap.opNorm_le_bound O2 (by positivity)
  intro f
  simpa [O2, B] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_apply_norm_le
      H N hN beta hbeta f

/-- The K_beta S_path insertion has a quadratic Taylor remainder whose coefficient is C^3. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionInsertion_quadraticRemainder
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path +
        (gamma - beta) *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2)‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 3 * ‖gamma - beta‖ ^ 2 := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let S := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path
  let K := fun t : ℝ =>
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N t path
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hS : ‖S‖ ≤ C := by
    simpa [S, C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound
        H N path
  have hR :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_quadraticRemainder
      H N hN beta gamma hbeta hgamma path
  change ‖K gamma * S - K beta * S + (gamma - beta) * (K beta * S ^ 2)‖ ≤
    C ^ 3 * ‖gamma - beta‖ ^ 2
  rw [show
    K gamma * S - K beta * S + (gamma - beta) * (K beta * S ^ 2) =
      S * (K gamma - K beta + (gamma - beta) * (K beta * S)) by ring,
    norm_mul]
  have hR' :
      ‖K gamma - K beta + (gamma - beta) * (K beta * S)‖ ≤
        C ^ 2 * ‖gamma - beta‖ ^ 2 := by
    simpa [K, S, C] using hR
  calc
    ‖S‖ * ‖K gamma - K beta + (gamma - beta) * (K beta * S)‖ ≤
      C * (C ^ 2 * ‖gamma - beta‖ ^ 2) :=
        mul_le_mul hS hR' (norm_nonneg _) hC
    _ = C ^ 3 * ‖gamma - beta‖ ^ 2 := by ring

/-- Operator remainder for differentiating the first Wilson-action insertion family. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
      H N hN gamma hgamma -
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
      H N hN beta hbeta +
    (gamma - beta) •
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
        H N hN beta hbeta

private theorem wilsonCylinderSecondActionInsertionCouplingC21_firstIntegrand_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let base := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_endpointProduct_integrable H N f g
  have hKmeas :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable
      H N beta).aestronglyMeasurable
  have hSmeas :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_measurable
      H N).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathMu := by
    have h := (hbase.aestronglyMeasurable.mul hKmeas).mul hSmeas
    simpa [base, Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using h
  have hdom : Integrable (fun path => C * |base path|) pathMu := by
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
      C * |base path|
  rw [show
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) =
      base path *
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path) by
          simp [base]
          ring,
    abs_mul, abs_mul]
  have hKS :
      |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path| *
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ≤ C := by
    calc
      _ ≤ 1 * C := mul_le_mul hK (by simpa [Real.norm_eq_abs, C] using hS)
        (abs_nonneg _) (by positivity)
      _ = C := by ring
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hKS (abs_nonneg (base path))

/-- Matrix coefficients of the first-insertion remainder are the literal pathwise
quadratic remainder for K_beta S_path. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator_inner_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
          H N hN beta hbeta gamma hgamma f) g =
      ∫ path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N,
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path -
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path +
            (gamma - beta) *
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
                periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2)) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let F := fun t : ℝ =>
    fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N t path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  let A2 := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hFgamma : Integrable (F gamma) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_firstIntegrand_integrable
        H N hN gamma hgamma f g
  have hFbeta : Integrable (F beta) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_firstIntegrand_integrable
        H N hN beta hbeta f g
  have hA2 : Integrable A2 pathMu := by
    simpa [A2, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable
        H N hN beta hbeta f g
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
  change inner ℝ
      ((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN gamma hgamma f -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN beta hbeta f) +
        (gamma - beta) •
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
            H N hN beta hbeta f) g = _
  rw [inner_add_left]
  rw [show inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN gamma hgamma f -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN beta hbeta f) g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN gamma hgamma f) g -
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN beta hbeta f) g from inner_sub_left (𝕜 := ℝ) _ _ _]
  have hsmul :
      inner ℝ
        ((gamma - beta) •
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
            H N hN beta hbeta f) g =
        (gamma - beta) * inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
            H N hN beta hbeta f) g := by
    simpa using
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).innerProductSpace.smul_left
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN beta hbeta f) g (gamma - beta)
  rw [hsmul]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_inner_eq_pathActionIntegral
    H N hN gamma hgamma f g]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_inner_eq_pathActionIntegral
    H N hN beta hbeta f g]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_inner_eq_pathActionSquareIntegral
    H N hN beta hbeta f g]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
  change (∫ path, F gamma path ∂pathMu) - (∫ path, F beta path ∂pathMu) +
      (gamma - beta) * (∫ path, A2 path ∂pathMu) = _
  rw [← integral_sub hFgamma hFbeta]
  rw [← integral_const_mul]
  rw [← integral_add (hFgamma.sub hFbeta) (hA2.const_mul (gamma - beta))]
  apply integral_congr_ae
  filter_upwards with path
  simp [F, A2]
  ring

/-- Matrix-coefficient quadratic remainder estimate for the first insertion family. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator_inner_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    ‖inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
          H N hN beta hbeta gamma hgamma f) g‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 3 * ‖gamma - beta‖ ^ 2 * ‖f‖ * ‖g‖ := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let B := C ^ 3 * ‖gamma - beta‖ ^ 2
  let base := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  let R := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path -
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path +
      (gamma - beta) *
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2)
  let D := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    base path * R path
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_endpointProduct_integrable H N f g
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hdom : Integrable (fun path => B * |base path|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul B
  have hpoint : ∀ path, ‖D path‖ ≤ B * |base path| := by
    intro path
    have hR :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionInsertion_quadraticRemainder
        H N hN beta gamma hbeta hgamma path
    change |base path * R path| ≤ B * |base path|
    rw [abs_mul]
    have hR' : |R path| ≤ B := by
      simpa [R, B, C, Real.norm_eq_abs] using hR
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hR' (abs_nonneg (base path))
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator_inner_eq_integral
    H N hN beta hbeta gamma hgamma f g]
  change ‖∫ path, D path ∂pathMu‖ ≤ _
  have hint := norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall hpoint)
  calc
    ‖∫ path, D path ∂pathMu‖ ≤ ∫ path, B * |base path| ∂pathMu := hint
    _ = B * (∫ path, |base path| ∂pathMu) := by
      exact integral_const_mul B (fun path => |base path|)
    _ ≤ B * (‖f‖ * ‖g‖) := by
      apply mul_le_mul_of_nonneg_left _ hB
      simpa [base, pathMu] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderEndpointProduct_integral_abs_le H N f g
    _ = periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 3 * ‖gamma - beta‖ ^ 2 * ‖f‖ * ‖g‖ := by
      simp [B, C]
      ring

/-- Pointwise quadratic remainder estimate for differentiating the first insertion operator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator_apply_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
        H N hN beta hbeta gamma hgamma f‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 3 * ‖gamma - beta‖ ^ 2) * ‖f‖ := by
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
    H N hN beta hbeta gamma hgamma
  let B := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
    H N ^ 3 * ‖gamma - beta‖ ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hinner :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator_inner_norm_le
      H N hN beta hbeta gamma hgamma f (R f)
  have hsq : ‖R f‖ ^ 2 ≤ B * ‖f‖ * ‖R f‖ := by
    rw [← real_inner_self_eq_norm_sq]
    exact (le_abs_self _).trans (by simpa [R, B, mul_assoc] using hinner)
  change ‖R f‖ ≤ B * ‖f‖
  by_cases hz : ‖R f‖ = 0
  · rw [hz]
    exact mul_nonneg hB (norm_nonneg f)
  have hpos : 0 < ‖R f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have hfnonneg : 0 ≤ ‖f‖ := norm_nonneg _
  nlinarith

/-- Operator-norm quadratic remainder for the first Wilson-action insertion family. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
        H N hN beta hbeta gamma hgamma‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 3 * ‖gamma - beta‖ ^ 2 := by
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
    H N hN beta hbeta gamma hgamma
  let B := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
    H N ^ 3 * ‖gamma - beta‖ ^ 2
  change ‖R‖ ≤ B
  apply ContinuousLinearMap.opNorm_le_bound R (by dsimp [B]; positivity)
  intro f
  simpa [R, B] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator_apply_norm_le
      H N hN beta hbeta gamma hgamma f

/-- The genuine second-insertion family on the nonnegative Wilson-coupling half-line. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily
    (H N : ℕ)
    (hN : 0 < N)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
    H N hN beta.1 beta.2

/-- Difference-quotient error for differentiating the first Wilson-action insertion family. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientError
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  (gamma.1 - beta.1)⁻¹ •
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily H N hN gamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily H N hN beta) +
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily H N hN beta

/-- Away from the base point, the first-insertion difference quotient is the quadratic
remainder divided by the coupling increment. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientError_eq_inv_smul_remainder
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling)
    (h : gamma ≠ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientError
        H N hN beta gamma =
      (gamma.1 - beta.1)⁻¹ •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
          H N hN beta.1 beta.2 gamma.1 gamma.2 := by
  have hval : gamma.1 ≠ beta.1 := by
    intro hval
    apply h
    exact Subtype.ext hval
  have hsub : gamma.1 - beta.1 ≠ 0 := sub_ne_zero.mpr hval
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientError
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
  apply ContinuousLinearMap.ext
  intro f
  change
    (gamma.1 - beta.1)⁻¹ •
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
              H N hN gamma.1 gamma.2 f -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
              H N hN beta.1 beta.2 f) +
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
            H N hN beta.1 beta.2 f =
      (gamma.1 - beta.1)⁻¹ •
        ((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
              H N hN gamma.1 gamma.2 f -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
              H N hN beta.1 beta.2 f) +
          (gamma.1 - beta.1) •
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
              H N hN beta.1 beta.2 f)
  rw [smul_add, smul_smul, inv_mul_cancel₀ hsub, one_smul]

/-- Quantitative first-insertion difference-quotient estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotient_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling)
    (h : gamma ≠ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientError
        H N hN beta gamma‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 3 * ‖gamma.1 - beta.1‖ := by
  have hval : gamma.1 ≠ beta.1 := by
    intro hval
    apply h
    exact Subtype.ext hval
  have hsub : gamma.1 - beta.1 ≠ 0 := sub_ne_zero.mpr hval
  have hnorm : ‖gamma.1 - beta.1‖ ≠ 0 := norm_ne_zero_iff.mpr hsub
  apply ContinuousLinearMap.opNorm_le_bound
    (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientError
      H N hN beta gamma)
    (by positivity)
  intro f
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientError_eq_inv_smul_remainder
    H N hN beta gamma h]
  change
    ‖(gamma.1 - beta.1)⁻¹ •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
          H N hN beta.1 beta.2 gamma.1 gamma.2 f‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 3 * ‖gamma.1 - beta.1‖) * ‖f‖
  rw [norm_smul]
  have hR :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator_apply_norm_le
      H N hN beta.1 beta.2 gamma.1 gamma.2 f
  calc
    ‖(gamma.1 - beta.1)⁻¹‖ *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
          H N hN beta.1 beta.2 gamma.1 gamma.2 f‖ ≤
      ‖(gamma.1 - beta.1)⁻¹‖ *
        ((periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
            H N ^ 3 * ‖gamma.1 - beta.1‖ ^ 2) * ‖f‖) :=
      mul_le_mul_of_nonneg_left hR (norm_nonneg _)
    _ = (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 3 * ‖gamma.1 - beta.1‖) * ‖f‖ := by
      rw [norm_inv]
      field_simp [hnorm]

/-- Total scalar norm error for the first-insertion difference quotient. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) : ℝ :=
  if gamma = beta then 0 else
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientError
        H N hN beta gamma‖

/-- Linear control of the total first-insertion difference-quotient error. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN beta gamma ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 3 * ‖gamma.1 - beta.1‖ := by
  by_cases h : gamma = beta
  · subst gamma
    simp [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm]
  · simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm,
      if_neg h] using
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotient_norm_le
        H N hN beta gamma h

/-- The first Wilson-action insertion family is operator-norm differentiable with derivative
minus the genuine second Wilson-action insertion. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonAction_hasNonnegativeOperatorNormDerivAt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    Tendsto
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN beta)
      (𝓝 beta)
      (𝓝 0) := by
  let B :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ 3
  have hB : 0 ≤ B := by positivity
  rw [Metric.tendsto_nhds_nhds]
  intro epsilon hepsilon
  by_cases hBzero : B = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro gamma hdist
    have herr :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm_le
        H N hN beta gamma
    change periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN beta gamma ≤ B * ‖gamma.1 - beta.1‖ at herr
    rw [hBzero, zero_mul] at herr
    have hnonneg : 0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN beta gamma := by
      unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm
      split
      · exact le_rfl
      · exact ContinuousLinearMap.opNorm_nonneg _
    have hz := le_antisymm herr hnonneg
    rw [hz]
    simpa using hepsilon
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
    refine ⟨epsilon / B, div_pos hepsilon hBpos, ?_⟩
    intro gamma hdist
    have hdist' : ‖gamma.1 - beta.1‖ < epsilon / B := by
      simpa [Real.dist_eq] using hdist
    have herr :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm_le
        H N hN beta gamma
    change periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN beta gamma ≤ B * ‖gamma.1 - beta.1‖ at herr
    have hmul : B * ‖gamma.1 - beta.1‖ < B * (epsilon / B) :=
      mul_lt_mul_of_pos_left hdist' hBpos
    have hcancel : B * (epsilon / B) = epsilon := by
      field_simp [ne_of_gt hBpos]
    have herrlt :
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm
          H N hN beta gamma < epsilon := herr.trans_lt (by simpa [hcancel] using hmul)
    have hnonneg : 0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN beta gamma := by
      unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm
      split
      · exact le_rfl
      · exact ContinuousLinearMap.opNorm_nonneg _
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using herrlt

/-- Sharp pathwise coupling Lipschitz estimate for K_beta S_path^2. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertion_norm_sub_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 3 * ‖gamma - beta‖ := by
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let S := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hK :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_norm_sub_le
      H N hN beta gamma hbeta hgamma path
  have hS : ‖S‖ ≤ C := by
    simpa [S, C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound H N path
  have hSsq : ‖S‖ ^ 2 ≤ C ^ 2 := by
    nlinarith [norm_nonneg S]
  rw [show
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path * S ^ 2 -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path * S ^ 2 =
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path) * S ^ 2 by ring,
    norm_mul, norm_pow]
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path‖ * ‖S‖ ^ 2 ≤
      (C * ‖gamma - beta‖) * C ^ 2 :=
        mul_le_mul hK hSsq (sq_nonneg _) (mul_nonneg hC (norm_nonneg _))
    _ = C ^ 3 * ‖gamma - beta‖ := by ring

/-- Global operator-norm Lipschitz estimate for the genuine second-insertion family. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_norm_sub_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 3 * ‖gamma - beta‖ := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
        H N hN gamma hgamma -
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
        H N hN beta hbeta
  let B := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
    H N ^ 3 * ‖gamma - beta‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply ContinuousLinearMap.opNorm_le_bound D hB
  intro f
  let v := D f
  have hgammaAmp :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_inner_eq_pathActionSquareIntegral
      H N hN gamma hgamma f v
  have hbetaAmp :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_inner_eq_pathActionSquareIntegral
      H N hN beta hbeta f v
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let base := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      (v : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  let F := fun t : ℝ =>
    fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N t path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
        (v : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hFg : Integrable (F gamma) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable H N hN gamma hgamma f v
  have hFb : Integrable (F beta) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable H N hN beta hbeta f v
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_endpointProduct_integrable H N f v
  have hdom : Integrable (fun path => B * |base path|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul B
  have hpoint : ∀ path, ‖F gamma path - F beta path‖ ≤ B * |base path| := by
    intro path
    have hfac :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertion_norm_sub_le
        H N hN beta gamma hbeta hgamma path
    change
      |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
          (v : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) -
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
          (v : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))| ≤ B * |base path|
    rw [show
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
          (v : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) -
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
          (v : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) =
        base path *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 -
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2) by
          simp [base]
          ring,
      abs_mul]
    have hfac' :
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 -
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2| ≤ B := by
      simpa [B, Real.norm_eq_abs] using hfac
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hfac' (abs_nonneg (base path))
  have hint := norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall hpoint)
  have hcoeff : ‖inner ℝ (D f) v‖ ≤ B * ‖f‖ * ‖v‖ := by
    change ‖inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN gamma hgamma f -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN beta hbeta f) v‖ ≤ _
    rw [show inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN gamma hgamma f -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN beta hbeta f) v =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN gamma hgamma f) v -
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN beta hbeta f) v from inner_sub_left (𝕜 := ℝ) _ _ _]
    rw [hgammaAmp, hbetaAmp]
    unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
    change ‖(∫ path, F gamma path ∂pathMu) - (∫ path, F beta path ∂pathMu)‖ ≤ _
    rw [← integral_sub hFg hFb]
    calc
      ‖∫ path, F gamma path - F beta path ∂pathMu‖ ≤
          ∫ path, B * |base path| ∂pathMu := hint
      _ = B * (∫ path, |base path| ∂pathMu) := integral_const_mul B _
      _ ≤ B * (‖f‖ * ‖v‖) := by
        apply mul_le_mul_of_nonneg_left _ hB
        simpa [base, pathMu] using
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderEndpointProduct_integral_abs_le H N f v
      _ = B * ‖f‖ * ‖v‖ := by ring
  have hsq : ‖v‖ ^ 2 ≤ B * ‖f‖ * ‖v‖ := by
    rw [← real_inner_self_eq_norm_sq]
    exact (le_abs_self _).trans (by simpa [v, D] using hcoeff)
  change ‖D f‖ ≤ B * ‖f‖
  change ‖v‖ ≤ B * ‖f‖
  by_cases hz : ‖v‖ = 0
  · rw [hz]
    exact mul_nonneg hB (norm_nonneg f)
  have hpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have hfnonneg : 0 ≤ ‖f‖ := norm_nonneg _
  nlinarith

/-- The second-insertion family is globally Lipschitz with coefficient C^3. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily_norm_sub_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily H N hN gamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily H N hN beta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 3 * ‖gamma.1 - beta.1‖ := by
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_norm_sub_le
      H N hN beta.1 beta.2 gamma.1 gamma.2

/-- Operator-norm C^{2,1} certificate on the genuine nonnegative Wilson-coupling domain:
T has first derivative -O, O has derivative -O2, hence the second derivative of T is O2,
and O2 is globally Lipschitz with coefficient C^3. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransfer_C21_operatorNormCertificate
    (H N : ℕ)
    (hN : 0 < N)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    Tendsto
      (fun gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling =>
        if gamma = beta then 0 else
          ‖(gamma.1 - beta.1)⁻¹ •
                (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN gamma -
                  periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN beta) +
              periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily H N hN beta‖)
      (𝓝 beta) (𝓝 0) ∧
    Tendsto
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN beta)
      (𝓝 beta) (𝓝 0) ∧
    ∀ gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily H N hN gamma -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily H N hN beta‖ ≤
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
            H N ^ 3 * ‖gamma.1 - beta.1‖ := by
  refine ⟨periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransfer_hasNonnegativeOperatorNormDerivAt
      H N hN beta, ?_⟩
  refine ⟨periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonAction_hasNonnegativeOperatorNormDerivAt
      H N hN beta, ?_⟩
  intro gamma
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily_norm_sub_le
      H N hN beta gamma

end

end MathlibAnalytic
end MGAP4D
