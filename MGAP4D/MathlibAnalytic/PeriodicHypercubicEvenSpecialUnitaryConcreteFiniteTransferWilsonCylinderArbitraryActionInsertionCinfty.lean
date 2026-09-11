import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderSecondActionInsertionCouplingC21
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

local instance wilsonCylinderArbitraryActionInsertionCinftySpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance wilsonCylinderArbitraryActionInsertionCinftySpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance wilsonCylinderArbitraryActionInsertionCinftySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance wilsonCylinderArbitraryActionInsertionCinftySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance wilsonCylinderArbitraryActionInsertionCinftySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance wilsonCylinderArbitraryActionInsertionCinftySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance wilsonCylinderArbitraryActionInsertionCinftySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance wilsonCylinderArbitraryActionInsertionCinftyPhysicalCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

private theorem wilsonCylinderArbitraryActionInsertionCinfty_inner_sub_left
    (H N : ℕ)
    (x y z : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    inner ℝ (x - y) z = inner ℝ x z - inner ℝ y z := by
  calc
    inner ℝ (x - y) z = inner ℝ (x + -y) z := by rw [sub_eq_add_neg]
    _ = inner ℝ x z + inner ℝ (-y) z :=
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).innerProductSpace.add_left
        x (-y) z
    _ = inner ℝ x z + (-1 : ℝ) * inner ℝ y z := by
      have hneg :=
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).innerProductSpace.smul_left
          y z (-1 : ℝ)
      have hneg' : inner ℝ (-y) z = (-1 : ℝ) * inner ℝ y z := by
        simpa using hneg
      rw [hneg']
    _ = inner ℝ x z - inner ℝ y z := by ring

private theorem wilsonCylinderArbitraryActionInsertionCinfty_pathZero_measurePreserving
    (H N : ℕ) :
    MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        path 0)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let n := periodicHypercubicEvenPositiveHalfCylinderSlabCount H
  simpa [μ, n,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
    (MeasureTheory.measurePreserving_eval
      (μ := fun _ : Fin (n + 1) => μ) (0 : Fin (n + 1)))

private theorem wilsonCylinderArbitraryActionInsertionCinfty_pathLast_measurePreserving
    (H N : ℕ) :
    MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let n := periodicHypercubicEvenPositiveHalfCylinderSlabCount H
  simpa [μ, n,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
    (MeasureTheory.measurePreserving_eval
      (μ := fun _ : Fin (n + 1) => μ) (Fin.last n))

private theorem wilsonCylinderArbitraryActionInsertionCinfty_endpointProduct_integrable
    (H N : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  have hf2 : MemLp
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0)) 2 pathMu := by
    simpa [Function.comp_def, pathMu] using
      (Lp.memLp (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)).comp_measurePreserving
        (wilsonCylinderArbitraryActionInsertionCinfty_pathZero_measurePreserving H N)
  have hg2 : MemLp
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) 2 pathMu := by
    simpa [Function.comp_def, pathMu] using
      (Lp.memLp (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)).comp_measurePreserving
        (wilsonCylinderArbitraryActionInsertionCinfty_pathLast_measurePreserving H N)
  rw [← memLp_one_iff_integrable]
  exact hg2.mul' hf2

private theorem wilsonCylinderArbitraryActionInsertionCinfty_left_add_ae
    (H N : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
      ((f + g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0)) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N]
    (fun path =>
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) +
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0)) := by
  have h :=
    (wilsonCylinderArbitraryActionInsertionCinfty_pathZero_measurePreserving H N).quasiMeasurePreserving.ae_eq
      (Lp.coeFn_add
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N))
  simpa [Pi.add_apply] using h

private theorem wilsonCylinderArbitraryActionInsertionCinfty_left_smul_ae
    (H N : ℕ)
    (r : ℝ)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
      ((r • f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0)) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N]
    (fun path => r *
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0)) := by
  have h :=
    (wilsonCylinderArbitraryActionInsertionCinfty_pathZero_measurePreserving H N).quasiMeasurePreserving.ae_eq
      (Lp.coeFn_smul r
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N))
  simpa [Pi.smul_apply, smul_eq_mul] using h

private theorem wilsonCylinderArbitraryActionInsertionCinfty_right_add_ae
    (H N : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
      ((f + g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N]
    (fun path =>
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) +
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) := by
  have h :=
    (wilsonCylinderArbitraryActionInsertionCinfty_pathLast_measurePreserving H N).quasiMeasurePreserving.ae_eq
      (Lp.coeFn_add
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N))
  simpa [Pi.add_apply] using h

private theorem wilsonCylinderArbitraryActionInsertionCinfty_right_smul_ae
    (H N : ℕ)
    (r : ℝ)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
      ((r • f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N]
    (fun path => r *
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) := by
  have h :=
    (wilsonCylinderArbitraryActionInsertionCinfty_pathLast_measurePreserving H N).quasiMeasurePreserving.ae_eq
      (Lp.coeFn_smul r
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N))
  simpa [Pi.smul_apply, smul_eq_mul] using h

private theorem wilsonCylinderArbitraryActionInsertionCinfty_nthIntegrand_integrable
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let base := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderArbitraryActionInsertionCinfty_endpointProduct_integrable H N f g
  have hKmeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta) pathMu :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable
      H N beta).aestronglyMeasurable
  have hSmeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N) pathMu :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_measurable
      H N).aestronglyMeasurable
  have hSpowMeas : AEStronglyMeasurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m) pathMu := by
    exact (continuous_pow m).comp_aestronglyMeasurable hSmeas
  have hmeas : AEStronglyMeasurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathMu := by
    have h := hbase.aestronglyMeasurable.mul (hKmeas.mul hSpowMeas)
    have heq :
        (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) =
          (fun path => base path *
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m)) := by
      funext path
      simp [base]
      ring
    rw [heq]
    simpa only [Pi.mul_apply] using h
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hdom : Integrable (fun path => C ^ m * |base path|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul (C ^ m)
  apply hdom.mono' hmeas
  filter_upwards with path
  have hK := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
    H N hN beta hbeta path
  have hS := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound
    H N path
  have hSabs : |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ≤ C := by
    simpa [Real.norm_eq_abs, C] using hS
  have hSpow :
      |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ^ m ≤ C ^ m :=
    pow_le_pow_left₀ (abs_nonneg _) hSabs m
  change
    |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))| ≤
      C ^ m * |base path|
  rw [show
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) =
      base path *
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m) by
          simp [base]
          ring,
    abs_mul]
  have hfac :
      |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m| ≤ C ^ m := by
    rw [abs_mul, abs_pow]
    calc
      _ ≤ 1 * C ^ m :=
        mul_le_mul hK hSpow (pow_nonneg (abs_nonneg _) m) zero_le_one
      _ = C ^ m := one_mul _
  calc
    |base path| *
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m| ≤
      |base path| * C ^ m :=
        mul_le_mul_of_nonneg_left hfac (abs_nonneg (base path))
    _ = C ^ m * |base path| := by ring

/-- Literal arbitrary-order Wilson-action insertion on the common positive-half path carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude
    (H N : ℕ) (m : ℕ) (beta : ℝ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) : ℝ :=
  ∫ path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N,
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
    ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)

/-- Every order is bounded by the corresponding power of the cylinder action bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude_abs_le
    (H N : ℕ) (hN : 0 < N) (m : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude
        H N m beta f g| ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ m *
        ‖f‖ * ‖g‖ := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let base := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  let F := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderArbitraryActionInsertionCinfty_endpointProduct_integrable H N f g
  have hF : Integrable F pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderArbitraryActionInsertionCinfty_nthIntegrand_integrable H N hN m beta hbeta f g
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hdom : Integrable (fun path => C ^ m * |base path|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul (C ^ m)
  have hpoint : ∀ path, ‖F path‖ ≤ C ^ m * |base path| := by
    intro path
    have hK := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
      H N hN beta hbeta path
    have hS := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound
      H N path
    have hSabs : |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ≤ C := by
      simpa [Real.norm_eq_abs, C] using hS
    have hSpow :
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ^ m ≤ C ^ m :=
      pow_le_pow_left₀ (abs_nonneg _) hSabs m
    change |F path| ≤ C ^ m * |base path|
    rw [show F path = base path *
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m) by
        simp [F, base]
        ring,
      abs_mul]
    have hfac :
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m| ≤ C ^ m := by
      rw [abs_mul, abs_pow]
      calc
        _ ≤ 1 * C ^ m :=
          mul_le_mul hK hSpow (pow_nonneg (abs_nonneg _) m) zero_le_one
        _ = C ^ m := one_mul _
    calc
      |base path| *
          |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m| ≤
        |base path| * C ^ m :=
          mul_le_mul_of_nonneg_left hfac (abs_nonneg (base path))
      _ = C ^ m * |base path| := by ring
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude
  change |∫ path, F path ∂pathMu| ≤ _
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ path, F path ∂pathMu‖ ≤ ∫ path, C ^ m * |base path| ∂pathMu :=
      norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall hpoint)
    _ = C ^ m * (∫ path, |base path| ∂pathMu) := integral_const_mul _ _
    _ ≤ C ^ m * (‖f‖ * ‖g‖) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC m)
      simpa [base, pathMu] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderEndpointProduct_integral_abs_le H N f g
    _ = periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ m *
        ‖f‖ * ‖g‖ := by simp [C]; ring

private noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionLinearBilin
    (H N : ℕ) (hN : 0 < N) (m : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    LinearMap.BilinForm ℝ
      (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
  LinearMap.mk₂ ℝ
    (fun f g =>
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude
        H N m beta f g)
    (by
      intro f₁ f₂ g
      let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
      let F := fun f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N =>
        fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      have h1 : Integrable (F f₁) pathMu := by
        simpa [F, pathMu] using
          wilsonCylinderArbitraryActionInsertionCinfty_nthIntegrand_integrable H N hN m beta hbeta f₁ g
      have h2 : Integrable (F f₂) pathMu := by
        simpa [F, pathMu] using
          wilsonCylinderArbitraryActionInsertionCinfty_nthIntegrand_integrable H N hN m beta hbeta f₂ g
      have hadd := wilsonCylinderArbitraryActionInsertionCinfty_left_add_ae H N f₁ f₂
      unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude
      change (∫ path, F (f₁ + f₂) path ∂pathMu) =
        (∫ path, F f₁ path ∂pathMu) + (∫ path, F f₂ path ∂pathMu)
      rw [← integral_add h1 h2]
      apply integral_congr_ae
      filter_upwards [hadd] with path hp
      simp only [F]
      rw [hp]
      ring)
    (by
      intro r f g
      let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
      let F := fun f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N =>
        fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      have hsmul := wilsonCylinderArbitraryActionInsertionCinfty_left_smul_ae H N r f
      unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude
      change (∫ path, F (r • f) path ∂pathMu) = r * (∫ path, F f path ∂pathMu)
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hsmul] with path hp
      simp only [F]
      rw [hp]
      ring)
    (by
      intro f g₁ g₂
      let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
      let F := fun g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N =>
        fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      have h1 : Integrable (F g₁) pathMu := by
        simpa [F, pathMu] using
          wilsonCylinderArbitraryActionInsertionCinfty_nthIntegrand_integrable H N hN m beta hbeta f g₁
      have h2 : Integrable (F g₂) pathMu := by
        simpa [F, pathMu] using
          wilsonCylinderArbitraryActionInsertionCinfty_nthIntegrand_integrable H N hN m beta hbeta f g₂
      have hadd := wilsonCylinderArbitraryActionInsertionCinfty_right_add_ae H N g₁ g₂
      unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude
      change (∫ path, F (g₁ + g₂) path ∂pathMu) =
        (∫ path, F g₁ path ∂pathMu) + (∫ path, F g₂ path ∂pathMu)
      rw [← integral_add h1 h2]
      apply integral_congr_ae
      filter_upwards [hadd] with path hp
      simp only [F]
      rw [hp]
      ring)
    (by
      intro r f g
      let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
      let F := fun g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N =>
        fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      have hsmul := wilsonCylinderArbitraryActionInsertionCinfty_right_smul_ae H N r g
      unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude
      change (∫ path, F (r • g) path ∂pathMu) = r * (∫ path, F g path ∂pathMu)
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hsmul] with path hp
      simp only [F]
      rw [hp]
      ring)

noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionBilin
    (H N : ℕ) (hN : 0 < N) (m : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ] ℝ :=
  (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionLinearBilin
    H N hN m beta hbeta).mkContinuous₂
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ m)
      (by
        intro f g
        simpa [Real.norm_eq_abs, mul_assoc] using
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude_abs_le
            H N hN m beta hbeta f g)

/-- Genuine arbitrary-order Wilson-action insertion on the existing physical Gauss-law Hilbert space. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
    (H N : ℕ) (hN : 0 < N) (m : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  InnerProductSpace.continuousLinearMapOfBilin
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionBilin
      H N hN m beta hbeta)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_inner_eq_pathActionPowerIntegral
    (H N : ℕ) (hN : 0 < N) (m : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN m beta hbeta f) g =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude
        H N m beta f g := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
  unfold InnerProductSpace.continuousLinearMapOfBilin
  change inner ℝ
      ((InnerProductSpace.toDual ℝ
        (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)).symm
        ((periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionBilin
          H N hN m beta hbeta) f)) g = _
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

private theorem wilsonCylinderArbitraryActionInsertionCinfty_opNorm_le_of_inner_bound
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)
    (B : ℝ) (hB : 0 ≤ B)
    (hinner : ∀ f g, ‖inner ℝ (A f) g‖ ≤ B * ‖f‖ * ‖g‖) :
    ‖A‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound A hB
  intro f
  let v := A f
  have h := hinner f v
  have hsq : ‖v‖ ^ 2 ≤ B * ‖f‖ * ‖v‖ := by
    rw [← real_inner_self_eq_norm_sq]
    exact (le_abs_self _).trans (by simpa [v] using h)
  change ‖v‖ ≤ B * ‖f‖
  by_cases hz : ‖v‖ = 0
  · rw [hz]
    exact mul_nonneg hB (norm_nonneg f)
  have hv : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  nlinarith [norm_nonneg f]

/-- Uniform all-order operator-norm bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_norm_le
    (H N : ℕ) (hN : 0 < N) (m : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
        H N hN m beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ m := by
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  apply wilsonCylinderArbitraryActionInsertionCinfty_opNorm_le_of_inner_bound H N _ (C ^ m) (pow_nonneg hC m)
  intro f g
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_inner_eq_pathActionPowerIntegral
    H N hN m beta hbeta f g]
  simpa [C, Real.norm_eq_abs, mul_assoc] using
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude_abs_le
      H N hN m beta hbeta f g

/-- Arbitrary-order insertion family on the genuine nonnegative coupling domain. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionFamily
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
    H N hN m beta.1 beta.2

/-- The generic hierarchy agrees at order one with the previously constructed first insertion. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_one_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
        H N hN 1 beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
        H N hN beta hbeta := by
  apply ContinuousLinearMap.ext
  intro f
  apply (InnerProductSpace.toDualMap ℝ
    (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)).injective
  apply ContinuousLinearMap.ext
  intro g
  change inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
        H N hN 1 beta hbeta f) g =
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
        H N hN beta hbeta f) g
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_inner_eq_pathActionPowerIntegral
    H N hN 1 beta hbeta f g]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_inner_eq_pathActionIntegral
    H N hN beta hbeta f g]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude
  simp [pow_one]

/-- The generic hierarchy also recovers the second insertion of the `C^{2,1}` layer. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_two_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
        H N hN 2 beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
        H N hN beta hbeta := by
  apply ContinuousLinearMap.ext
  intro f
  apply (InnerProductSpace.toDualMap ℝ
    (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)).injective
  apply ContinuousLinearMap.ext
  intro g
  change inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
        H N hN 2 beta hbeta f) g =
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
        H N hN beta hbeta f) g
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_inner_eq_pathActionPowerIntegral
    H N hN 2 beta hbeta f g]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_inner_eq_pathActionSquareIntegral
    H N hN beta hbeta f g]
  rfl

/-- Pathwise coupling Lipschitz bound at arbitrary insertion order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertion_norm_sub_le
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ (m + 1) *
        ‖gamma - beta‖ := by
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let S := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hK := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_norm_sub_le
    H N hN beta gamma hbeta hgamma path
  have hS : ‖S‖ ≤ C := by
    simpa [S, C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound H N path
  have hSm : ‖S‖ ^ m ≤ C ^ m :=
    pow_le_pow_left₀ (norm_nonneg S) hS m
  rw [show
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path * S ^ m -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path * S ^ m =
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path) * S ^ m by ring,
    norm_mul, norm_pow]
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path‖ * ‖S‖ ^ m ≤
      (C * ‖gamma - beta‖) * C ^ m :=
        mul_le_mul hK hSm (pow_nonneg (norm_nonneg S) m)
          (mul_nonneg hC (norm_nonneg _))
    _ = C ^ (m + 1) * ‖gamma - beta‖ := by
      rw [pow_succ]
      ring

/-- Global operator-norm Lipschitz bound at arbitrary insertion order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_norm_sub_le
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta) (gamma : ℝ) (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN m gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN m beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ (m + 1) *
        ‖gamma - beta‖ := by
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let B := C ^ (m + 1) * ‖gamma - beta‖
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hB : 0 ≤ B := mul_nonneg (pow_nonneg hC (m + 1)) (norm_nonneg _)
  apply wilsonCylinderArbitraryActionInsertionCinfty_opNorm_le_of_inner_bound H N _ B hB
  intro f g
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let base := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  let F := fun t : ℝ =>
    fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N t path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hFg : Integrable (F gamma) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderArbitraryActionInsertionCinfty_nthIntegrand_integrable H N hN m gamma hgamma f g
  have hFb : Integrable (F beta) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderArbitraryActionInsertionCinfty_nthIntegrand_integrable H N hN m beta hbeta f g
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderArbitraryActionInsertionCinfty_endpointProduct_integrable H N f g
  have hdom : Integrable (fun path => B * |base path|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul B
  have hpoint : ∀ path, ‖F gamma path - F beta path‖ ≤ B * |base path| := by
    intro path
    have hfac := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertion_norm_sub_le
      H N hN m beta gamma hbeta hgamma path
    change |F gamma path - F beta path| ≤ B * |base path|
    rw [show F gamma path - F beta path = base path *
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m) by
        simp [F, base]
        ring,
      abs_mul]
    have hfac' :
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m -
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m| ≤ B := by
      simpa [B, C, Real.norm_eq_abs] using hfac
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hfac' (abs_nonneg (base path))
  change ‖inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN m gamma hgamma f -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN m beta hbeta f) g‖ ≤ B * ‖f‖ * ‖g‖
  rw [wilsonCylinderArbitraryActionInsertionCinfty_inner_sub_left H N]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_inner_eq_pathActionPowerIntegral
    H N hN m gamma hgamma f g]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_inner_eq_pathActionPowerIntegral
    H N hN m beta hbeta f g]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude
  change ‖(∫ path, F gamma path ∂pathMu) - (∫ path, F beta path ∂pathMu)‖ ≤ B * ‖f‖ * ‖g‖
  rw [← integral_sub hFg hFb]
  calc
    ‖∫ path, F gamma path - F beta path ∂pathMu‖ ≤ ∫ path, B * |base path| ∂pathMu :=
      norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall hpoint)
    _ = B * (∫ path, |base path| ∂pathMu) := integral_const_mul _ _
    _ ≤ B * (‖f‖ * ‖g‖) := by
      apply mul_le_mul_of_nonneg_left _ hB
      simpa [base, pathMu] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderEndpointProduct_integral_abs_le H N f g
    _ = B * ‖f‖ * ‖g‖ := by ring

/-- Pathwise quadratic Taylor remainder for the order-`m` insertion `K_beta S^m`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertion_quadraticRemainder
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m +
        (gamma - beta) *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ (m + 1))‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ (m + 2) *
        ‖gamma - beta‖ ^ 2 := by
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let S := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path
  let K := fun t : ℝ =>
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N t path
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hS : ‖S‖ ≤ C := by
    simpa [S, C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound H N path
  have hSm : ‖S‖ ^ m ≤ C ^ m :=
    pow_le_pow_left₀ (norm_nonneg S) hS m
  have hR := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_quadraticRemainder
    H N hN beta gamma hbeta hgamma path
  change ‖K gamma * S ^ m - K beta * S ^ m +
      (gamma - beta) * (K beta * S ^ (m + 1))‖ ≤
    C ^ (m + 2) * ‖gamma - beta‖ ^ 2
  rw [show K gamma * S ^ m - K beta * S ^ m +
      (gamma - beta) * (K beta * S ^ (m + 1)) =
      S ^ m * (K gamma - K beta + (gamma - beta) * (K beta * S)) by
        rw [pow_succ]
        ring,
    norm_mul, norm_pow]
  have hR' :
      ‖K gamma - K beta + (gamma - beta) * (K beta * S)‖ ≤
        C ^ 2 * ‖gamma - beta‖ ^ 2 := by
    simpa [K, S, C] using hR
  calc
    ‖S‖ ^ m * ‖K gamma - K beta + (gamma - beta) * (K beta * S)‖ ≤
      C ^ m * (C ^ 2 * ‖gamma - beta‖ ^ 2) :=
        mul_le_mul hSm hR' (norm_nonneg _) (pow_nonneg hC m)
    _ = C ^ (m + 2) * ‖gamma - beta‖ ^ 2 := by
      rw [pow_add]
      ring

/-- Operator remainder for differentiating the order-`m` insertion family. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaRemainderOperator
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta) (gamma : ℝ) (hgamma : 0 ≤ gamma) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
      H N hN m gamma hgamma -
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
      H N hN m beta hbeta +
    (gamma - beta) •
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
        H N hN (m + 1) beta hbeta

private theorem wilsonCylinderArbitraryActionInsertionCinfty_remainder_inner_eq_integral
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta) (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaRemainderOperator
        H N hN m beta hbeta gamma hgamma f) g =
    ∫ path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N,
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m -
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m +
          (gamma - beta) *
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ (m + 1))) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let F := fun t : ℝ =>
    fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N t path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  let A1 := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ (m + 1) *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hFg : Integrable (F gamma) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderArbitraryActionInsertionCinfty_nthIntegrand_integrable H N hN m gamma hgamma f g
  have hFb : Integrable (F beta) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderArbitraryActionInsertionCinfty_nthIntegrand_integrable H N hN m beta hbeta f g
  have hA1 : Integrable A1 pathMu := by
    simpa [A1, pathMu] using
      wilsonCylinderArbitraryActionInsertionCinfty_nthIntegrand_integrable H N hN (m + 1) beta hbeta f g
  have hsub : Integrable (fun path => F gamma path - F beta path) pathMu := hFg.sub hFb
  have hscaled : Integrable (fun path => (gamma - beta) * A1 path) pathMu :=
    hA1.const_mul (gamma - beta)
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaRemainderOperator
  change inner ℝ
    ((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
        H N hN m gamma hgamma f -
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
        H N hN m beta hbeta f) +
      (gamma - beta) •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN (m + 1) beta hbeta f) g = _
  have hadd :
      inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
            H N hN m gamma hgamma f -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
            H N hN m beta hbeta f) +
          (gamma - beta) •
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
              H N hN (m + 1) beta hbeta f) g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
            H N hN m gamma hgamma f -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
            H N hN m beta hbeta f) g +
      inner ℝ
        ((gamma - beta) •
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
            H N hN (m + 1) beta hbeta f) g :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).innerProductSpace.add_left _ _ _
  rw [hadd]
  rw [wilsonCylinderArbitraryActionInsertionCinfty_inner_sub_left H N]
  have hsmul :
      inner ℝ
        ((gamma - beta) •
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
            H N hN (m + 1) beta hbeta f) g =
        (gamma - beta) * inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
            H N hN (m + 1) beta hbeta f) g := by
    simpa using
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).innerProductSpace.smul_left
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN (m + 1) beta hbeta f) g (gamma - beta)
  rw [hsmul]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_inner_eq_pathActionPowerIntegral
    H N hN m gamma hgamma f g]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_inner_eq_pathActionPowerIntegral
    H N hN m beta hbeta f g]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_inner_eq_pathActionPowerIntegral
    H N hN (m + 1) beta hbeta f g]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude
  change (∫ path, F gamma path ∂pathMu) - (∫ path, F beta path ∂pathMu) +
    (gamma - beta) * (∫ path, A1 path ∂pathMu) = _
  rw [← integral_sub hFg hFb]
  rw [← integral_const_mul]
  have hcombine :
      (∫ path, F gamma path - F beta path ∂pathMu) +
          (∫ path, (gamma - beta) * A1 path ∂pathMu) =
        ∫ path, (F gamma path - F beta path) + (gamma - beta) * A1 path ∂pathMu := by
    symm
    exact integral_add hsub hscaled
  rw [hcombine]
  apply integral_congr_ae
  filter_upwards with path
  simp [F, A1]
  ring

/-- Operator-norm quadratic remainder at arbitrary insertion order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaRemainderOperator_norm_le
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta) (gamma : ℝ) (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaRemainderOperator
        H N hN m beta hbeta gamma hgamma‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ (m + 2) *
        ‖gamma - beta‖ ^ 2 := by
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let B := C ^ (m + 2) * ‖gamma - beta‖ ^ 2
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hB : 0 ≤ B := mul_nonneg (pow_nonneg hC (m + 2)) (sq_nonneg _)
  apply wilsonCylinderArbitraryActionInsertionCinfty_opNorm_le_of_inner_bound H N _ B hB
  intro f g
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let base := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  let R := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m -
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ m +
      (gamma - beta) *
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ (m + 1))
  let D := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) * R path *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderArbitraryActionInsertionCinfty_endpointProduct_integrable H N f g
  have hdom : Integrable (fun path => B * |base path|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul B
  have hpoint : ∀ path, ‖D path‖ ≤ B * |base path| := by
    intro path
    have hR := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertion_quadraticRemainder
      H N hN m beta gamma hbeta hgamma path
    change |D path| ≤ B * |base path|
    rw [show D path = base path * R path by simp [D, base, R]; ring, abs_mul]
    have hR' : |R path| ≤ B := by
      simpa [R, B, C, Real.norm_eq_abs] using hR
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hR' (abs_nonneg (base path))
  rw [wilsonCylinderArbitraryActionInsertionCinfty_remainder_inner_eq_integral
    H N hN m beta hbeta gamma hgamma f g]
  change ‖∫ path, D path ∂pathMu‖ ≤ _
  calc
    ‖∫ path, D path ∂pathMu‖ ≤ ∫ path, B * |base path| ∂pathMu :=
      norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall hpoint)
    _ = B * (∫ path, |base path| ∂pathMu) := integral_const_mul _ _
    _ ≤ B * (‖f‖ * ‖g‖) := by
      apply mul_le_mul_of_nonneg_left _ hB
      simpa [base, pathMu] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderEndpointProduct_integral_abs_le H N f g
    _ = B * ‖f‖ * ‖g‖ := by ring

noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientError
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  (gamma.1 - beta.1)⁻¹ •
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionFamily H N hN m gamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionFamily H N hN m beta) +
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionFamily H N hN (m + 1) beta

private theorem wilsonCylinderArbitraryActionInsertionCinfty_differenceQuotientError_eq
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling)
    (h : gamma ≠ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientError
        H N hN m beta gamma =
      (gamma.1 - beta.1)⁻¹ •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaRemainderOperator
          H N hN m beta.1 beta.2 gamma.1 gamma.2 := by
  have hval : gamma.1 ≠ beta.1 := by
    intro hval
    apply h
    exact Subtype.ext hval
  have hsub : gamma.1 - beta.1 ≠ 0 := sub_ne_zero.mpr hval
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientError
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionFamily
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaRemainderOperator
  apply ContinuousLinearMap.ext
  intro f
  change
    (gamma.1 - beta.1)⁻¹ •
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
              H N hN m gamma.1 gamma.2 f -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
              H N hN m beta.1 beta.2 f) +
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
            H N hN (m + 1) beta.1 beta.2 f =
      (gamma.1 - beta.1)⁻¹ •
        ((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
              H N hN m gamma.1 gamma.2 f -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
              H N hN m beta.1 beta.2 f) +
          (gamma.1 - beta.1) •
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
              H N hN (m + 1) beta.1 beta.2 f)
  rw [smul_add, smul_smul, inv_mul_cancel₀ hsub, one_smul]

private theorem wilsonCylinderArbitraryActionInsertionCinfty_differenceQuotientError_norm_le
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling)
    (h : gamma ≠ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientError
        H N hN m beta gamma‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ (m + 2) *
        ‖gamma.1 - beta.1‖ := by
  have hval : gamma.1 ≠ beta.1 := by
    intro hval
    apply h
    exact Subtype.ext hval
  have hsub : gamma.1 - beta.1 ≠ 0 := sub_ne_zero.mpr hval
  have hnorm : ‖gamma.1 - beta.1‖ ≠ 0 := norm_ne_zero_iff.mpr hsub
  rw [wilsonCylinderArbitraryActionInsertionCinfty_differenceQuotientError_eq H N hN m beta gamma h]
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaRemainderOperator
    H N hN m beta.1 beta.2 gamma.1 gamma.2
  let B := C ^ (m + 2) * ‖gamma.1 - beta.1‖
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hB : 0 ≤ B := mul_nonneg (pow_nonneg hC (m + 2)) (norm_nonneg _)
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  change ‖(gamma.1 - beta.1)⁻¹ • R f‖ ≤ B * ‖f‖
  rw [norm_smul]
  have hRop :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaRemainderOperator_norm_le
      H N hN m beta.1 beta.2 gamma.1 gamma.2
  have hRapp :
      ‖R f‖ ≤ (C ^ (m + 2) * ‖gamma.1 - beta.1‖ ^ 2) * ‖f‖ := by
    calc
      ‖R f‖ ≤ ‖R‖ * ‖f‖ := R.le_opNorm f
      _ ≤ (C ^ (m + 2) * ‖gamma.1 - beta.1‖ ^ 2) * ‖f‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
        simpa [R, C] using hRop
  calc
    ‖(gamma.1 - beta.1)⁻¹‖ * ‖R f‖ ≤
        ‖(gamma.1 - beta.1)⁻¹‖ *
          ((C ^ (m + 2) * ‖gamma.1 - beta.1‖ ^ 2) * ‖f‖) :=
      mul_le_mul_of_nonneg_left hRapp (norm_nonneg _)
    _ = B * ‖f‖ := by
      rw [norm_inv]
      dsimp [B]
      field_simp [hnorm]

noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientErrorNorm
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) : ℝ :=
  if gamma = beta then 0 else
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientError
        H N hN m beta gamma‖

private theorem wilsonCylinderArbitraryActionInsertionCinfty_differenceQuotientErrorNorm_le
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN m beta gamma ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ (m + 2) *
        ‖gamma.1 - beta.1‖ := by
  by_cases h : gamma = beta
  · subst gamma
    simp [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientErrorNorm]
  · simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientErrorNorm, h] using
      wilsonCylinderArbitraryActionInsertionCinfty_differenceQuotientError_norm_le H N hN m beta gamma h

/-- Every insertion order is operator-norm differentiable, with derivative the negative next order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonAction_hasNonnegativeOperatorNormDerivAt
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    Tendsto
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN m beta)
      (𝓝 beta) (𝓝 0) := by
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let B := C ^ (m + 2)
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hB : 0 ≤ B := pow_nonneg hC (m + 2)
  rw [Metric.tendsto_nhds_nhds]
  intro epsilon hepsilon
  by_cases hBzero : B = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro gamma hdist
    have herr := wilsonCylinderArbitraryActionInsertionCinfty_differenceQuotientErrorNorm_le H N hN m beta gamma
    change periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN m beta gamma ≤ B * ‖gamma.1 - beta.1‖ at herr
    rw [hBzero, zero_mul] at herr
    have hnonneg : 0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN m beta gamma := by
      unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientErrorNorm
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
    have herr := wilsonCylinderArbitraryActionInsertionCinfty_differenceQuotientErrorNorm_le H N hN m beta gamma
    change periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN m beta gamma ≤ B * ‖gamma.1 - beta.1‖ at herr
    have hmul : B * ‖gamma.1 - beta.1‖ < B * (epsilon / B) :=
      mul_lt_mul_of_pos_left hdist' hBpos
    have hcancel : B * (epsilon / B) = epsilon := by field_simp [ne_of_gt hBpos]
    have herrlt :
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientErrorNorm
          H N hN m beta gamma < epsilon := herr.trans_lt (by simpa [hcancel] using hmul)
    have hnonneg : 0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN m beta gamma := by
      unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientErrorNorm
      split
      · exact le_rfl
      · exact ContinuousLinearMap.opNorm_nonneg _
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using herrlt

/-- The all-order insertion family is globally Lipschitz at each fixed order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionFamily_norm_sub_le
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionFamily H N hN m gamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionFamily H N hN m beta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ (m + 1) *
        ‖gamma.1 - beta.1‖ := by
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionFamily] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_norm_sub_le
      H N hN m beta.1 beta.2 gamma.1 gamma.2

/-- Operator-norm `C^∞` certificate for the genuine nonnegative Wilson-coupling transfer family.
Order one agrees with the physical Wilson-action insertion, every order differentiates to minus the
next insertion, and every derivative field is globally Lipschitz with its natural `C^(m+1)` bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransfer_Cinfty_operatorNormCertificate
    (H N : ℕ) (hN : 0 < N)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionFamily H N hN 1 beta =
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily H N hN beta ∧
    Tendsto
      (fun gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling =>
        if gamma = beta then 0 else
          ‖(gamma.1 - beta.1)⁻¹ •
                (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN gamma -
                  periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN beta) +
              periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily H N hN beta‖)
      (𝓝 beta) (𝓝 0) ∧
    ∀ m : ℕ,
      Tendsto
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaDifferenceQuotientErrorNorm
          H N hN m beta)
        (𝓝 beta) (𝓝 0) ∧
      ∀ gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionFamily H N hN (m + 1) gamma -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionFamily H N hN (m + 1) beta‖ ≤
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ (m + 2) *
            ‖gamma.1 - beta.1‖ := by
  refine ⟨?_, periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransfer_hasNonnegativeOperatorNormDerivAt
      H N hN beta, ?_⟩
  · simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionFamily,
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily] using
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_one_eq
        H N hN beta.1 beta.2
  · intro m
    refine ⟨periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonAction_hasNonnegativeOperatorNormDerivAt
      H N hN m beta, ?_⟩
    intro gamma
    exact periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionFamily_norm_sub_le
      H N hN (m + 1) beta gamma

end
end MathlibAnalytic
end MGAP4D
