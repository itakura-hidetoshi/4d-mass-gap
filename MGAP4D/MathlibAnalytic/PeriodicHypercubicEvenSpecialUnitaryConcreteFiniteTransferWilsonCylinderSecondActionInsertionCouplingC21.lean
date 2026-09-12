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
set_option synthInstance.maxHeartbeats 200000

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

/-- The existing Gauss-law physical submodule is complete because it was proved closed
in the ambient Haar `L²` Hilbert space.  Supplying this instance explicitly keeps
Fréchet--Riesz away from expensive typeclass search. -/
local instance wilsonCylinderSecondActionInsertionCouplingC21PhysicalCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

private theorem wilsonCylinderSecondActionInsertionCouplingC21_inner_sub_left
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

private theorem wilsonCylinderSecondActionInsertionCouplingC21_pathZero_measurePreserving
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

private theorem wilsonCylinderSecondActionInsertionCouplingC21_pathLast_measurePreserving
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

private theorem wilsonCylinderSecondActionInsertionCouplingC21_endpointProduct_integrable
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
        (wilsonCylinderSecondActionInsertionCouplingC21_pathZero_measurePreserving H N)
  have hg2 : MemLp
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) 2 pathMu := by
    simpa [Function.comp_def, pathMu] using
      (Lp.memLp (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)).comp_measurePreserving
        (wilsonCylinderSecondActionInsertionCouplingC21_pathLast_measurePreserving H N)
  rw [← memLp_one_iff_integrable]
  exact hg2.mul' hf2

private theorem wilsonCylinderSecondActionInsertionCouplingC21_left_add_ae
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
    (wilsonCylinderSecondActionInsertionCouplingC21_pathZero_measurePreserving H N).quasiMeasurePreserving.ae_eq
      (Lp.coeFn_add
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N))
  simpa [Pi.add_apply] using h

private theorem wilsonCylinderSecondActionInsertionCouplingC21_left_smul_ae
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
    (wilsonCylinderSecondActionInsertionCouplingC21_pathZero_measurePreserving H N).quasiMeasurePreserving.ae_eq
      (Lp.coeFn_smul r
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N))
  simpa [Pi.smul_apply, smul_eq_mul] using h

private theorem wilsonCylinderSecondActionInsertionCouplingC21_right_add_ae
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
    (wilsonCylinderSecondActionInsertionCouplingC21_pathLast_measurePreserving H N).quasiMeasurePreserving.ae_eq
      (Lp.coeFn_add
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N))
  simpa [Pi.add_apply] using h

private theorem wilsonCylinderSecondActionInsertionCouplingC21_right_smul_ae
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
    (wilsonCylinderSecondActionInsertionCouplingC21_pathLast_measurePreserving H N).quasiMeasurePreserving.ae_eq
      (Lp.coeFn_smul r
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N))
  simpa [Pi.smul_apply, smul_eq_mul] using h

private theorem wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
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
      wilsonCylinderSecondActionInsertionCouplingC21_endpointProduct_integrable H N f g
  have hKmeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta) pathMu :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable
      H N beta).aestronglyMeasurable
  have hSmeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N) pathMu :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_measurable
      H N).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
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
  have hK := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
    H N hN beta hbeta path
  have hS := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound
    H N path
  have hSabs : |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ≤ C := by
    simpa [Real.norm_eq_abs, C] using hS
  have hSsq : |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ^ 2 ≤ C ^ 2 := by
    nlinarith [abs_nonneg (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path)]
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
  have hfac :
      |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2| ≤ C ^ 2 := by
    rw [abs_mul, abs_pow]
    calc
      _ ≤ 1 * C ^ 2 := mul_le_mul hK hSsq (sq_nonneg _) zero_le_one
      _ = C ^ 2 := one_mul _
  calc
    |base path| *
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2| ≤
      |base path| * C ^ 2 :=
        mul_le_mul_of_nonneg_left hfac (abs_nonneg (base path))
    _ = C ^ 2 * |base path| := by ring

/-- Literal second Wilson-action insertion on the common positive-half path carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
    (H N : ℕ)
    (beta : ℝ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) : ℝ :=
  ∫ path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N,
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
    ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)

/-- The second insertion is bounded by the square of the cylinder action bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude_abs_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
        H N beta f g| ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ 2 *
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
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_endpointProduct_integrable H N f g
  have hF : Integrable F pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable H N hN beta hbeta f g
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hdom : Integrable (fun path => C ^ 2 * |base path|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul (C ^ 2)
  have hpoint : ∀ path, ‖F path‖ ≤ C ^ 2 * |base path| := by
    intro path
    have hK := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
      H N hN beta hbeta path
    have hS := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound
      H N path
    have hSabs : |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ≤ C := by
      simpa [Real.norm_eq_abs, C] using hS
    have hSsq : |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ^ 2 ≤ C ^ 2 := by
      nlinarith [abs_nonneg (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path)]
    change |F path| ≤ C ^ 2 * |base path|
    rw [show F path = base path *
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2) by
        simp [F, base]
        ring,
      abs_mul]
    have hfac :
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2| ≤ C ^ 2 := by
      rw [abs_mul, abs_pow]
      calc
        _ ≤ 1 * C ^ 2 := mul_le_mul hK hSsq (sq_nonneg _) zero_le_one
        _ = C ^ 2 := one_mul _
    calc
      |base path| *
          |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2| ≤
        |base path| * C ^ 2 :=
          mul_le_mul_of_nonneg_left hfac (abs_nonneg (base path))
      _ = C ^ 2 * |base path| := by ring
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
  change |∫ path, F path ∂pathMu| ≤ _
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ path, F path ∂pathMu‖ ≤ ∫ path, C ^ 2 * |base path| ∂pathMu :=
      norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall hpoint)
    _ = C ^ 2 * (∫ path, |base path| ∂pathMu) := integral_const_mul _ _
    _ ≤ C ^ 2 * (‖f‖ * ‖g‖) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      simpa [base, pathMu] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderEndpointProduct_integral_abs_le H N f g
    _ = periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ 2 *
        ‖f‖ * ‖g‖ := by simp [C]; ring

private noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionLinearBilin
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
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
          wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable H N hN beta hbeta f₁ g
      have h2 : Integrable (F f₂) pathMu := by
        simpa [F, pathMu] using
          wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable H N hN beta hbeta f₂ g
      have hadd := wilsonCylinderSecondActionInsertionCouplingC21_left_add_ae H N f₁ f₂
      unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
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
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      have hsmul := wilsonCylinderSecondActionInsertionCouplingC21_left_smul_ae H N r f
      unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
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
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      have h1 : Integrable (F g₁) pathMu := by
        simpa [F, pathMu] using
          wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable H N hN beta hbeta f g₁
      have h2 : Integrable (F g₂) pathMu := by
        simpa [F, pathMu] using
          wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable H N hN beta hbeta f g₂
      have hadd := wilsonCylinderSecondActionInsertionCouplingC21_right_add_ae H N g₁ g₂
      unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
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
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      have hsmul := wilsonCylinderSecondActionInsertionCouplingC21_right_smul_ae H N r g
      unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
      change (∫ path, F (r • g) path ∂pathMu) = r * (∫ path, F g path ∂pathMu)
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hsmul] with path hp
      simp only [F]
      rw [hp]
      ring)

noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionBilin
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
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

/-- Genuine second Wilson-action insertion on the existing physical Gauss-law Hilbert space. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  InnerProductSpace.continuousLinearMapOfBilin
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionBilin
      H N hN beta hbeta)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_inner_eq_pathActionSquareIntegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN beta hbeta f) g =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
        H N beta f g := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
  unfold InnerProductSpace.continuousLinearMapOfBilin
  change inner ℝ
      ((InnerProductSpace.toDual ℝ
        (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)).symm
        ((periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionBilin
          H N hN beta hbeta) f)) g = _
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

private theorem wilsonCylinderSecondActionInsertionCouplingC21_opNorm_le_of_inner_bound
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)
    (B : ℝ) (hB : 0 ≤ B)
    (hinner : ∀ f g,
      ‖inner ℝ (A f) g‖ ≤ B * ‖f‖ * ‖g‖) :
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

/-- Uniform second-insertion operator norm bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
        H N hN beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ 2 := by
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  apply wilsonCylinderSecondActionInsertionCouplingC21_opNorm_le_of_inner_bound H N _ (C ^ 2) (sq_nonneg C)
  intro f g
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_inner_eq_pathActionSquareIntegral
    H N hN beta hbeta f g]
  simpa [C, Real.norm_eq_abs, mul_assoc] using
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude_abs_le
      H N hN beta hbeta f g

/-- Pathwise quadratic Taylor remainder for the first Wilson-action insertion `K_beta S`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionInsertion_quadraticRemainder
    (H N : ℕ) (hN : 0 < N) (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path +
        (gamma - beta) *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2)‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ 3 *
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
  have hR := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_quadraticRemainder
    H N hN beta gamma hbeta hgamma path
  change ‖K gamma * S - K beta * S + (gamma - beta) * (K beta * S ^ 2)‖ ≤
    C ^ 3 * ‖gamma - beta‖ ^ 2
  rw [show K gamma * S - K beta * S + (gamma - beta) * (K beta * S ^ 2) =
      S * (K gamma - K beta + (gamma - beta) * (K beta * S)) by ring,
    norm_mul]
  have hR' :
      ‖K gamma - K beta + (gamma - beta) * (K beta * S)‖ ≤ C ^ 2 * ‖gamma - beta‖ ^ 2 := by
    simpa [K, S, C] using hR
  calc
    ‖S‖ * ‖K gamma - K beta + (gamma - beta) * (K beta * S)‖ ≤
        C * (C ^ 2 * ‖gamma - beta‖ ^ 2) :=
      mul_le_mul hS hR' (norm_nonneg _) hC
    _ = C ^ 3 * ‖gamma - beta‖ ^ 2 := by ring

private theorem wilsonCylinderSecondActionInsertionCouplingC21_firstIntegrand_integrable
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
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
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let base := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_endpointProduct_integrable H N f g
  have hKmeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta) pathMu :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable
      H N beta).aestronglyMeasurable
  have hSmeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N) pathMu :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_measurable H N).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathMu := by
    have h := (hbase.aestronglyMeasurable.mul hKmeas).mul hSmeas
    simpa [base, Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using h
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hdom : Integrable (fun path => C * |base path|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul C
  apply hdom.mono' hmeas
  filter_upwards with path
  have hK := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
    H N hN beta hbeta path
  have hS := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound
    H N path
  have hSabs : |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ≤ C := by
    simpa [Real.norm_eq_abs, C] using hS
  change
    |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))| ≤ C * |base path|
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
    abs_mul]
  have hfac :
      |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ≤ C := by
    rw [abs_mul]
    calc
      _ ≤ 1 * C := mul_le_mul hK hSabs (abs_nonneg _) zero_le_one
      _ = C := one_mul _
  calc
    |base path| *
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ≤
      |base path| * C :=
        mul_le_mul_of_nonneg_left hfac (abs_nonneg (base path))
    _ = C * |base path| := by ring

/-- Operator remainder for differentiating the first Wilson-action insertion family. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (gamma : ℝ) (hgamma : 0 ≤ gamma) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
      H N hN gamma hgamma -
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
      H N hN beta hbeta +
    (gamma - beta) •
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
        H N hN beta hbeta

private theorem wilsonCylinderSecondActionInsertionCouplingC21_remainder_inner_eq_integral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
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
  have hFg : Integrable (F gamma) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_firstIntegrand_integrable H N hN gamma hgamma f g
  have hFb : Integrable (F beta) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_firstIntegrand_integrable H N hN beta hbeta f g
  have hA2 : Integrable A2 pathMu := by
    simpa [A2, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable H N hN beta hbeta f g
  have hsub : Integrable (fun path => F gamma path - F beta path) pathMu := hFg.sub hFb
  have hscaled : Integrable (fun path => (gamma - beta) * A2 path) pathMu :=
    hA2.const_mul (gamma - beta)
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
  change inner ℝ
    ((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
        H N hN gamma hgamma f -
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
        H N hN beta hbeta f) +
      (gamma - beta) •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN beta hbeta f) g = _
  have hadd :
      inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
            H N hN gamma hgamma f -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
            H N hN beta hbeta f) +
          (gamma - beta) •
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
              H N hN beta hbeta f) g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
            H N hN gamma hgamma f -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
            H N hN beta hbeta f) g +
      inner ℝ
        ((gamma - beta) •
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
            H N hN beta hbeta f) g :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).innerProductSpace.add_left _ _ _
  rw [hadd]
  rw [wilsonCylinderSecondActionInsertionCouplingC21_inner_sub_left H N]
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
  rw [← integral_sub hFg hFb]
  rw [← integral_const_mul]
  have hcombine :
      (∫ path, F gamma path - F beta path ∂pathMu) +
          (∫ path, (gamma - beta) * A2 path ∂pathMu) =
        ∫ path, (F gamma path - F beta path) + (gamma - beta) * A2 path ∂pathMu := by
    symm
    exact integral_add hsub hscaled
  rw [hcombine]
  apply integral_congr_ae
  filter_upwards with path
  simp [F, A2]
  ring

/-- Operator-norm quadratic remainder for the first insertion family. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : ℝ) (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
        H N hN beta hbeta gamma hgamma‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ 3 *
        ‖gamma - beta‖ ^ 2 := by
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let B := C ^ 3 * ‖gamma - beta‖ ^ 2
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (pow_nonneg hC 3) (sq_nonneg _)
  apply wilsonCylinderSecondActionInsertionCouplingC21_opNorm_le_of_inner_bound H N _ B hB
  intro f g
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
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
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) * R path *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_endpointProduct_integrable H N f g
  have hdom : Integrable (fun path => B * |base path|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul B
  have hpoint : ∀ path, ‖D path‖ ≤ B * |base path| := by
    intro path
    have hR := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionInsertion_quadraticRemainder
      H N hN beta gamma hbeta hgamma path
    change |D path| ≤ B * |base path|
    rw [show D path = base path * R path by simp [D, base, R]; ring, abs_mul]
    have hR' : |R path| ≤ B := by
      simpa [R, B, C, Real.norm_eq_abs] using hR
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hR' (abs_nonneg (base path))
  rw [wilsonCylinderSecondActionInsertionCouplingC21_remainder_inner_eq_integral
    H N hN beta hbeta gamma hgamma f g]
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

/-- The second-insertion family on the genuine nonnegative coupling domain. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily
    (H N : ℕ) (hN : 0 < N)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
    H N hN beta.1 beta.2

noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientError
    (H N : ℕ) (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  (gamma.1 - beta.1)⁻¹ •
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily H N hN gamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily H N hN beta) +
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily H N hN beta

private theorem wilsonCylinderSecondActionInsertionCouplingC21_differenceQuotientError_eq
    (H N : ℕ) (hN : 0 < N)
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

private theorem wilsonCylinderSecondActionInsertionCouplingC21_differenceQuotientError_norm_le
    (H N : ℕ) (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling)
    (h : gamma ≠ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientError
        H N hN beta gamma‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ 3 *
        ‖gamma.1 - beta.1‖ := by
  have hval : gamma.1 ≠ beta.1 := by
    intro hval
    apply h
    exact Subtype.ext hval
  have hsub : gamma.1 - beta.1 ≠ 0 := sub_ne_zero.mpr hval
  have hnorm : ‖gamma.1 - beta.1‖ ≠ 0 := norm_ne_zero_iff.mpr hsub
  rw [wilsonCylinderSecondActionInsertionCouplingC21_differenceQuotientError_eq H N hN beta gamma h]
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator
    H N hN beta.1 beta.2 gamma.1 gamma.2
  let B := C ^ 3 * ‖gamma.1 - beta.1‖
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hB : 0 ≤ B := mul_nonneg (pow_nonneg hC 3) (norm_nonneg _)
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  change ‖(gamma.1 - beta.1)⁻¹ • R f‖ ≤ B * ‖f‖
  rw [norm_smul]
  have hRop :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaRemainderOperator_norm_le
      H N hN beta.1 beta.2 gamma.1 gamma.2
  have hRapp :
      ‖R f‖ ≤ (C ^ 3 * ‖gamma.1 - beta.1‖ ^ 2) * ‖f‖ := by
    calc
      ‖R f‖ ≤ ‖R‖ * ‖f‖ := R.le_opNorm f
      _ ≤ (C ^ 3 * ‖gamma.1 - beta.1‖ ^ 2) * ‖f‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
        simpa [R, C] using hRop
  calc
    ‖(gamma.1 - beta.1)⁻¹‖ * ‖R f‖ ≤
        ‖(gamma.1 - beta.1)⁻¹‖ *
          ((C ^ 3 * ‖gamma.1 - beta.1‖ ^ 2) * ‖f‖) :=
      mul_le_mul_of_nonneg_left hRapp (norm_nonneg _)
    _ = B * ‖f‖ := by
      rw [norm_inv]
      dsimp [B]
      field_simp [hnorm]

noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm
    (H N : ℕ) (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) : ℝ :=
  if gamma = beta then 0 else
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientError
        H N hN beta gamma‖

private theorem wilsonCylinderSecondActionInsertionCouplingC21_differenceQuotientErrorNorm_le
    (H N : ℕ) (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN beta gamma ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ 3 *
        ‖gamma.1 - beta.1‖ := by
  by_cases h : gamma = beta
  · subst gamma
    simp [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm]
  · simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm, h] using
      wilsonCylinderSecondActionInsertionCouplingC21_differenceQuotientError_norm_le H N hN beta gamma h

/-- The first Wilson-action insertion is operator-norm differentiable with derivative `-O2`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonAction_hasNonnegativeOperatorNormDerivAt
    (H N : ℕ) (hN : 0 < N)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    Tendsto
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN beta)
      (𝓝 beta) (𝓝 0) := by
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let B := C ^ 3
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hB : 0 ≤ B := pow_nonneg hC 3
  rw [Metric.tendsto_nhds_nhds]
  intro epsilon hepsilon
  by_cases hBzero : B = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro gamma hdist
    have herr := wilsonCylinderSecondActionInsertionCouplingC21_differenceQuotientErrorNorm_le H N hN beta gamma
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
    have herr := wilsonCylinderSecondActionInsertionCouplingC21_differenceQuotientErrorNorm_le H N hN beta gamma
    change periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionBetaDifferenceQuotientErrorNorm
        H N hN beta gamma ≤ B * ‖gamma.1 - beta.1‖ at herr
    have hmul : B * ‖gamma.1 - beta.1‖ < B * (epsilon / B) :=
      mul_lt_mul_of_pos_left hdist' hBpos
    have hcancel : B * (epsilon / B) = epsilon := by field_simp [ne_of_gt hBpos]
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

/-- Pathwise coupling Lipschitz bound for the second insertion `K_beta S²`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertion_norm_sub_le
    (H N : ℕ) (hN : 0 < N) (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ 3 *
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
  have hSsq : ‖S‖ ^ 2 ≤ C ^ 2 := by nlinarith [norm_nonneg S]
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

/-- Global operator-norm Lipschitz bound for the second physical insertion family. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_norm_sub_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : ℝ) (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ 3 *
        ‖gamma - beta‖ := by
  let C := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let B := C ^ 3 * ‖gamma - beta‖
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hB : 0 ≤ B := mul_nonneg (pow_nonneg hC 3) (norm_nonneg _)
  let D :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
        H N hN gamma hgamma -
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
        H N hN beta hbeta
  apply wilsonCylinderSecondActionInsertionCouplingC21_opNorm_le_of_inner_bound H N D B hB
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
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hFg : Integrable (F gamma) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable H N hN gamma hgamma f g
  have hFb : Integrable (F beta) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_secondIntegrand_integrable H N hN beta hbeta f g
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderSecondActionInsertionCouplingC21_endpointProduct_integrable H N f g
  have hdom : Integrable (fun path => B * |base path|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul B
  have hpoint : ∀ path, ‖F gamma path - F beta path‖ ≤ B * |base path| := by
    intro path
    have hfac := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertion_norm_sub_le
      H N hN beta gamma hbeta hgamma path
    change |F gamma path - F beta path| ≤ B * |base path|
    rw [show F gamma path - F beta path = base path *
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2) by
        simp [F, base]
        ring,
      abs_mul]
    have hfac' :
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N gamma path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2 -
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path ^ 2| ≤ B := by
      simpa [B, C, Real.norm_eq_abs] using hfac
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hfac' (abs_nonneg (base path))
  change ‖inner ℝ
      ((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN beta hbeta) f) g‖ ≤ B * ‖f‖ * ‖g‖
  change ‖inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN gamma hgamma f -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator
          H N hN beta hbeta f) g‖ ≤ B * ‖f‖ * ‖g‖
  rw [wilsonCylinderSecondActionInsertionCouplingC21_inner_sub_left H N]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_inner_eq_pathActionSquareIntegral
    H N hN gamma hgamma f g]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_inner_eq_pathActionSquareIntegral
    H N hN beta hbeta f g]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathSecondActionInsertionAmplitude
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

/-- The second-insertion family is globally Lipschitz with coefficient `C^3`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily_norm_sub_le
    (H N : ℕ) (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily H N hN gamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily H N hN beta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ 3 *
        ‖gamma.1 - beta.1‖ := by
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionInsertionOperator_norm_sub_le
      H N hN beta.1 beta.2 gamma.1 gamma.2

/-- Operator-norm `C^{2,1}` certificate on the genuine nonnegative Wilson-coupling half-line.
The first derivative of `T` is `-O`, the derivative of `O` is `-O2`, hence the second derivative
of `T` is `O2`, and the second-derivative field is globally Lipschitz. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransfer_C21_operatorNormCertificate
    (H N : ℕ) (hN : 0 < N)
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
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N ^ 3 *
          ‖gamma.1 - beta.1‖ := by
  refine ⟨periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransfer_hasNonnegativeOperatorNormDerivAt
      H N hN beta, ?_⟩
  refine ⟨periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonAction_hasNonnegativeOperatorNormDerivAt
      H N hN beta, ?_⟩
  intro gamma
  exact periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderSecondWilsonActionFamily_norm_sub_le
    H N hN beta gamma

end
end MathlibAnalytic
end MGAP4D
