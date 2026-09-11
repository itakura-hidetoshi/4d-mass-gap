import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderCellHaarSemantics
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

local instance wilsonCylinderActionHaarSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance wilsonCylinderActionHaarSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance wilsonCylinderActionHaarSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance wilsonCylinderActionHaarSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance wilsonCylinderActionHaarSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance wilsonCylinderActionHaarSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance wilsonCylinderActionHaarSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Transport an adjacent-slice insertion amplitude across an equality of the
number of slabs.  No additional path equivalence is needed when the two finite
path lengths are literally equal. -/
private theorem periodicHypercubicEvenSpecialUnitaryNSlabPairAmplitudeCommonCarrierTransport
    (H N : ℕ)
    (beta : ℝ)
    {n m : ℕ}
    (h : n = m)
    (j : Fin n)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta n j b f g =
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta m (Fin.cast h j) b f g := by
  subst m
  rfl

/-- One positive-half Wilson cell word is exactly the insertion on slab `i` of
the common `H+1`-slab path carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWord_haarAmplitude_eq_commonCarrierAmplitude
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWord H N i)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) i
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
          H N)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
  have hi : i.1 ≤ H := by
    have hlt : i.1 < H + 1 := by
      simpa [periodicHypercubicEvenPositiveHalfCylinderSlabCount] using i.2
    omega
  have htotal :
      i.1 + (H - i.1) + 1 = periodicHypercubicEvenPositiveHalfCylinderSlabCount H := by
    unfold periodicHypercubicEvenPositiveHalfCylinderSlabCount
    omega
  have hindex :
      Fin.cast htotal
          (periodicHypercubicEvenSpecialUnitaryTransferSlabIndex i.1 (H - i.1)) = i := by
    apply Fin.ext
    rfl
  calc
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWord H N i)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude
        H N beta i.1 (H - i.1)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
          H N)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
      unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWord
      simpa [periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord] using
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord_haarAmplitude_eq_amplitude
          H N hN beta hbeta i.1 (H - i.1)
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
            H N)
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable_gaugeInvariant
            H N) f g)
    _ = periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
        H N beta (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) i
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
          H N)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
      unfold periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude
      rw [periodicHypercubicEvenSpecialUnitaryNSlabPairAmplitudeCommonCarrierTransport
        H N beta htotal]
      rw [hindex]

/-- Finite linear combination of all Wilson-cell transfer-word Haar amplitudes
on the positive half-cylinder. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWordHaarAmplitudeSum
    (H N : ℕ)
    (beta : ℝ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) : ℝ :=
  ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWord H N i)
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)

/-- The finite transfer-word sum is the sum of literal pair-observable
insertions on one common `H+1`-slab carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWordHaarAmplitudeSum_eq_commonCarrierSum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWordHaarAmplitudeSum
        H N beta f g =
      ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
          H N beta (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) i
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
            H N)
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWordHaarAmplitudeSum
  apply Finset.sum_congr rfl
  intro i _hi
  exact
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWord_haarAmplitude_eq_commonCarrierAmplitude
      H N hN beta hbeta i f g

/-- The complete positive-half Wilson action inserted into the literal
product-Haar path integral. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionInsertionAmplitude
    (H N : ℕ)
    (beta : ℝ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) : ℝ :=
  ∫ path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N,
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta path *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
        H N path *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
    ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)

/-- Generic measurability carrier for a finite nearest-neighbour path kernel.
Keeping the path length generic avoids expensive reduction of the concrete
positive-half-cylinder index type. -/
private theorem wilsonCylinderActionFinitePathKernel_measurable
    {X : Type*}
    [MeasurableSpace X]
    (K : X × X → ℝ)
    (hK : Measurable K)
    (n : ℕ) :
    Measurable
      (fun path : Fin (n + 1) → X =>
        ∏ i : Fin n, K (path i.castSucc, path i.succ)) := by
  classical
  apply (Finset.univ : Finset (Fin n)).measurable_prod
  intro i _hi
  exact hK.comp
    ((measurable_pi_apply i.castSucc).prodMk (measurable_pi_apply i.succ))

/-- Measurability of the complete positive-half temporal-gauge path kernel. -/
private theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable'
    (H N : ℕ)
    (beta : ℝ) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta) := by
  let K :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun p => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta p.1 p.2
  have hK : Measurable K :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).measurable
  simpa [K,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight] using
    (wilsonCylinderActionFinitePathKernel_measurable K hK
      (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))

/-- A bounded pair observable inserted on any one positive-half slab gives an
integrable endpoint-weighted path integrand.  Endpoint `L² × L² → L¹` is
Hölder; the Wilson path kernel and bounded insertion are a uniform multiplier. -/
private theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderBoundedPairIntegrand_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path *
          b
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let n := periodicHypercubicEvenPositiveHalfCylinderSlabCount H
  have hzero : MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        path (0 : Fin (n + 1))) pathMu μ := by
    simpa [pathMu, μ, n,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (n + 1) => μ) (0 : Fin (n + 1)))
  have hlast : MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        path (Fin.last n)) pathMu μ := by
    simpa [pathMu, μ, n,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (n + 1) => μ) (Fin.last n))
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
  have hbaseMem : MemLp
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last n))) 1 pathMu := by
    simpa using hg2.mul' hf2
  have hbase : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last n))) pathMu := by
    rw [← memLp_one_iff_integrable]
    exact hbaseMem
  have hKmeas : Measurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta) :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable'
      H N beta
  have hbmeas : Measurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        b
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)) := by
    unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft
    unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight
    exact b.continuous.measurable.comp
      ((measurable_pi_apply i.castSucc).prodMk (measurable_pi_apply i.succ))
  have hmeas : AEStronglyMeasurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path *
          b
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last n))) pathMu :=
    (((hf2.1.mul hKmeas.aestronglyMeasurable).mul hbmeas.aestronglyMeasurable).mul hg2.1)
  have hmajor : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        ‖b‖ *
          ((f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last n)))) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.smul ‖b‖
  apply hmajor.mono hmeas
  filter_upwards with path
  have hK :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
      H N hN beta hbeta path
  have hb :
      |b
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)| ≤ ‖b‖ := by
    simpa [Real.norm_eq_abs] using
      b.norm_coe_le_norm
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)
  have hfactor :
      |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path *
        b
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)| ≤ ‖b‖ := by
    rw [abs_mul]
    calc
      _ ≤ 1 * ‖b‖ := mul_le_mul hK hb (abs_nonneg _) zero_le_one
      _ = ‖b‖ := one_mul _
  change
    ‖(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path *
        b
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last n))‖ ≤
      ‖‖b‖ *
        ((f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last n)))‖
  simp only [Real.norm_eq_abs]
  calc
    |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path *
        b
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last n))| =
      |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last n))| *
      |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path *
        b
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)| := by
      rw [show
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta path *
            b
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
                periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i) *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last n)) =
          ((f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last n))) *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta path *
            b
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
                periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)) by ring,
        abs_mul]
    _ ≤ |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last n))| * ‖b‖ :=
      mul_le_mul_of_nonneg_left hfactor (abs_nonneg _)
    _ = ‖b‖ * |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last n))| := by ring
    _ = |‖b‖ *
        ((f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last n)))| := by
      symm
      rw [abs_mul, abs_of_nonneg (norm_nonneg b)]

/-- Summing all common-carrier cell insertions is exactly one insertion of the
complete positive-half Wilson path action. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionInsertionAmplitude_eq_commonCarrierSum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionInsertionAmplitude
        H N beta f g =
      ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
          H N beta (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) i
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
            H N)
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionInsertionAmplitude
  simp_rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_eq_sum_cellObservable]
  calc
    (∫ path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N,
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path *
        (∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
            H N
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)) =
      ∫ path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N,
        ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta path *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
              H N
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
                periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i) *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
      apply integral_congr_ae
      filter_upwards with path
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
        ∫ path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N,
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta path *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
              H N
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
                periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i) *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
      simpa using
        (MeasureTheory.integral_finset_sum
          (μ := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)
          (Finset.univ : Finset (Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
          (f := fun i path =>
            (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
                H N beta path *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
                H N
                (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
                  periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i) *
              (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
                (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
          (by
            intro i _hi
            exact
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderBoundedPairIntegrand_integrable
                H N hN beta hbeta i
                (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
                  H N) f g))
    _ = ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
        periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude
          H N beta (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) i
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
            H N)
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rfl

/-- The finite linear combination of concrete Wilson-cell transfer words is
literally insertion of the complete positive-half Wilson cylinder action. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWordHaarAmplitudeSum_eq_pathActionInsertionAmplitude
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWordHaarAmplitudeSum
        H N beta f g =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionInsertionAmplitude
        H N beta f g := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWordHaarAmplitudeSum_eq_commonCarrierSum
    H N hN beta hbeta f g]
  symm
  exact
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionInsertionAmplitude_eq_commonCarrierSum
      H N hN beta hbeta f g

/-- Genuine Gauss-law operator obtained by summing the actual Wilson cylinder
cell insertion over every slab of the positive half-cylinder. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
    periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabWilsonCylinderCellActionOperator
      H N hN beta hbeta i.1 (H - i.1)

/-- Matrix coefficients of the summed physical cylinder-action operator are the
finite sum of the corresponding concrete transfer-word Haar amplitudes. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_inner_eq_wordSum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN beta hbeta f) g =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWordHaarAmplitudeSum
        H N beta f g := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWordHaarAmplitudeSum
  rw [show
    (∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabWilsonCylinderCellActionOperator
        H N hN beta hbeta i.1 (H - i.1)) f =
      ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
        periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabWilsonCylinderCellActionOperator
          H N hN beta hbeta i.1 (H - i.1) f by simp]
  have hsum :
      inner ℝ
        (∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
          periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabWilsonCylinderCellActionOperator
            H N hN beta hbeta i.1 (H - i.1) f) g =
        ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
          inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabWilsonCylinderCellActionOperator
              H N hN beta hbeta i.1 (H - i.1) f) g := by
    simpa using
      (sum_inner (𝕜 := ℝ)
        (Finset.univ : Finset (Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        (fun i =>
          periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabWilsonCylinderCellActionOperator
            H N hN beta hbeta i.1 (H - i.1) f) g)
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _hi
  symm
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWord
  exact
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord_haarAmplitude_eq_operator_inner
      H N hN beta hbeta i.1 (H - i.1) f g

/-- Final finite-volume identity for this layer: the matrix coefficient of the
genuine physical sum of all Wilson cylinder-cell insertions is exactly the
literal product-Haar path integral with the complete Wilson path action
inserted. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_inner_eq_pathActionIntegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN beta hbeta f) g =
      ∫ path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N,
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
            H N path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  calc
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN beta hbeta f) g =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWordHaarAmplitudeSum
        H N beta f g :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_inner_eq_wordSum
        H N hN beta hbeta f g
    _ = periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionInsertionAmplitude
        H N beta f g :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWordHaarAmplitudeSum_eq_pathActionInsertionAmplitude
        H N hN beta hbeta f g
    _ = _ := by
      rfl

end
end MathlibAnalytic
end MGAP4D