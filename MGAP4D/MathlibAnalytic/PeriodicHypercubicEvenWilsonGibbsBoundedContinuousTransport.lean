import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsReflectionPositivity
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasureInstances
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.ContinuousMap.Bounded.Normed

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Canonical positive open-half `SU(N)` configuration space. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
    (H N : ℕ) :=
  (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
    (Matrix.specialUnitaryGroup (Fin N) ℂ)

/-- Canonical reflection-fixed boundary `SU(N)` configuration space. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
    (H N : ℕ) :=
  (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
    (Matrix.specialUnitaryGroup (Fin N) ℂ)

/-- Since the Wilson action is nonnegative and `beta ≥ 0`, the normalized Gibbs
coordinate density is bounded by the reciprocal partition function. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_le_inv_partitionFunction
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N)) :
    (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta z).toReal ≤
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹ := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let A := (P.boundaryFiberedPiMeasurableEquiv C.base.Gauge).symm z
  have hZ : 0 < C.base.partitionFunction :=
    compact_oriented_partitionFunction_pos C.base
      (continuous_compact_oriented_boltzmannIntegrable C)
  have hAction : 0 ≤ C.base.wilsonAction A :=
    compact_oriented_wilsonAction_nonneg C.base A
  have hExponent : C.base.gibbsExponent A ≤ 0 := by
    unfold CompactOrientedGaugeWilsonSystem.gibbsExponent
    change -beta * C.base.wilsonAction A ≤ 0
    exact neg_nonpos.mpr (mul_nonneg hbeta hAction)
  have hBoltzmann : Real.exp (C.base.gibbsExponent A) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hExponent
  have hRatioNonneg :
      0 ≤ Real.exp (C.base.gibbsExponent A) / C.base.partitionFunction :=
    div_nonneg (Real.exp_nonneg _) hZ.le
  change (ENNReal.ofReal
      (Real.exp (C.base.gibbsExponent A) / C.base.partitionFunction)).toReal ≤
    C.base.partitionFunction⁻¹
  rw [ENNReal.toReal_ofReal hRatioNonneg]
  simpa [one_div] using (div_le_div_iff_of_pos_right hZ).2 hBoltzmann

/-- The boundary-coordinate reflected observable associated with a bounded
continuous positive-half observable is measurable. -/
theorem periodicHypercubicEvenBoundaryReflectedObservable_measurable_of_boundedContinuous
    (H N : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    Measurable (periodicHypercubicEvenBoundaryReflectedObservable H f) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  have hf : Measurable (fun x => f x) := f.continuous.measurable
  have hc : Measurable
      (periodicHypercubicEvenOpenHalfOrientationCorrection
        (H := H) (Gauge := Gauge)) :=
    (periodicHypercubicEvenOpenHalfOrientationCorrectionMeasurableEquiv
      H Gauge).measurable
  unfold periodicHypercubicEvenBoundaryReflectedObservable
  exact
    (hf.comp (measurable_fst.comp measurable_snd)).mul
      (hf.comp (hc.comp (measurable_snd.comp measurable_snd)))

/-- Sup-norm control of the reflected observable in boundary coordinates. -/
theorem periodicHypercubicEvenBoundaryReflectedObservable_norm_le
    (H N : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ)
    (z : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N)) :
    ‖periodicHypercubicEvenBoundaryReflectedObservable H f z‖ ≤ ‖f‖ * ‖f‖ := by
  have hx : |f z.2.1| ≤ ‖f‖ := by
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm z.2.1
  have hy :
      |f (periodicHypercubicEvenOpenHalfOrientationCorrection H z.2.2)| ≤ ‖f‖ := by
    simpa [Real.norm_eq_abs] using
      f.norm_coe_le_norm
        (periodicHypercubicEvenOpenHalfOrientationCorrection H z.2.2)
  unfold periodicHypercubicEvenBoundaryReflectedObservable
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) (norm_nonneg f)

/-- The density-weighted reflected observable is measurable. -/
theorem periodicHypercubicEvenBoundaryWeightedReflectedObservable_measurable_of_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    Measurable
      (periodicHypercubicEvenBoundaryWeightedReflectedObservable
        H N hN beta hbeta f) := by
  have hd :=
    periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_measurable
      H N hN beta hbeta
  have hf :=
    periodicHypercubicEvenBoundaryReflectedObservable_measurable_of_boundedContinuous
      H N f
  unfold periodicHypercubicEvenBoundaryWeightedReflectedObservable
  exact (ENNReal.measurable_toReal.comp hd).mul hf

/-- A bounded continuous positive-half observable automatically supplies every
measurability and integrability receipt needed to transport the full Gibbs
reflection integral to boundary coordinates. -/
noncomputable def
    periodicHypercubicEvenWilsonGibbsReflectionTransportData_of_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    PeriodicHypercubicEvenWilsonGibbsReflectionTransportData
      H N hN beta hbeta f := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H N
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let density := periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
    H N hN beta hbeta
  let coordinateObservable := periodicHypercubicEvenBoundaryReflectedObservable H f
  let weightedObservable := periodicHypercubicEvenBoundaryWeightedReflectedObservable
    H N hN beta hbeta f
  let bound := C.base.partitionFunction⁻¹ * (‖f‖ * ‖f‖)
  letI : IsFiniteMeasure boundaryMeasure := by
    dsimp [boundaryMeasure, periodicHypercubicEvenBoundaryHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
    infer_instance
  letI : IsFiniteMeasure halfMeasure := by
    dsimp [halfMeasure, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  have hCoordinateMeasurable : Measurable coordinateObservable := by
    simpa [coordinateObservable] using
      periodicHypercubicEvenBoundaryReflectedObservable_measurable_of_boundedContinuous
        H N f
  have hWeightedMeasurable : Measurable weightedObservable := by
    simpa [weightedObservable] using
      periodicHypercubicEvenBoundaryWeightedReflectedObservable_measurable_of_boundedContinuous
        H N hN beta hbeta f
  have hZ : 0 < C.base.partitionFunction :=
    compact_oriented_partitionFunction_pos C.base
      (continuous_compact_oriented_boltzmannIntegrable C)
  have hWeightedNorm : ∀ z, ‖weightedObservable z‖ ≤ bound := by
    intro z
    have hd : (density z).toReal ≤ C.base.partitionFunction⁻¹ := by
      simpa [density, C] using
        periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_le_inv_partitionFunction
          H N hN beta hbeta z
    have hfz : ‖coordinateObservable z‖ ≤ ‖f‖ * ‖f‖ := by
      simpa [coordinateObservable] using
        periodicHypercubicEvenBoundaryReflectedObservable_norm_le H N f z
    change ‖(density z).toReal * coordinateObservable z‖ ≤ bound
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul hd hfz (norm_nonneg _) (inv_nonneg.mpr hZ.le)
  refine
    { coordinateAestronglyMeasurable := ?_
      kernelIntegrable := ?_
      fiberKernelIntegrable := ?_ }
  · exact hCoordinateMeasurable.aestronglyMeasurable
  · exact Integrable.of_bound hWeightedMeasurable.aestronglyMeasurable bound
      (Filter.Eventually.of_forall hWeightedNorm)
  · intro b
    have hEmbedding : Measurable
        (fun z : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N => (b, z)) :=
      measurable_const.prod_mk measurable_id
    have hFiberMeasurable : Measurable (fun z => weightedObservable (b, z)) :=
      hWeightedMeasurable.comp hEmbedding
    exact Integrable.of_bound hFiberMeasurable.aestronglyMeasurable bound
      (Filter.Eventually.of_forall fun z => hWeightedNorm (b, z))

end

end MathlibAnalytic
end MGAP4D
