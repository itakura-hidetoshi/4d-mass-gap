import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialCyclicFourLegFockPullback
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryObservableGram
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasurableEquivSymm
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelFeatureMeasurability
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelFeatureNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProduct TensorProduct

noncomputable section

local instance cyclicFourLegL2TopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance cyclicFourLegL2CompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance cyclicFourLegL2SecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance cyclicFourLegL2MeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance cyclicFourLegL2BorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance cyclicFourLegL2HaarLeftInvariant (N : ℕ) :
    Measure.IsMulLeftInvariant
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  unfold normalizedCompactHaar
  infer_instance

/-- Evaluation of a fixed signed physical edge is measurable on the full
finite `SU(N)` configuration product. -/
private theorem periodicHypercubicStepValue_specialUnitary_measurable
    {H N : ℕ}
    (s : PeriodicHypercubicBoundaryStep (PeriodicHypercubicEvenSideLength H)) :
    Measurable
      (fun A : PeriodicHypercubicEvenEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicStepValue A s) := by
  cases hs : s.orientation with
  | forward =>
      simpa [periodicHypercubicStepValue, hs] using
        (measurable_pi_apply s.edge :
          Measurable
            (fun A : PeriodicHypercubicEvenEdge H →
                Matrix.specialUnitaryGroup (Fin N) ℂ => A s.edge))
  | backward =>
      have h :=
        (measurable_pi_apply s.edge :
          Measurable
            (fun A : PeriodicHypercubicEvenEdge H →
                Matrix.specialUnitaryGroup (Fin N) ℂ => A s.edge))
      simpa [periodicHypercubicStepValue, hs] using h.inv

/-- The cyclic three-edge path of any fixed positive-boundary temporal
plaquette is measurable as a function of the full lattice configuration. -/
private theorem periodicHypercubicEvenPositiveBoundaryTemporalOpenPath_measurable
    {H N : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H) :
    Measurable
      (fun A : PeriodicHypercubicEvenEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenPositiveBoundaryTemporalOpenPath A p) := by
  have hstep (k : Fin 4) :
      Measurable
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          periodicHypercubicStepValue A
            (periodicHypercubicBoundaryStep
              (PeriodicHypercubicEvenSideLength H) p k)) :=
    periodicHypercubicStepValue_specialUnitary_measurable
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p k)
  by_cases hbase : (p.1 0).val = 0
  · simp only [periodicHypercubicEvenPositiveBoundaryTemporalOpenPath,
      if_pos hbase]
    exact ((hstep 0).mul (hstep 1)).mul (hstep 2)
  · simp only [periodicHypercubicEvenPositiveBoundaryTemporalOpenPath,
      if_neg hbase]
    exact ((hstep 2).mul (hstep 3)).mul (hstep 0)

/-- Inserting a positive open-half configuration into boundary-fibered
coordinates with identity boundary and negative-half coordinates is measurable. -/
private theorem periodicHypercubicEvenIdentityBoundaryFiberedOpenHalf_measurable
    (H N : ℕ) :
    Measurable
      (fun x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          (fun _ => 1) x (fun _ => 1)) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  have hz :
      Measurable
        (fun x : P.OpenHalfConfiguration Gauge =>
          ((fun _ : P.FixedEdge => (1 : Gauge)),
            (x, (fun _ : P.PositiveEdge => (1 : Gauge))))) := by
    exact measurable_const.prodMk (measurable_id.prodMk measurable_const)
  have h := (P.boundaryFiberedPiMeasurableEquiv Gauge).symm.measurable.comp hz
  have hfun :
      ((P.boundaryFiberedPiMeasurableEquiv Gauge).symm ∘
          (fun x : P.OpenHalfConfiguration Gauge =>
            ((fun _ : P.FixedEdge => (1 : Gauge)),
              (x, (fun _ : P.PositiveEdge => (1 : Gauge)))))) =
        (fun x : P.OpenHalfConfiguration Gauge =>
          P.boundaryFiberedAssemble
            (fun _ => (1 : Gauge)) x (fun _ => (1 : Gauge))) := by
    funext x
    exact P.boundaryFiberedPiMeasurableEquiv_symm_apply Gauge
      ((fun _ : P.FixedEdge => (1 : Gauge)),
        (x, (fun _ : P.PositiveEdge => (1 : Gauge))))
  rw [← hfun]
  exact h

/-- Every canonical temporal-companion open path is measurable on the actual
positive open-half configuration space. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath_measurable
    {H N : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H) :
    Measurable
      (fun x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x p) := by
  unfold periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath
  exact
    (periodicHypercubicEvenPositiveBoundaryTemporalOpenPath_measurable p).comp
      (periodicHypercubicEvenIdentityBoundaryFiberedOpenHalf_measurable H N)

/-- The cyclic holonomy generated by the four canonical temporal-companion open
paths is measurable on the actual positive open-half Haar space. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy_measurable
    (H N : ℕ) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy
        H N) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let μ := normalizedCompactHaar Gauge
  have hlegs :
      Measurable
        (fun x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge =>
          fun k : Fin 4 =>
            periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)) := by
    refine measurable_pi_lambda _ ?_
    intro k
    exact periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath_measurable
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)
  have hword :
      Measurable
        (haarFinFourCyclicPlaquetteWord : (Fin 4 → Gauge) → Gauge) :=
    (measurePreserving_haarFinFourCyclicPlaquetteWord μ).measurable
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy,
    Function.comp_def] using hword.comp hlegs

/-- The normalized real-trace relative kernel has unit diagonal. -/
theorem specialUnitaryNormalizedTraceRelativeKernel_self
    (N : ℕ)
    (hN : 0 < N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryNormalizedTraceRelativeKernel N g g = 1 := by
  unfold specialUnitaryNormalizedTraceRelativeKernel
  rw [show g⁻¹ * g = (1 : Matrix.specialUnitaryGroup (Fin N) ℂ) by group]
  exact normalizedSpecialUnitaryRealTrace_one N hN

/-- The normalized real-trace relative kernel is jointly continuous. -/
theorem continuous_specialUnitaryNormalizedTraceRelativeKernel
    (N : ℕ) :
    Continuous
      (fun p : Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ =>
        specialUnitaryNormalizedTraceRelativeKernel N p.1 p.2) := by
  simp_rw [specialUnitaryNormalizedTraceRelativeKernel_eq_scaled]
  unfold specialUnitaryRealTraceRelativeKernel
  fun_prop

/-- The degree-`n` positive-half cyclic feature is almost-everywhere strongly
measurable for the actual open-half Haar product measure. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature_aestronglyMeasurable
    (H n : ℕ) :
    AEStronglyMeasurable
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature
        H n).feature
      (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  let C := (specialUnitaryNormalizedTraceRelativeKernelFeature
    2 (by norm_num : 0 < (2 : ℕ))).pow n
  have hC : Continuous C.feature :=
    RealHilbertKernelFeature.continuous_feature_of_continuous_kernel C
      (by
        simpa [C] using
          (continuous_specialUnitaryNormalizedTraceRelativeKernel 2).pow n)
  have hHol : AEStronglyMeasurable
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy
        H 2)
      (periodicHypercubicEvenOpenHalfHaarMeasure H 2) :=
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy_measurable
      H 2).aestronglyMeasurable
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature,
    RealHilbertKernelFeature.comap, C] using
    hC.comp_aestronglyMeasurable hHol

/-- Every degree-`n` positive-half cyclic feature vector has norm one. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature_norm_eq_one
    (H n : ℕ)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ‖(periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature
        H n).feature x‖ = 1 := by
  apply RealHilbertKernelFeature.feature_norm_eq_one
  intro y
  simp [specialUnitaryNormalizedTraceRelativeKernel_self 2 (by norm_num : 0 < (2 : ℕ))]

/-- The scalar positive-half dual probe is almost-everywhere strongly
measurable for the actual open-half Haar product measure. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_aestronglyMeasurable
    (H n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    AEStronglyMeasurable
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
        H n q)
      (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  let q' :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeVector
      H n q
  have hFeature :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature_aestronglyMeasurable
      H n
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe,
    q'] using
    (innerSL ℝ q').continuous.comp_aestronglyMeasurable hFeature

/-- Cauchy--Schwarz and the unit feature norm give the sharp uniform dual-probe
bound. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_norm_le
    (H n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ‖periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
        H n q x‖ ≤
      ‖periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeVector
        H n q‖ := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
  calc
    ‖inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeVector
          H n q)
        ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature
          H n).feature x)‖ ≤
      ‖periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeVector
          H n q‖ *
        ‖(periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature
          H n).feature x‖ := norm_inner_le_norm _ _
    _ = ‖periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeVector
          H n q‖ := by
      rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfNormalizedTraceRelativeDegreeFeature_norm_eq_one]
      simp

/-- The actual positive-half scalar dual probe belongs to Haar `L²`. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_memLp
    (H n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    MemLp
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
        H n q)
      2
      (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  letI : IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
    dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  exact MemLp.of_bound
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_aestronglyMeasurable
      H n q)
    ‖periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeVector
      H n q‖
    (Filter.Eventually.of_forall fun x =>
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_norm_le
        H n q x)

/-- Actual open-half Haar `L²` realization of the cyclic temporal-companion
Fock dual probe.  This is the carrier expected by the #1645 rectangular pairing
matrix. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
    (H n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2) :=
  (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_memLp
    H n q).toLp
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
        H n q)

/-- The `L²` probe has the intended scalar temporal-companion dual probe as its
almost-everywhere representative. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_coeFn
    (H n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
      H n q :
      (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) → ℝ) =ᵐ[
          periodicHypercubicEvenOpenHalfHaarMeasure H 2]
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
        H n q := by
  exact
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_memLp
      H n q).coeFn_toLp

end

end MathlibAnalytic
end MGAP4D
