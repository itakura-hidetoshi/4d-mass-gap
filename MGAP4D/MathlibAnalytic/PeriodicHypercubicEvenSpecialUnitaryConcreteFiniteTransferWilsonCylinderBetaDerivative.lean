import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderActionHaarSemantics
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Set
open scoped BigOperators InnerProductSpace Topology

noncomputable section

set_option maxHeartbeats 2000000

local instance wilsonCylinderBetaDerivativeSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance wilsonCylinderBetaDerivativeSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance wilsonCylinderBetaDerivativeSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance wilsonCylinderBetaDerivativeSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance wilsonCylinderBetaDerivativeSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance wilsonCylinderBetaDerivativeSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance wilsonCylinderBetaDerivativeSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The complete positive-half Wilson path action as one bounded continuous
observable on the compact finite path carrier.  This supplies both measurability
and the beta-independent domination needed below. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionBoundedObservable
    (H N : ℕ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N,
      by
        unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
        apply continuous_finset_sum
        intro i _hi
        exact
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
            H N).continuous.comp
            ((continuous_apply i.castSucc).prodMk (continuous_apply i.succ))⟩

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionBoundedObservable_apply
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionBoundedObservable
        H N path =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path :=
  rfl

/-- The complete temporal-gauge path action is uniformly bounded on the finite
compact path carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionBoundedObservable
        H N‖ := by
  simpa using
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionBoundedObservable
      H N).norm_coe_le_norm path

/-- Measurability of the full positive-half path kernel, obtained through its
exact Boltzmann form rather than by unfolding the finite product. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable
    (H N : ℕ)
    (beta : ℝ) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta) := by
  have haction : Measurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N) :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionBoundedObservable
      H N).continuous.measurable
  have hexp : Measurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        Real.exp
          (-beta *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
              H N path)) :=
    Real.measurable_exp.comp (measurable_const.mul haction)
  convert hexp using 1
  funext path
  exact
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_eq_boltzmann
      H N beta path).symm

/-- Pointwise beta derivative of the exact finite-volume Wilson path kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_hasDerivAt_beta
    (H N : ℕ)
    (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    HasDerivAt
      (fun beta' : ℝ =>
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta' path)
      (-periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
          H N path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path)
      beta := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path
  have hlinear : HasDerivAt (fun beta' : ℝ => -beta' * S) (-S) beta := by
    simpa [S] using (hasDerivAt_id (x := beta)).neg.mul_const S
  have hexp : HasDerivAt (fun beta' : ℝ => Real.exp (-beta' * S))
      (Real.exp (-beta * S) * (-S)) beta :=
    hlinear.exp
  simpa only [S,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_eq_boltzmann,
    neg_mul, mul_neg, neg_neg, mul_comm, mul_left_comm, mul_assoc] using hexp

/-- Literal positive-half temporal-gauge endpoint amplitude as a function of
beta.  For nonnegative beta the existing transfer theorem identifies its value
with the physical positive-half transfer matrix coefficient. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude
    (H N : ℕ)
    (beta : ℝ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) : ℝ :=
  ∫ path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N,
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta path *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
    ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)

/-- At nonnegative beta the literal endpoint amplitude is exactly the genuine
physical positive-half transfer matrix coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude_eq_physicalTransfer_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude
        H N beta f g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta f) g := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude
  exact
    periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_temporalGauge_integral_eq_physicalTransfer
      H N hN beta hbeta f g

/-- The product of the two L2 endpoint states is L1 on the common product-Haar
path carrier. -/
private theorem wilsonCylinderBetaDerivative_endpointProduct_integrable
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

/-- For beta >= 0 the endpoint integrand is integrable because the Wilson path
kernel is bounded by one. -/
private theorem wilsonCylinderBetaDerivative_endpointIntegrand_integrable
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
  have hbase := wilsonCylinderBetaDerivative_endpointProduct_integrable H N f g
  have hKmeas :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable
      H N beta).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathMu := by
    have h := hbase.aestronglyMeasurable.mul hKmeas
    convert h using 1
    funext path
    ring
  apply hbase.mono hmeas
  filter_upwards with path
  change
    |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))| ≤
      |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))|
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
    abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
      H N hN beta hbeta path)

/-- The beta derivative of one endpoint-weighted path integrand is minus the
same path integrand with the complete Wilson path action inserted. -/
private theorem wilsonCylinderBetaDerivative_endpointIntegrand_hasDerivAt
    (H N : ℕ)
    (beta : ℝ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    HasDerivAt
      (fun beta' : ℝ =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta' path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      (-((f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
            H N path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))))
      beta := by
  have hK :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_hasDerivAt_beta
      H N beta path
  have h :=
    (hK.const_mul
      ((f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0))).mul_const
      ((g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
  convert h using 1 <;> ring

/-- Differentiation under the finite product-Haar path integral at strictly
positive beta.  The derivative is minus the complete Wilson path-action
insertion amplitude. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude_hasDerivAt_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    HasDerivAt
      (fun beta' : ℝ =>
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude
          H N beta' f g)
      (-periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionInsertionAmplitude
        H N beta f g)
      beta := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let F := fun beta' : ℝ =>
    fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta' path *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  let F' := fun beta' : ℝ =>
    fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
      -((f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta' path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
          H N path *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
  let actionBound :=
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionBoundedObservable
      H N‖
  let bound := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    actionBound *
      |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))|
  have hbase := wilsonCylinderBetaDerivative_endpointProduct_integrable H N f g
  have hboundInt : Integrable bound pathMu := by
    simpa [bound, actionBound, pathMu, Pi.smul_apply, smul_eq_mul] using
      hbase.norm.smul actionBound
  have hFmeas : ∀ᶠ beta' in 𝓝 beta, AEStronglyMeasurable (F beta') pathMu := by
    filter_upwards with beta'
    have hK :=
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable
        H N beta').aestronglyMeasurable
    have h := hbase.aestronglyMeasurable.mul hK
    convert h using 1
    funext path
    simp [F]
    ring
  have hFint : Integrable (F beta) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderBetaDerivative_endpointIntegrand_integrable
        H N hN beta hbeta.le f g
  have hF'meas : AEStronglyMeasurable (F' beta) pathMu := by
    have hK :=
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable
        H N beta).aestronglyMeasurable
    have hS :=
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionBoundedObservable
        H N).continuous.measurable.aestronglyMeasurable
    have h := (hbase.aestronglyMeasurable.mul hK).mul hS
    exact (by
      convert h.neg using 1
      funext path
      simp [F']
      ring)
  have hbound : ∀ᵐ path ∂pathMu, ∀ beta' ∈ Ioi (0 : ℝ), ‖F' beta' path‖ ≤ bound path := by
    filter_upwards with path
    intro beta' hbeta'
    have hK :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
        H N hN beta' (le_of_lt hbeta') path
    have hS :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le
        H N path
    simp only [F', bound, actionBound, Real.norm_eq_abs, norm_neg, abs_mul]
    rw [show
      |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0)| *
          |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta' path| *
          |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| *
          |(g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))| =
        (|(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0)| *
          |(g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))|) *
          (|periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta' path| *
           |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path|) by ring]
    calc
      _ ≤ (|(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0)| *
          |(g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))|) *
          (1 * actionBound) := by
        gcongr
        · exact hK
        · simpa [Real.norm_eq_abs, actionBound] using hS
      _ = actionBound *
          |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
            (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))| := by
        rw [abs_mul]
        ring
  have hdiff : ∀ᵐ path ∂pathMu, ∀ beta' ∈ Ioi (0 : ℝ),
      HasDerivAt (F · path) (F' beta' path) beta' := by
    filter_upwards with path
    intro beta' _hbeta'
    simpa [F, F'] using
      wilsonCylinderBetaDerivative_endpointIntegrand_hasDerivAt H N beta' f g path
  have hparam :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (x₀ := beta) (bound := bound) (μ := pathMu)
      (s := Ioi (0 : ℝ))
      (Ioi_mem_nhds hbeta) hFmeas hFint hF'meas hbound hboundInt hdiff
  have hderiv := hparam.2
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude
  change HasDerivAt (fun beta' : ℝ => ∫ path, F beta' path ∂pathMu)
    (-periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionInsertionAmplitude
      H N beta f g) beta
  convert hderiv using 1
  · simp [F]
  · unfold F'
    rw [integral_neg]
    congr 1
    rfl

/-- Final physical beta-variation identity at strictly positive coupling: the
beta derivative of the literal positive-half endpoint amplitude is minus the
matrix coefficient of the genuine summed Wilson cylinder-action insertion
operator constructed in the previous layer. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude_hasDerivAt_beta_eq_neg_physicalWilsonActionInsertion
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    HasDerivAt
      (fun beta' : ℝ =>
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude
          H N beta' f g)
      (-inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN beta hbeta.le f) g)
      beta := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude_hasDerivAt_beta
      H N hN beta hbeta f g
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_inner_eq_pathActionIntegral
    H N hN beta hbeta.le f g]
  exact h

/-- Derivative-value form of the finite-volume beta-variation identity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude_deriv_beta_eq_neg_physicalWilsonActionInsertion
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    deriv
      (fun beta' : ℝ =>
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude
          H N beta' f g)
      beta =
      -inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
          H N hN beta hbeta.le f) g :=
  (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude_hasDerivAt_beta_eq_neg_physicalWilsonActionInsertion
    H N hN beta hbeta f g).deriv

end

end MathlibAnalytic
end MGAP4D
