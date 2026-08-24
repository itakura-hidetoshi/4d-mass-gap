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

/-- A beta-independent finite bound for the complete positive-half Wilson path
action, obtained by summing the norms of the already-established bounded
one-slab Wilson cell observable. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
    (H N : ℕ) : ℝ :=
  ∑ _i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable H N‖

/-- The complete temporal-gauge Wilson path action is uniformly bounded by the
finite sum of the one-slab cell norms.  This avoids constructing a separate
bounded-continuous function on the full concrete path carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_eq_sum_cellObservable]
  calc
    ‖∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable H N
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)‖ ≤
      ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
        ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable H N
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)‖ := by
        exact norm_sum_le _ _
    _ ≤ ∑ _i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
        ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable H N‖ := by
      apply Finset.sum_le_sum
      intro i _hi
      exact
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
          H N).norm_coe_le_norm
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)
    _ = periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N := rfl

/-- Measurability of the complete positive-half Wilson path action follows by
its canonical finite decomposition into measurable bounded one-slab cells. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_measurable
    (H N : ℕ) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N) := by
  classical
  let b :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable H N
  have hcell : ∀ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
      Measurable
        (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
          b
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)) := by
    intro i
    unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft
    unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight
    exact b.continuous.measurable.comp
      ((measurable_pi_apply i.castSucc).prodMk (measurable_pi_apply i.succ))
  have hsum : ∀ s : Finset (Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)),
      Measurable
        (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
          ∑ i in s,
            b
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
                periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (measurable_const : Measurable
        (fun _ : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N => (0 : ℝ)))
    | @insert a s ha ih =>
        simpa [Finset.sum_insert, ha] using (hcell a).add ih
  convert hsum Finset.univ using 1
  funext path
  simpa [b] using
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_eq_sum_cellObservable
      H N path).symm

/-- Generic measurability carrier for a finite nearest-neighbour path kernel. -/
private theorem wilsonCylinderBetaDerivativeFinitePathKernel_measurable
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

/-- Measurability of the full positive-half path kernel, specialized from the
generic finite nearest-neighbour product carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable
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
    (wilsonCylinderBetaDerivativeFinitePathKernel_measurable K hK
      (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))

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
beta. -/
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
  have hbase : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathMu := by
    simpa [pathMu] using wilsonCylinderBetaDerivative_endpointProduct_integrable H N f g
  have hKmeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta) pathMu :=
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
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
      H N
  let bound := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    actionBound *
      |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))|
  have hbase : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathMu := by
    simpa [pathMu] using wilsonCylinderBetaDerivative_endpointProduct_integrable H N f g
  have hboundInt : Integrable bound pathMu := by
    simpa [bound, actionBound, Pi.smul_apply, smul_eq_mul] using
      hbase.norm.smul actionBound
  have hFmeas : ∀ᶠ beta' in 𝓝 beta, AEStronglyMeasurable (F beta') pathMu := by
    filter_upwards with beta'
    have hK : AEStronglyMeasurable
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta') pathMu :=
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
    have hK : AEStronglyMeasurable
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta) pathMu :=
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable
        H N beta).aestronglyMeasurable
    have hS : AEStronglyMeasurable
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N)
        pathMu :=
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_measurable
        H N).aestronglyMeasurable
    have h := (hbase.aestronglyMeasurable.mul hK).mul hS
    convert h.neg using 1
    funext path
    simp [F']
    ring
  have hbound : ∀ᵐ path ∂pathMu, ∀ beta' ∈ Ioi (0 : ℝ), ‖F' beta' path‖ ≤ bound path := by
    filter_upwards with path
    intro beta' hbeta'
    have hK :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
        H N hN beta' (le_of_lt hbeta') path
    have hS :
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ≤
          actionBound := by
      simpa [Real.norm_eq_abs, actionBound] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound
          H N path
    simp only [F', bound, Real.norm_eq_abs, norm_neg, abs_mul]
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
        · exact hS
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
  simpa [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionInsertionAmplitude]
    using h

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
