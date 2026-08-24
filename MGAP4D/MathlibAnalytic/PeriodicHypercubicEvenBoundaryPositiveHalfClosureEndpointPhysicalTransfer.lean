import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveHalfClosureTransferKernelBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfTransferPathIteration
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryBoundaryFiberedGibbsFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOpenHalfHaarOrientationCorrectionCore
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

local instance positiveHalfClosureEndpointSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance positiveHalfClosureEndpointSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance positiveHalfClosureEndpointSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfClosureEndpointSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfClosureEndpointSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfClosureEndpointSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfClosureEndpointSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The unfixed positive-half-cylinder kernel is strictly positive.  This is
transported from the already established temporal-gauge path kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_pos
    (H N : ℕ)
    (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :
    0 < periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
      H N beta path U := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_eq_temporalGauge]
  exact
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_pos
      H N beta _

/-- At nonnegative coupling the unfixed positive-half-cylinder kernel has
absolute value at most one.  The noncommutative temporal links are removed by
the exact cumulative temporal-gauge transformation before applying the existing
path-kernel bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_abs_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :
    |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
      H N beta path U| ≤ 1 := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_eq_temporalGauge]
  exact
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
      H N hN beta hbeta _

/-- The completed positive Gram feature is nonnegative directly from the #2065
normalized unfixed-kernel representation. -/
private theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg_from_kernel
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta b x := by
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_normalizedUnfixedPathKernel
    H N hN beta hbeta b x]
  apply mul_nonneg
  · unfold periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
    exact Real.sqrt_nonneg _
  · exact le_of_lt
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_pos
        H N beta
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
          H N (b, x)).1
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
          H N (b, x)).2)

/-- On the diagonal, the completed positive Gram feature is the nonnegative
square root of the orientation-corrected boundary-fibered Gibbs density.  This
is derived here from the already canonical Gram-kernel identity, avoiding a
higher-level reflection-positivity import. -/
private theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_sqrt_diagonalDensity_local
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b x =
      Real.sqrt
        ((periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))).toReal) := by
  let a := periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
    H N hN beta hbeta b x
  have ha : 0 ≤ a := by
    dsimp [a]
    exact
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg_from_kernel
        H N hN beta hbeta b x
  have hd :
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))).toReal =
        a * a := by
    simpa [a, periodicHypercubicEven_real_inner_eq_mul, pow_two] using
      (periodicHypercubicEvenBoundaryDensity_orientationCorrection_eq_inner
        H N hN beta hbeta b x x)
  calc
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b x = a := rfl
    _ = |a| := (abs_of_nonneg ha).symm
    _ = Real.sqrt (a ^ 2) := (Real.sqrt_sq_eq_abs a).symm
    _ = Real.sqrt (a * a) := by rw [pow_two]
    _ = Real.sqrt
        ((periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))).toReal) := by
      rw [hd]

/-- The completed positive Gram feature is jointly measurable in the actual
positive-closure coordinates `(boundary, open half)`. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_joint_measurable
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measurable
      (fun z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
          (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  have hc : Measurable
      (periodicHypercubicEvenOpenHalfOrientationCorrection
        (H := H) (Gauge := Gauge)) :=
    (periodicHypercubicEvenOpenHalfOrientationCorrectionMeasurableEquiv
      H Gauge).measurable
  have hdiag : Measurable
      (fun z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H Gauge =>
        (z.1, (z.2, periodicHypercubicEvenOpenHalfOrientationCorrection H z.2))) :=
    measurable_fst.prodMk (measurable_snd.prodMk (hc.comp measurable_snd))
  have hd :=
    periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_measurable
      H N hN beta hbeta
  have hsqrt : Measurable
      (fun z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H Gauge =>
        Real.sqrt
          ((periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
            H N hN beta hbeta
            (z.1, (z.2,
              periodicHypercubicEvenOpenHalfOrientationCorrection H z.2))).toReal)) :=
    Real.continuous_sqrt.measurable.comp
      ((ENNReal.measurable_toReal.comp hd).comp hdiag)
  have heq :
      (fun z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H Gauge =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2) =
      (fun z =>
        Real.sqrt
          ((periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
            H N hN beta hbeta
            (z.1, (z.2,
              periodicHypercubicEvenOpenHalfOrientationCorrection H z.2))).toReal)) := by
    funext z
    exact
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_sqrt_diagonalDensity_local
        H N hN beta hbeta z.1 z.2
  rw [heq]
  exact hsqrt

/-- The primary spatial endpoint of the transfer coordinates is normalized Haar
when the actual positive closure is distributed by its closure Haar law. -/
private theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosure_primaryEndpoint_measurePreserving
    (H N : ℕ) :
    MeasurePreserving
      (fun z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
          (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
          H N z).1 0)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let pathMu :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let temporalMu :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N
  have hTransfer :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv_measurePreserving_explicitHaar
      H N
  have hFst : MeasurePreserving
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N => p.1)
      (pathMu.prod temporalMu) pathMu := by
    exact MeasureTheory.measurePreserving_fst
  have hEval : MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        path 0)
      pathMu
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
    simpa [pathMu,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) =>
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (0 : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1)))
  have hTransfer' : MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)
      (pathMu.prod temporalMu) := by
    simpa [pathMu, temporalMu,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaarMeasure] using hTransfer
  simpa [Function.comp_def] using hEval.comp (hFst.comp hTransfer')

/-- The antipodal spatial endpoint is also normalized one-slice Haar under the
same closure Haar law. -/
private theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosure_antipodalEndpoint_measurePreserving
    (H N : ℕ) :
    MeasurePreserving
      (fun z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
          (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
          H N z).1
          (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let pathMu :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let temporalMu :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N
  have hTransfer :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv_measurePreserving_explicitHaar
      H N
  have hFst : MeasurePreserving
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N => p.1)
      (pathMu.prod temporalMu) pathMu := by
    exact MeasureTheory.measurePreserving_fst
  have hEval : MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      pathMu
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
    simpa [pathMu,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) =>
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hTransfer' : MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)
      (pathMu.prod temporalMu) := by
    simpa [pathMu, temporalMu,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaarMeasure] using hTransfer
  simpa [Function.comp_def] using hEval.comp (hFst.comp hTransfer')

/-- Endpoint `L²` states remain integrable after pullback to the actual positive
closure, and multiplication by the completed positive Gram feature preserves
integrability because #2065 identifies that feature with the partition
square-root normalization times a kernel bounded by one. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_gaussEndpoints_integrable
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    Integrable
      (fun z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
          (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta z.1 z.2 *
          (f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
              H N z).1 0) *
          (g : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
              H N z).1
              (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N) := by
  let closureMu :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N
  let c :=
    periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
      H N hN beta hbeta
  let f0 := fun z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
      (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N z).1 0)
  let gLast := fun z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
      (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N z).1
        (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hf2 : MemLp f0 2 closureMu := by
    simpa [f0, closureMu, Function.comp_def] using
      (Lp.memLp
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))).comp_measurePreserving
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosure_primaryEndpoint_measurePreserving
          H N)
  have hg2 : MemLp gLast 2 closureMu := by
    simpa [gLast, closureMu, Function.comp_def] using
      (Lp.memLp
        (g : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))).comp_measurePreserving
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosure_antipodalEndpoint_measurePreserving
          H N)
  have hfg : Integrable (fun z => f0 z * gLast z) closureMu :=
    hf2.integrable_mul hg2
  have hc : 0 ≤ c := by
    dsimp [c, periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization]
    exact Real.sqrt_nonneg _
  have hmajor : Integrable (fun z => c * (f0 z * gLast z)) closureMu :=
    hfg.const_mul c
  have hfeature :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_joint_measurable
      H N hN beta hbeta
  apply hmajor.mono
    ((hfeature.aestronglyMeasurable.mul hf2.aestronglyMeasurable).mul
      hg2.aestronglyMeasurable)
  filter_upwards with z
  let path :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
      H N z).1
  let U :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
      H N z).2
  let K :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
      H N beta path U
  have hk0 : 0 ≤ K := by
    exact le_of_lt
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_pos
        H N beta path U)
  have hkAbs : |K| ≤ 1 :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_abs_le_one
      H N hN beta hbeta path U
  have hkLe : K ≤ 1 := le_trans (le_abs_self K) hkAbs
  have hfeatureEq :
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2 = c * K := by
    simpa [c, path, U, K] using
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_normalizedUnfixedPathKernel
        H N hN beta hbeta z.1 z.2
  have hfeature0 :
      0 ≤ periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2 := by
    rw [hfeatureEq]
    exact mul_nonneg hc hk0
  have hfeatureLe :
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2 ≤ c := by
    rw [hfeatureEq]
    simpa using mul_le_mul_of_nonneg_left hkLe hc
  change
    |periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta z.1 z.2 * f0 z * gLast z| ≤
      |c * (f0 z * gLast z)|
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hfeature0, abs_of_nonneg hc]
  calc
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2 * |f0 z| * |gLast z| =
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2 * (|f0 z| * |gLast z|) := by ring
    _ ≤ c * (|f0 z| * |gLast z|) :=
      mul_le_mul_of_nonneg_right hfeatureLe
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = c * |f0 z * gLast z| := by rw [abs_mul]

/-- The normalized endpoint integrand on explicit `(spatial path, temporal
field)` Haar coordinates is integrable.  Rather than rebuilding joint
measurability of the noncommutative unfixed kernel, this is transported through
the already measure-preserving closure equivalence from the integrable OS
closure expression. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalf_normalizedGaussEndpointKernel_integrable
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N =>
        periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
            H N hN beta hbeta *
          ((f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) (p.1 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
              H N beta p.1 p.2 *
            (g : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              (p.1 (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaarMeasure H N) := by
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv H N
  let closureMu :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N
  let nestedMu :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaarMeasure H N
  let G := fun p :
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N =>
    periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
        H N hN beta hbeta *
      ((f : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) (p.1 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
          H N beta p.1 p.2 *
        (g : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
          (p.1 (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
  let F := fun z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
      (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta z.1 z.2 *
      (f : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
        ((e z).1 0) *
      (g : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
        ((e z).1 (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hF : Integrable F closureMu := by
    simpa [F, e, closureMu] using
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_gaussEndpoints_integrable
        H N hN beta hbeta f g
  have hFG : F = fun z => G (e z) := by
    funext z
    dsimp [F, G]
    rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_normalizedUnfixedPathKernel
      H N hN beta hbeta z.1 z.2]
    ring
  have hGcomp : Integrable (fun z => G (e z)) closureMu := by
    rw [← hFG]
    exact hF
  have hGcompLp : MemLp (G ∘ e) 1 closureMu := by
    rw [memLp_one_iff_integrable]
    simpa [Function.comp_def] using hGcomp
  have hGmap : MemLp G 1 (Measure.map e closureMu) := by
    exact (e.memLp_map_measure_iff).2 hGcompLp
  have hTransfer : MeasurePreserving e closureMu nestedMu := by
    simpa [e, closureMu, nestedMu] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv_measurePreserving_explicitHaar
        H N
  have hGLp : MemLp G 1 nestedMu := by
    rw [← hTransfer.map_eq]
    exact hGmap
  have hG : Integrable G nestedMu :=
    (memLp_one_iff_integrable).1 hGLp
  simpa [G, nestedMu] using hG

/-- Terminal theorem for this mathematical unit.  Pairing the completed positive
OS closure feature with Gauss-law states at its two spatial endpoints, and
integrating over the actual positive-closure Haar coordinates, gives exactly
the same partition square-root normalization times the `H+1`-slab physical
transfer matrix element.  This is a finite-volume integral identity; it does not
identify the completed OS Hilbert carrier with the Gauss-law Hilbert carrier. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_gaussEndpoint_integral_eq_normalizedPhysicalTransfer
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∫ z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
        (Matrix.specialUnitaryGroup (Fin N) ℂ),
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2 *
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
          ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N z).1 0) *
        (g : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
          ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N z).1
            (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)) =
      periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
          H N hN beta hbeta *
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
            H N hN beta hbeta f) g := by
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv H N
  let closureMu :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N
  let pathMu :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let temporalMu :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N
  let nestedMu :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaarMeasure H N
  let c :=
    periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
      H N hN beta hbeta
  let G := fun p :
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N =>
    c *
      ((f : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) (p.1 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
          H N beta p.1 p.2 *
        (g : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
          (p.1 (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
  have hTransfer : MeasurePreserving e closureMu nestedMu := by
    simpa [e, closureMu, nestedMu] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv_measurePreserving_explicitHaar
        H N
  have hG : Integrable G nestedMu := by
    simpa [G, c, nestedMu] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalf_normalizedGaussEndpointKernel_integrable
        H N hN beta hbeta f g
  have hChange := hTransfer.integral_comp' G
  calc
    (∫ z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
        (Matrix.specialUnitaryGroup (Fin N) ℂ),
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2 *
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) ((e z).1 0) *
        (g : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
          ((e z).1 (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      ∂closureMu) =
        ∫ z, G (e z) ∂closureMu := by
      apply integral_congr_ae
      filter_upwards with z
      dsimp [G, c]
      rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_normalizedUnfixedPathKernel
        H N hN beta hbeta z.1 z.2]
      ring
    _ = ∫ p, G p ∂nestedMu := hChange
    _ = ∫ U,
        (∫ path,
          c *
            ((f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) (path 0) *
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
                H N beta path U *
              (g : Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
                (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
          ∂pathMu)
        ∂temporalMu := by
      simpa [nestedMu,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaarMeasure,
        pathMu, temporalMu, G] using
        (MeasureTheory.integral_prod_symm G hG)
    _ = c *
        (∫ U,
          (∫ path,
            (f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) (path 0) *
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
                H N beta path U *
              (g : Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
                (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
            ∂pathMu)
          ∂temporalMu) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with U
      rw [integral_const_mul]
    _ = c *
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
            H N hN beta hbeta f) g := by
      rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_unfixed_iteratedHaar_integral_eq_physicalTransfer
        H N hN beta hbeta f g]
    _ = periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
          H N hN beta hbeta *
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
            H N hN beta hbeta f) g := by
      rfl

end

end MathlibAnalytic
end MGAP4D