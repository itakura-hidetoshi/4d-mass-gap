import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCoordinateTransferBridge
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance positiveHalfHaarTemporalGaugeSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance positiveHalfHaarTemporalGaugeSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance positiveHalfHaarTemporalGaugeSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfHaarTemporalGaugeSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfHaarTemporalGaugeSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfHaarTemporalGaugeSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfHaarTemporalGaugeSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Product one-slice Haar law on every spatial slice of the complete positive-half path. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure
    (H N : ℕ) :
    Measure (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :=
  Measure.pi
    (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) =>
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

instance periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaar_isProbabilityMeasure
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure
  infer_instance

/-- Product normalized Haar law on one spatial-slice gauge transformation. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformationHaarMeasure
    (H N : ℕ) :
    Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :=
  Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceVertex H =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))

instance periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformationHaar_isProbabilityMeasure
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformationHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformationHaarMeasure
  infer_instance

/-- Independent product Haar law on the `H+1` temporal-link fields. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure
    (H N : ℕ) :
    Measure (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :=
  Measure.pi
    (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) =>
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformationHaarMeasure H N)

instance periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaar_isProbabilityMeasure
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure
  infer_instance

/-- The explicit nested Haar law on the transfer coordinates: independent spatial paths and
independent temporal-link fields, each themselves finite products of normalized compact Haar. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaarMeasure
    (H N : ℕ) :
    Measure
      (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :=
  (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N).prod
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N)

instance periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaar_isProbabilityMeasure
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaarMeasure
  infer_instance

/-- Mathlib's product-measure curry theorem identifies the flat `H+2` spatial-link product Haar
with the path of one-slice product Haar laws. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPath_measurePreserving_haar
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv H N)
      (Measure.pi
        (fun _ : PeriodicHypercubicEvenPositiveHalfFlatSpatialPathIndex H =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let mu : Fin (H + 2) → PeriodicHypercubicEvenSpatialSliceLink H →
      Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun _ _ => normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  have hmap := Measure.infinitePi_map_curry mu
  simp_rw [Measure.infinitePi_eq_pi] at hmap
  refine ⟨
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv H N).measurable,
    ?_⟩
  simpa [mu,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure,
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount] using hmap

/-- The same curry theorem identifies the flat `H+1` temporal-vertex product Haar with the
finite path of one-slice gauge-transformation Haar laws. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalField_measurePreserving_haar
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv H N)
      (Measure.pi
        (fun _ : PeriodicHypercubicEvenPositiveHalfFlatTemporalFieldIndex H =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N) := by
  let mu : Fin (H + 1) → PeriodicHypercubicEvenSpatialSliceVertex H →
      Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun _ _ => normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  have hmap := Measure.infinitePi_map_curry mu
  simp_rw [Measure.infinitePi_eq_pi] at hmap
  refine ⟨
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv H N).measurable,
    ?_⟩
  simpa [mu,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure,
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformationHaarMeasure,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount] using hmap

/-- The #2060 flat-to-transfer coordinate map preserves the fully explicit nested Haar law. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinates_measurePreserving_explicitHaar
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv
        H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureFlatHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaarMeasure H N) := by
  have h :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPath_measurePreserving_haar
      H N).prod
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalField_measurePreserving_haar
        H N)
  simpa [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureFlatHaarMeasure,
    periodicHypercubicEvenPositiveHalfClosureFlatCoordinatePiMeasure,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaarMeasure,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv] using h

/-- The pushforward Haar law introduced in #2060 is exactly the iterated one-slice/one-gauge
product Haar law, not merely an abstract mapped measure. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfNestedCoordinateHaarMeasure_eq_explicit
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfNestedCoordinateHaarMeasure H N =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaarMeasure H N := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfNestedCoordinateHaarMeasure
  exact
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinates_measurePreserving_explicitHaar
      H N).map_eq

/-- Consequently the actual positive-closure coordinates map measure-preservingly directly to the
explicit product of spatial-path Haar and temporal-field Haar. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv_measurePreserving_explicitHaar
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaarMeasure H N) := by
  rw [← periodicHypercubicEvenSpecialUnitaryPositiveHalfNestedCoordinateHaarMeasure_eq_explicit]
  exact
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv_measurePreserving
      H N

/-- A fixed spatial lattice gauge transformation is a measurable self-equivalence of one-slice
configuration space; its inverse is the pointwise inverse gauge transformation. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeMeasurableEquiv
    (H N : ℕ)
    (gamma : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ≃ᵐ
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N where
  toFun := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N gamma
  invFun := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N gamma⁻¹
  left_inv A := by
    calc
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N gamma⁻¹
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N gamma A) =
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N (gamma⁻¹ * gamma) A :=
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_mul
            H N gamma⁻¹ gamma A).symm
      _ = A := by simp
  right_inv A := by
    calc
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N gamma
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N gamma⁻¹ A) =
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N (gamma * gamma⁻¹) A :=
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_mul
            H N gamma gamma⁻¹ A).symm
      _ = A := by simp
  measurable_toFun :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H N gamma).measurable
  measurable_invFun :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H N gamma⁻¹).measurable

/-- For a fixed temporal field, the cumulative temporal-gauge transformation on every spatial
slice is a measurable self-equivalence of the whole path space. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugeSpatialPathMeasurableEquiv
    (H N : ℕ)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :
    PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ≃ᵐ
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N :=
  MeasurableEquiv.piCongrRight fun j =>
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeMeasurableEquiv H N
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge H N U j)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugeSpatialPathMeasurableEquiv_apply
    (H N : ℕ)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugeSpatialPathMeasurableEquiv
        H N U path =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath
        H N U path := by
  rfl

/-- The cumulative temporal-gauge transformation preserves the complete spatial-path Haar law in
one shot, by Mathlib's finite Pi measure-preservation theorem and the canonical one-slice receipt. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugeSpatialPath_measurePreserving
    (H N : ℕ)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugeSpatialPathMeasurableEquiv
        H N U)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  have h := MeasureTheory.measurePreserving_pi
    (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) =>
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) =>
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (fun j =>
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H N
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge H N U j))
  simpa [periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugeSpatialPathMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeMeasurableEquiv] using h

/-- For every fixed temporal field, the #2057 pointwise gauge reduction becomes an exact Haar
change-of-variables identity for the complete path kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfUnfixedPathKernel_integral_eq_temporalGauge
    (H N : ℕ)
    (beta : ℝ)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :
    (∫ path,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
        H N beta path U
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)) =
      ∫ path,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  calc
    (∫ path,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
        H N beta path U
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)) =
        ∫ path,
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugeSpatialPathMeasurableEquiv
              H N U path)
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
      apply integral_congr_ae
      filter_upwards with path
      simpa using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_eq_temporalGauge
          H N beta path U
    _ = ∫ path,
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
      exact
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugeSpatialPath_measurePreserving
          H N U).integral_comp'
          (fun path =>
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta path)

/-- A Gauss-law `L²` state is pointwise gauge invariant almost everywhere for each fixed spatial
lattice gauge transformation.  This is derived directly from the canonical pullback definition and
its fixed-submodule membership, without passing through the orthogonal projector. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariant_ae
    (H N : ℕ)
    (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (hg : g ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (gamma : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    (fun A =>
      g (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N gamma A)) =ᵐ[
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      fun A => g A := by
  have hPull :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N gamma g =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
        fun A =>
          g (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N gamma A) := by
    simpa [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry,
      Function.comp_def] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving g
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H N gamma))
  have hFixed :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N gamma g = g :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_mem H N g).1 hg gamma
  rw [hFixed] at hPull
  exact hPull.symm

/-- The antipodal residual gauge produced by temporal gauge fixing is invisible almost everywhere
to a terminal Gauss-law state, after lifting the one-slice a.e. identity through the terminal path
evaluation map. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfTerminalGaugeInvariant_ae
    (H N : ℕ)
    (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (hg : g ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :
    (fun path =>
      g ((periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath
        H N U path) (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) =ᵐ[
        periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N]
      fun path =>
        g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) := by
  let gamma :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTerminalGauge H N U
  have hSlice :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariant_ae H N g hg gamma
  have hEval :=
    (MeasureTheory.measurePreserving_eval
      (mu := fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))).quasiMeasurePreserving.ae_eq
      hSlice
  filter_upwards [hEval] with path hpath
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath_last]
  exact hpath

/-- Fixed-`U` physical endpoint amplitude: temporal gauge is an exact path-Haar change of variables.
The primary endpoint is fixed pointwise, while the antipodal residual is removed only through the
Gauss-law a.e. invariance of the terminal state. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_unfixed_integral_eq_temporalGauge
    (H N : ℕ)
    (beta : ℝ)
    (f g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (hg : g ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :
    (∫ path,
      f (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
          H N beta path U *
        g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)) =
      ∫ path,
        f (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path *
          g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let gaugeEquiv :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugeSpatialPathMeasurableEquiv
      H N U
  have hTerminal :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfTerminalGaugeInvariant_ae H N g hg U
  calc
    (∫ path,
      f (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
          H N beta path U *
        g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)) =
        ∫ path,
          f ((gaugeEquiv path) 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta (gaugeEquiv path) *
            g ((gaugeEquiv path)
              (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
      apply integral_congr_ae
      filter_upwards [hTerminal] with path hterminal
      rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_eq_temporalGauge]
      change
        f (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta (gaugeEquiv path) *
            g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) = _
      rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath_zero]
      exact congrArg
        (fun x =>
          f (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta (gaugeEquiv path) * x)
        hterminal.symm
    _ = ∫ path,
          f (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta path *
            g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
      exact
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugeSpatialPath_measurePreserving
          H N U).integral_comp'
          (fun path =>
            f (path 0) *
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
                H N beta path *
              g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))

/-- After integrating the temporal-link field against its normalized product Haar law, the entire
unfixed positive-half endpoint amplitude is exactly the temporal-gauge spatial-path amplitude on the
Gauss-law terminal sector.  No terminal residual is canceled pointwise. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_iteratedHaar_integral_eq_temporalGauge
    (H N : ℕ)
    (beta : ℝ)
    (f g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (hg : g ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∫ U,
      (∫ path,
        f (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
            H N beta path U *
          g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N))
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N)) =
      ∫ path,
        f (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path *
          g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  calc
    (∫ U,
      (∫ path,
        f (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
            H N beta path U *
          g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N))
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N)) =
        ∫ _U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N,
          (∫ path,
            f (path 0) *
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
                H N beta path *
              g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
            ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N))
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N) := by
      apply integral_congr_ae
      filter_upwards with U
      exact
        periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_unfixed_integral_eq_temporalGauge
          H N beta f g hg U
    _ = ∫ path,
          f (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta path *
            g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
      simp

end

end MathlibAnalytic
end MGAP4D