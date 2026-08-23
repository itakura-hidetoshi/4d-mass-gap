import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferFactorization
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

universe u v

/-- The bounded analysis operator associated with an arbitrary Hilbert-valued
`L²` feature.  This is the continuous bilinear Hölder pairing

`(Φ, f) ↦ ∫ x, f x • Φ x ∂μ`

curried in the feature variable. -/
noncomputable def realL2HilbertFeatureAnalysisFamily
    {α : Type u}
    [MeasurableSpace α]
    (μ : Measure α)
    (H : Type v)
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace H] :
    Lp H 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] H :=
  ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] H →L[ℝ] H).lpPairing μ 2 2).flip

/-- The generic feature-analysis family evaluates to the literal Bochner
integral. -/
theorem realL2HilbertFeatureAnalysisFamily_apply
    {α : Type u}
    [MeasurableSpace α]
    (μ : Measure α)
    (H : Type v)
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Φ : Lp H 2 μ)
    (f : Lp ℝ 2 μ) :
    realL2HilbertFeatureAnalysisFamily μ H Φ f =
      ∫ x, f x • Φ x ∂μ := by
  change
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] H →L[ℝ] H).lpPairing μ 2 2 f Φ = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  rfl

/-- An `L²` simple Hilbert-valued feature gives a compact analysis operator.
Its image lies in the finite-dimensional span of the finite range of a simple
representative. -/
theorem realL2HilbertFeatureAnalysisFamily_simple_isCompact
    {α : Type u}
    [MeasurableSpace α]
    {μ : Measure α}
    [IsProbabilityMeasure μ]
    (H : Type v)
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Φs : Lp.simpleFunc H 2 μ) :
    IsCompactOperator
      (realL2HilbertFeatureAnalysisFamily μ H (Φs : Lp H 2 μ)) := by
  let s : SimpleFunc α H := Lp.simpleFunc.toSimpleFunc Φs
  let V : Submodule ℝ H := Submodule.span ℝ (Set.range s)
  have hsfinite : (Set.range s).Finite := s.finite_range
  letI : FiniteDimensional ℝ V := by
    dsimp [V]
    exact FiniteDimensional.span_of_finite ℝ hsfinite
  have hVclosed : IsClosed (V : Set H) := by
    exact V.closed_of_finiteDimensional
  let A : Lp ℝ 2 μ →L[ℝ] H :=
    realL2HilbertFeatureAnalysisFamily μ H (Φs : Lp H 2 μ)
  have hRange : ∀ f : Lp ℝ 2 μ, A f ∈ V := by
    intro f
    have hInt : Integrable (fun x => f x • (Φs : Lp H 2 μ) x) μ := by
      rw [← memLp_one_iff_integrable]
      exact
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] H →L[ℝ] H).memLp_of_bilin
          1 (Lp.memLp f) (Lp.memLp (Φs : Lp H 2 μ))
    have hsAE :
        (fun x => (Φs : Lp H 2 μ) x) =ᵐ[μ] s :=
      (Lp.simpleFunc.toSimpleFunc_eq_toFun Φs).symm
    have hPoint : ∀ᵐ x ∂μ, f x • (Φs : Lp H 2 μ) x ∈ V := by
      filter_upwards [hsAE] with x hx
      rw [hx]
      apply V.smul_mem
      exact Submodule.subset_span ⟨x, rfl⟩
    change ∫ x, f x • (Φs : Lp H 2 μ) x ∂μ ∈ V
    exact V.convex.integral_mem hVclosed hPoint hInt
  let AV : Lp ℝ 2 μ →L[ℝ] V := A.codRestrict V hRange
  have hAV : IsCompactOperator AV :=
    isCompactOperator_of_locallyCompactSpace_dom AV
  have hA : IsCompactOperator A := by
    have hcomp := hAV.clm_comp V.subtypeL
    simpa [AV, A] using hcomp
  simpa [A] using hA

/-- Every Hilbert-valued `L²` feature gives a compact analysis operator.
Simple features are dense in `L²`, and compact operators are closed in the
operator norm. -/
theorem realL2HilbertFeatureAnalysisFamily_isCompact
    {α : Type u}
    [MeasurableSpace α]
    {μ : Measure α}
    [IsProbabilityMeasure μ]
    (H : Type v)
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Φ : Lp H 2 μ) :
    IsCompactOperator (realL2HilbertFeatureAnalysisFamily μ H Φ) := by
  have hDense : Dense (Lp.simpleFunc H 2 μ : Set (Lp H 2 μ)) :=
    Lp.simpleFunc.dense (E := H) (μ := μ) (p := 2) (by norm_num)
  have hmem : Φ ∈ closure (Lp.simpleFunc H 2 μ : Set (Lp H 2 μ)) :=
    hDense Φ
  rw [mem_closure_iff_seq_limit] at hmem
  rcases hmem with ⟨Φn, hΦn, hΦnlim⟩
  let F : Lp H 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] H :=
    realL2HilbertFeatureAnalysisFamily μ H
  have hlim : Tendsto (fun n => F (Φn n)) atTop (𝓝 (F Φ)) :=
    F.continuous.continuousAt.tendsto.comp hΦnlim
  apply isCompactOperator_of_tendsto hlim
  filter_upwards with n
  exact
    realL2HilbertFeatureAnalysisFamily_simple_isCompact H
      (⟨Φn n, hΦn n⟩ : Lp.simpleFunc H 2 μ)

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

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance periodicHypercubicEvenSpecialUnitarySpatialSliceHaarCompact_isProbability
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The continuous canonical Moore--Aronszajn feature is an actual
Hilbert-valued `L²` vector over normalized spatial-slice Haar measure. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_memLp_two
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).feature
      2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
      H N hN beta hbeta
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hmeas : AEStronglyMeasurable C.feature μ :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_continuous
      H N hN beta hbeta).aestronglyMeasurable
  have htop : MemLp C.feature ∞ μ :=
    memLp_top_of_bound hmeas 1 <| by
      filter_upwards with A
      exact
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_norm_le_one
          H N hN beta hbeta A
  exact htop.mono_exponent (by norm_num)

/-- Canonical `L²` vector represented by the actual one-slab Moore--Aronszajn
feature. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeatureL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert
      2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_memLp_two
    H N hN beta hbeta).toLp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).feature

/-- The canonical feature `L²` vector has the literal continuous feature as an
a.e. representative. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeatureL2_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeatureL2
        H N hN beta hbeta =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).feature := by
  exact MemLp.coeFn_toLp
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_memLp_two
      H N hN beta hbeta)

/-- The existing actual Moore--Aronszajn analysis operator is exactly the
generic `L²` feature-analysis operator associated with the canonical feature
vector. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator_eq_featureL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
        H N hN beta hbeta =
      realL2HilbertFeatureAnalysisFamily
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
          H N hN beta hbeta).FeatureHilbert
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeatureL2
          H N hN beta hbeta) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator_apply]
  rw [realL2HilbertFeatureAnalysisFamily_apply]
  apply integral_congr_ae
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeatureL2_coeFn
      H N hN beta hbeta] with A hA
  rw [hA]

/-- The actual ambient one-slab feature-analysis operator is compact. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator_isCompact
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsCompactOperator
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
        H N hN beta hbeta) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator_eq_featureL2]
  exact
    realL2HilbertFeatureAnalysisFamily_isCompact
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeatureL2
        H N hN beta hbeta)

/-- The actual ambient one-slab transfer is compact.  This is the first
compactness statement for the complete Hilbert--Schmidt lattice transfer, not
a finite-dimensional truncation. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_isCompact
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsCompactOperator
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta) := by
  let A :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
      H N hN beta hbeta
  have hA : IsCompactOperator A :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator_isCompact
      H N hN beta hbeta
  have hcomp := hA.clm_comp (A†)
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_eq_adjoint_comp_analysis]
  simpa [A] using hcomp

/-- The actual physical Gauss-law one-slab transfer is compact. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isCompact
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsCompactOperator
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta) := by
  let V := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
    H N hN beta hbeta
  have hT : IsCompactOperator T :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_isCompact
      H N hN beta hbeta
  have hpre : IsCompactOperator (T.comp V.subtypeL) := hT.comp_clm V.subtypeL
  have hclosed : IsClosed (V : Set
      (Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) := by
    exact periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed H N
  have hcod := hpre.codRestrict
    (fun f =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_preserves_GaussLaw
        H N hN beta hbeta f.property)
    hclosed
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator, V, T] using hcod

/-- Audit-visible compactness receipt for the actual finite-volume one-slab
dynamics. -/
structure PeriodicHypercubicEvenSpecialUnitaryOneSlabCompactnessPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  featureMemL2 :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).feature
      2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
  analysisCompact :
    IsCompactOperator
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
        H N hN beta hbeta)
  ambientTransferCompact :
    IsCompactOperator
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta)
  physicalTransferCompact :
    IsCompactOperator
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta)

/-- Construct the actual finite-volume one-slab compactness receipt. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSlabCompactnessPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryOneSlabCompactnessPackage
      H N hN beta hbeta :=
  { featureMemL2 :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_memLp_two
        H N hN beta hbeta
    analysisCompact :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator_isCompact
        H N hN beta hbeta
    ambientTransferCompact :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_isCompact
        H N hN beta hbeta
    physicalTransferCompact :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isCompact
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
