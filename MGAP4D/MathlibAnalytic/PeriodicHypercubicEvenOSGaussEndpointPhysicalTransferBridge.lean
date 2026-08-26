import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSPositiveHalfClosureHaarPathTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfTransferPathIteration
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance osGaussEndpointPhysicalTransferSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osGaussEndpointPhysicalTransferSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osGaussEndpointPhysicalTransferSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osGaussEndpointPhysicalTransferSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osGaussEndpointPhysicalTransferSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osGaussEndpointPhysicalTransferSpatialSliceVertexFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance osGaussEndpointPhysicalTransferSpatialSliceLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The spatial lattice gauge action is jointly measurable in the gauge field
and the one-slice configuration.  This direct Pi-coordinate receipt avoids
introducing a large product-topology continuity obligation merely for Fubini. -/
private theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_measurable_joint
    (H N : ℕ) :
    Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N p.1 p.2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
  apply measurable_pi_lambda
  intro e
  exact
    (((measurable_pi_apply e.1).comp measurable_fst).mul
      ((measurable_pi_apply e).comp measurable_snd)).mul
      (((measurable_pi_apply
        (periodicHypercubicEvenSpatialSliceShift H e.1 e.2)).comp measurable_fst).inv)

/-- Joint measurability of one unfixed slab kernel, obtained by the existing
pointwise temporal-gauge reduction with the lower gauge fixed to the identity. -/
private theorem periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabKernel_measurable_joint
    (H N : ℕ) (beta : ℝ) :
    Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabKernel
          H N beta p.1 p.2.1 p.2.2) := by
  let T := fun p :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
      p.1
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N p.2.1 p.2.2)
  have hGaugeInput : Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        (p.2.1, p.2.2)) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp measurable_snd)
  have hGauge : Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N p.2.1 p.2.2) :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_measurable_joint H N).comp
      hGaugeInput
  have hPair : Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        (p.1,
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N p.2.1 p.2.2)) :=
    measurable_fst.prodMk hGauge
  have hT : Measurable T :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).measurable.comp hPair
  have hEq :
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabKernel
          H N beta p.1 p.2.1 p.2.2) = T := by
    funext p
    calc
      periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabKernel
          H N beta p.1 p.2.1 p.2.2 =
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N 1 p.1)
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N
            (1 * p.2.1) p.2.2) :=
        periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabKernel_eq_temporalGauge
          H N beta 1 p.2.1 p.1 p.2.2
      _ = T p := by
        simp only [one_mul,
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_one]
        rfl
  rw [hEq]
  exact hT

/-- The complete unfixed positive-half path kernel is jointly measurable in the
spatial path and all temporal-link fields. -/
private theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_measurable_joint
    (H N : ℕ) (beta : ℝ) :
    Measurable
      (fun q :
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N =>
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
          H N beta q.1 q.2) := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
  apply (Finset.univ :
    Finset (Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))).measurable_prod
  intro i _hi
  have hLower : Measurable
      (fun q :
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N =>
        q.1 i.castSucc) :=
    (measurable_pi_apply i.castSucc).comp measurable_fst
  have hTemporal : Measurable
      (fun q :
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N =>
        q.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hUpper : Measurable
      (fun q :
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N =>
        q.1 i.succ) :=
    (measurable_pi_apply i.succ).comp measurable_fst
  exact
    (periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabKernel_measurable_joint H N beta).comp
      (hLower.prodMk (hTemporal.prodMk hUpper))

/-- The physical endpoint integrand on explicit path × temporal-field Haar is
integrable.  The endpoint factor is `L² × L² ⊂ L¹` on path Haar, and the
unfixed Wilson kernel is jointly measurable and pointwise bounded by one. -/
private theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_unfixed_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    Integrable
      (fun q :
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N =>
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
            H N beta q.1 q.2 *
          (f (q.1 0) *
            g (q.1 (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))))
      ((periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N)) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let pathμ := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let temporalμ := periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N
  have hEvalZero :=
    MeasureTheory.measurePreserving_eval
      (μ := fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) => μ)
      (0 : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1))
  have hEvalLast :=
    MeasureTheory.measurePreserving_eval
      (μ := fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) => μ)
      (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
  have hfPath2 : MemLp (fun path :
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        f (path 0)) 2 pathμ := by
    have h := (Lp.memLp f).comp_measurePreserving hEvalZero
    simpa [μ, pathμ,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure,
      Function.comp_def] using h
  have hgPath2 : MemLp (fun path :
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) 2 pathμ := by
    have h := (Lp.memLp g).comp_measurePreserving hEvalLast
    simpa [μ, pathμ,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure,
      Function.comp_def] using h
  have hEndpointPath : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        f (path 0) *
          g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathμ := by
    rw [← memLp_one_iff_integrable]
    exact hgPath2.mul' hfPath2
  have hEndpointProd : Integrable
      (fun q :
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N =>
        f (q.1 0) *
          g (q.1 (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      (pathμ.prod temporalμ) := by
    exact hEndpointPath.comp_fst temporalμ
  have hKernelMeas : AEStronglyMeasurable
      (fun q :
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N =>
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
          H N beta q.1 q.2)
      (pathμ.prod temporalμ) :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_measurable_joint
      H N beta).aestronglyMeasurable
  apply hEndpointProd.mono
    (hKernelMeas.mul hEndpointProd.aestronglyMeasurable)
  filter_upwards with q
  have hk :
      |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
          H N beta q.1 q.2| ≤ 1 := by
    rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_eq_temporalGauge]
    exact
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
        H N hN beta hbeta _
  change
    |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
        H N beta q.1 q.2 *
      (f (q.1 0) *
        g (q.1 (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))| ≤
      |f (q.1 0) *
        g (q.1 (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))|
  rw [abs_mul]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hk
      (abs_nonneg
        (f (q.1 0) *
          g (q.1 (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))))

/-- On explicit nested Haar coordinates, the endpoint-local unfixed positive-half
path amplitude is exactly the physical `H+1`-slab transfer matrix coefficient.
This is the Fubini seam between the OS coordinate transport and the existing
temporal-gauge/transfer-iteration spine. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_nestedHaar_integral_eq_physicalTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∫ q,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
          H N beta q.1 q.2 *
        ((f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            (q.1 0) *
          (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            (q.1 (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfNestedCoordinateHaarMeasure H N)) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta f) g := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfNestedCoordinateHaarMeasure_eq_explicit]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfExplicitNestedHaarMeasure
  have hInt :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_unfixed_integrable
      H N hN beta hbeta
      (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  rw [MeasureTheory.integral_prod_symm _ hInt]
  calc
    (∫ U,
      ∫ path,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
            H N beta path U *
          ((f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              (path 0) *
            (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N)) =
      ∫ U,
        (∫ path,
          (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              (path 0) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
              H N beta path U *
            (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N) := by
      apply integral_congr_ae
      filter_upwards with U
      apply integral_congr_ae
      filter_upwards with path
      ring
    _ = _ :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_unfixed_iteratedHaar_integral_eq_physicalTransfer
        H N hN beta hbeta f g

/-- The genuine unnormalized OS positive-half closure amplitude, with insertions
localized only at its two spatial endpoints, is exactly the physical
`H+1`-slab transfer matrix coefficient on the Gauss-law Hilbert space.

General bulk insertions are intentionally excluded from this specialization:
#2260 continues to transport those as genuine path observables. -/
theorem periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude_GaussEndpoint_closureIntegral_eq_physicalTransfer
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∫ z,
      periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
          H N hN beta hbeta z.1 z.2 *
        ((f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
              H N z).1 0) *
          (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
              H N z).1
              (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta f) g := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv H N
  have hTransport :=
    periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude_closureIntegral_eq_nestedPathIntegral
      H N hN beta hbeta
      (fun z =>
        (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            ((E z).1 0) *
          (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            ((E z).1 (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
  calc
    _ = ∫ q,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
            H N beta q.1 q.2 *
          ((f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              (q.1 0) *
            (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              (q.1 (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfNestedCoordinateHaarMeasure H N) := by
      rw [hTransport]
      apply integral_congr_ae
      filter_upwards with q
      simp [E]
    _ = _ :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_nestedHaar_integral_eq_physicalTransfer
        H N hN beta hbeta f g

end

end MathlibAnalytic
end MGAP4D
