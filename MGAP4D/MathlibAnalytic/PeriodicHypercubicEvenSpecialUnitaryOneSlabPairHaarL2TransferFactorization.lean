import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2Transfer
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtSeparableKernelOperator
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

universe u

/-- The canonical middle-coordinate shuffle on four variables,

`((a,b),(c,d)) ↦ ((a,c),(b,d))`.

It is assembled only from measurable product associativity and the swap of the
middle two factors. -/
noncomputable def realL2PairMiddleSwapMeasurableEquiv
    (α : Type u)
    [MeasurableSpace α] :
    ((α × α) × (α × α)) ≃ᵐ ((α × α) × (α × α)) :=
  MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl α)
      MeasurableEquiv.prodAssoc.symm).trans
      ((MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl α)
        (MeasurableEquiv.prodCongr
          MeasurableEquiv.prodComm
          (MeasurableEquiv.refl α))).trans
        ((MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl α)
          MeasurableEquiv.prodAssoc).trans
          MeasurableEquiv.prodAssoc.symm)))

@[simp] theorem realL2PairMiddleSwapMeasurableEquiv_apply
    (α : Type u)
    [MeasurableSpace α]
    (a b c d : α) :
    realL2PairMiddleSwapMeasurableEquiv α ((a, b), (c, d)) =
      ((a, c), (b, d)) := by
  rfl

/-- The middle-coordinate shuffle preserves fourfold copies of the same
measure.  This is the exact product-measure receipt needed to turn the crossed
pair-kernel coordinates into two independent one-slab coordinates. -/
theorem realL2PairMiddleSwapMeasurableEquiv_measurePreserving
    {α : Type u}
    [MeasurableSpace α]
    (μ : Measure α)
    [SFinite μ] :
    MeasurePreserving
      (realL2PairMiddleSwapMeasurableEquiv α)
      ((μ.prod μ).prod (μ.prod μ))
      ((μ.prod μ).prod (μ.prod μ)) := by
  let hId : MeasurePreserving (MeasurableEquiv.refl α) μ μ := by
    simpa using MeasurePreserving.id μ
  let hAssocOuter :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc : ((α × α) × (α × α)) ≃ᵐ
          α × (α × (α × α)))
        ((μ.prod μ).prod (μ.prod μ))
        (μ.prod (μ.prod (μ.prod μ))) := by
    simpa using MeasureTheory.measurePreserving_prodAssoc μ μ (μ.prod μ)
  let hAssocMiddleSymm :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc.symm :
          (α × (α × α)) ≃ᵐ ((α × α) × α))
        (μ.prod (μ.prod μ))
        ((μ.prod μ).prod μ) := by
    simpa using (MeasureTheory.measurePreserving_prodAssoc μ μ μ).symm
  let hRefineAssoc :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl α)
          MeasurableEquiv.prodAssoc.symm)
        (μ.prod (μ.prod (μ.prod μ)))
        (μ.prod ((μ.prod μ).prod μ)) := by
    simpa using hId.prod hAssocMiddleSymm
  let hSwapMiddlePair :
      MeasurePreserving
        (MeasurableEquiv.prodComm : (α × α) ≃ᵐ (α × α))
        (μ.prod μ)
        (μ.prod μ) := by
    refine ⟨MeasurableEquiv.prodComm.measurable, ?_⟩
    simpa using (Measure.prod_swap (μ := μ) (ν := μ))
  let hSwapMiddle :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl α)
          (MeasurableEquiv.prodCongr
            MeasurableEquiv.prodComm
            (MeasurableEquiv.refl α)))
        (μ.prod ((μ.prod μ).prod μ))
        (μ.prod ((μ.prod μ).prod μ)) := by
    simpa using hId.prod (hSwapMiddlePair.prod hId)
  let hAssocMiddle :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc : ((α × α) × α) ≃ᵐ
          α × (α × α))
        ((μ.prod μ).prod μ)
        (μ.prod (μ.prod μ)) := by
    simpa using MeasureTheory.measurePreserving_prodAssoc μ μ μ
  let hCoarsenAssoc :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl α)
          MeasurableEquiv.prodAssoc)
        (μ.prod ((μ.prod μ).prod μ))
        (μ.prod (μ.prod (μ.prod μ))) := by
    simpa using hId.prod hAssocMiddle
  let hAssocOuterSymm :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc.symm :
          (α × (α × (α × α))) ≃ᵐ ((α × α) × (α × α)))
        (μ.prod (μ.prod (μ.prod μ)))
        ((μ.prod μ).prod (μ.prod μ)) := by
    simpa using hAssocOuter.symm
  have hAll :=
    hAssocOuter.trans
      (hRefineAssoc.trans
        (hSwapMiddle.trans
          (hCoarsenAssoc.trans hAssocOuterSymm)))
  simpa [realL2PairMiddleSwapMeasurableEquiv] using hAll

/-- Exact crossed-product integral factorization.  The source grouping is the
literal pair-transfer grouping `((a,b),(c,d))`; after the measure-preserving
middle shuffle it becomes the ordinary product grouping
`((a,c),(b,d))`, where `integral_prod_mul` applies directly. -/
theorem realL2_integral_crossed_pair_mul
    {α : Type u}
    [MeasurableSpace α]
    (μ : Measure α)
    [SFinite μ]
    (F G : α × α → ℝ) :
    (∫ q,
      F (q.1.1, q.2.1) * G (q.1.2, q.2.2)
      ∂((μ.prod μ).prod (μ.prod μ))) =
      (∫ p, F p ∂(μ.prod μ)) * ∫ p, G p ∂(μ.prod μ) := by
  let e := realL2PairMiddleSwapMeasurableEquiv α
  let H : (α × α) × (α × α) → ℝ := fun z => F z.1 * G z.2
  have hPres := realL2PairMiddleSwapMeasurableEquiv_measurePreserving μ
  calc
    (∫ q,
      F (q.1.1, q.2.1) * G (q.1.2, q.2.2)
      ∂((μ.prod μ).prod (μ.prod μ))) =
        ∫ q, H (e q) ∂((μ.prod μ).prod (μ.prod μ)) := by
      rfl
    _ = ∫ z, H z ∂((μ.prod μ).prod (μ.prod μ)) := by
      exact hPres.integral_comp' H
    _ = (∫ p, F p ∂(μ.prod μ)) * ∫ p, G p ∂(μ.prod μ) := by
      exact integral_prod_mul F G

local instance pairTransferFactorizationTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pairTransferFactorizationCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pairTransferFactorizationSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pairTransferFactorizationMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pairTransferFactorizationBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance pairTransferFactorizationSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance pairTransferFactorizationSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Exact integral formula for an arbitrary one-slab matrix coefficient on the
raw spatial-slice Haar `L²` carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner_eq_raw_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f u : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) u =
      ∫ p,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 * f p.1 * u p.2
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner]
  unfold realL2HilbertSchmidtKernelPairing
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
    H N hN beta hbeta
  let tensor := realL2ExternalTensor
    (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) f u
  calc
    inner ℝ K tensor =
        ∫ p,
          inner ℝ (K p) (tensor p)
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
      change
        inner ℝ K tensor =
          ∫ p,
            inner ℝ (K p) (tensor p)
            ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      exact MeasureTheory.L2.inner_def K tensor
    _ = _ := by
      have hK :=
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
          H N hN beta hbeta
      have hfu := realL2ExternalTensor_coeFn
        (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) f u
      apply integral_congr_ae
      filter_upwards [hK, hfu] with p hpK hpfu
      rw [show K p =
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 by simpa [K] using hpK]
      rw [show tensor p = f p.1 * u p.2 by
        simpa [tensor, realL2ExternalTensorFunction] using hpfu]
      rw [realScalarInner_eq_mul]
      ring

/-- Exact integral formula for a decomposable matrix coefficient of the raw
ambient ordered-pair transfer.  The integrand is displayed as the crossed
product of the two one-slab matrix-coefficient integrands, matching the literal
coordinate order of the pair kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_inner_externalTensor_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g u v : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta (realL2ExternalTensor f g))
        (realL2ExternalTensor u v) =
      ∫ q,
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta q.1.1 q.2.1 * f q.1.1 * u q.2.1) *
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta q.1.2 q.2.2 * g q.1.2 * v q.2.2)
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_inner]
  unfold realL2HilbertSchmidtKernelPairing
  rw [MeasureTheory.L2.inner_def]
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μPair := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  have hfg :
      (fun q :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        realL2ExternalTensor f g q.1) =ᵐ[μPair.prod μPair]
      (fun q => f q.1.1 * g q.1.2) := by
    simpa [μ, μPair,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      realL2ExternalTensorFunction] using
      (Measure.quasiMeasurePreserving_fst (μ := μPair) (ν := μPair)).ae_eq
        (realL2ExternalTensor_coeFn f g)
  have huv :
      (fun q :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        realL2ExternalTensor u v q.2) =ᵐ[μPair.prod μPair]
      (fun q => u q.2.1 * v q.2.2) := by
    simpa [μ, μPair,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      realL2ExternalTensorFunction] using
      (Measure.quasiMeasurePreserving_snd (μ := μPair) (ν := μPair)).ae_eq
        (realL2ExternalTensor_coeFn u v)
  apply integral_congr_ae
  filter_upwards
    [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_coeFn
      H N hN beta hbeta,
      realL2ExternalTensor_coeFn
        (μ := μPair) (ν := μPair)
        (realL2ExternalTensor f g) (realL2ExternalTensor u v),
      hfg, huv] with q hK houter hfgq huvq
  rw [hK, houter, realScalarInner_eq_mul]
  simp only [realL2ExternalTensorFunction]
  rw [hfgq, huvq]
  simp only [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel]
  ring

/-- The literal ambient ordered-pair transfer is exactly the tensor product of
the two raw one-slab transfers on all decomposable matrix coefficients.

No normalization is inserted here: this theorem intentionally retains the raw
Wilson transfer normalization on both factors. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_inner_externalTensor_factorization
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g u v : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta (realL2ExternalTensor f g))
        (realL2ExternalTensor u v) =
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta f) u *
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta g) v := by
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_inner_externalTensor_eq_integral,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner_eq_raw_integral,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner_eq_raw_integral]
  exact realL2_integral_crossed_pair_mul
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (fun p =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.1 p.2 * f p.1 * u p.2)
    (fun p =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.1 p.2 * g p.1 * v p.2)

end

end MathlibAnalytic
end MGAP4D