import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWordHaarPathSemantics

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- The chronological transfer word carrying the actual spatial Wilson action has
exactly the same physical matrix coefficient as the previously constructed
arbitrary-slice Wilson insertion operator.  This is the operator side of the
Wilson-word/Haar-path comparison. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord_haarAmplitude_eq_operator_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord H N left right)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator
          H N hN beta hbeta left right f) g := by
  calc
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord H N left right)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord H N left right) f) g := by
      symm
      exact
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_inner_eq_haarAmplitude
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord H N left right) f g
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator
          H N hN beta hbeta left right f) g := by
      rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWordPhysicalOperator_eq]

/-- Literal Wilson semantics for the spatial generator word at an arbitrary
transfer slice.  The generic finite-word Haar amplitude is exactly the actual
`left + right` slab product-Haar integral with the intrinsic spatial Wilson
action inserted at slice `left`. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord_haarAmplitude_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord H N left right)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      ∫ path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (left + right),
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) (path 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta (left + right) path *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (path (periodicHypercubicEvenSpecialUnitaryTransferSliceIndex left right)) *
          (g : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            (path (Fin.last (left + right)))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure
          H N (left + right)) := by
  calc
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord H N left right)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator
          H N hN beta hbeta left right f) g :=
      periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord_haarAmplitude_eq_operator_inner
        H N hN beta hbeta left right f g
    _ = _ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator_inner_eq_integral
        H N hN beta hbeta left right f g

/-- The chronological transfer word carrying the actual temporal crossing Wilson
action has the same physical matrix coefficient as the arbitrary-slab crossing
insertion operator. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord_haarAmplitude_eq_operator_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord H N left right)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator
          H N hN beta hbeta left right f) g := by
  calc
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord H N left right)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord H N left right) f) g := by
      symm
      exact
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_inner_eq_haarAmplitude
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord H N left right) f g
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator
          H N hN beta hbeta left right f) g := by
      rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWordPhysicalOperator_eq]

/-- Literal Wilson semantics for the temporal-crossing generator word at an
arbitrary transfer slab.  The generic finite-word Haar amplitude is exactly the
actual `(left + right + 1)`-slab product-Haar integral with the temporal crossing
Wilson action inserted between slices `left` and `left + 1`. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord_haarAmplitude_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord H N left right)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      ∫ path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath
          H N (left + right + 1),
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) (path 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta (left + right + 1) path *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N
            (path (periodicHypercubicEvenSpecialUnitaryTransferSlabIndex left right).castSucc)
            (path (periodicHypercubicEvenSpecialUnitaryTransferSlabIndex left right).succ) *
          (g : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            (path (Fin.last (left + right + 1)))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure
          H N (left + right + 1)) := by
  calc
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord H N left right)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator
          H N hN beta hbeta left right f) g :=
      periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord_haarAmplitude_eq_operator_inner
        H N hN beta hbeta left right f g
    _ = _ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator_inner_eq_integral
        H N hN beta hbeta left right f g

/-- Audit-visible package recording that the two concrete Wilson generator
families in the chronological transfer-word language have their literal actual
finite product-Haar insertion semantics. -/
structure PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonWordHaarPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  spatialWilson :
    ∀ (left right : ℕ)
      (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N),
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord H N left right)
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator
            H N hN beta hbeta left right f) g
  temporalCrossing :
    ∀ (left right : ℕ)
      (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N),
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord H N left right)
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator
            H N hN beta hbeta left right f) g

/-- Construct the concrete Wilson transfer-word Haar-semantics package. -/
theorem periodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonWordHaarPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonWordHaarPackage
      H N hN beta hbeta :=
  { spatialWilson :=
      periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord_haarAmplitude_eq_operator_inner
        H N hN beta hbeta
    temporalCrossing :=
      periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord_haarAmplitude_eq_operator_inner
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D
