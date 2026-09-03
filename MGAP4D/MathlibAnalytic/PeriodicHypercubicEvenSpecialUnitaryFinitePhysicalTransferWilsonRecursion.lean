import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryFinitePhysicalTransferProjectedTailIntegral
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance finitePhysicalTransferWilsonRecursionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finitePhysicalTransferWilsonRecursionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finitePhysicalTransferWilsonRecursionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finitePhysicalTransferWilsonRecursionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finitePhysicalTransferWilsonRecursionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance finitePhysicalTransferWilsonRecursionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- After exposing the next actual boundary `A₂`, the remaining Wilson factor is
exactly the product over the later `h` slabs. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryWilsonLaterTailRemainder
    (h N : ℕ) (beta : ℝ)
    (laterTail : Fin (h + 1) →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N) : ℝ :=
  ∏ i : Fin h,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      (h + 1) N beta (laterTail i.castSucc) (laterTail i.succ)

/-- The full post-`A₀` Wilson slab product splits into the actual `A₁ → A₂`
slab and the remaining later-tail product. -/
theorem periodicHypercubicEvenSpecialUnitaryWilsonLaterTail_product_factor
    (h N : ℕ) (beta : ℝ)
    (A₁ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N)
    (laterTail : Fin (h + 1) →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N) :
    (∏ x : Fin (h + 1),
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        (h + 1) N beta
        ((Fin.cons A₁ laterTail : Fin ((h + 1) + 1) →
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N) x.castSucc)
        (laterTail x)) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          (h + 1) N beta A₁ (laterTail 0) *
        periodicHypercubicEvenSpecialUnitaryWilsonLaterTailRemainder h N beta laterTail := by
  unfold periodicHypercubicEvenSpecialUnitaryWilsonLaterTailRemainder
  simpa only [Fin.cons_zero, Fin.cons_succ, Fin.succ_castSucc, cast_eq] using
    (Fin.prod_univ_succ
      (fun x : Fin (h + 1) =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          (h + 1) N beta
          ((Fin.cons A₁ laterTail : Fin ((h + 1) + 1) →
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N) x.castSucc)
          (laterTail x)))

/-- Specialization of the integrated projected-tail identity to the actual next
boundary `A₂ = laterTail 0` and the literal remaining Wilson slab product. -/
theorem periodicHypercubicEvenSpecialUnitaryProjectedPhysicalCoefficient_integral_wilsonLaterTail
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N) :
    (∫ laterTail : Fin (h + 1) →
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N,
        periodicHypercubicEvenSpecialUnitaryProjectedKernelRightPhysicalCoefficient
            (h + 1) N hN beta hbeta f (laterTail 0) *
          periodicHypercubicEvenSpecialUnitaryWilsonLaterTailRemainder h N beta laterTail
      ∂(Measure.pi (fun _ : Fin (h + 1) =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N))) =
      ∫ laterTail : Fin (h + 1) →
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N,
        periodicHypercubicEvenSpecialUnitaryRawTwoSlabCoefficient
            (h + 1) N beta f (laterTail 0) *
          periodicHypercubicEvenSpecialUnitaryWilsonLaterTailRemainder h N beta laterTail
      ∂(Measure.pi (fun _ : Fin (h + 1) =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N)) := by
  simpa using
    (periodicHypercubicEvenSpecialUnitaryProjectedKernelRightPhysicalCoefficient_integral_laterTail
      (h + 1) N hN beta hbeta f
      (fun laterTail => laterTail 0)
      (periodicHypercubicEvenSpecialUnitaryWilsonLaterTailRemainder h N beta))

/-- The specialized physical recursion is the literal finite Wilson integrand:
`f(A₀) K(A₀,A₁) K(A₁,A₂)` times all remaining adjacent slab kernels. -/
theorem periodicHypercubicEvenSpecialUnitaryProjectedPhysicalCoefficient_integral_eq_rawWilsonPath
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N) :
    (∫ laterTail : Fin (h + 1) →
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N,
        periodicHypercubicEvenSpecialUnitaryProjectedKernelRightPhysicalCoefficient
            (h + 1) N hN beta hbeta f (laterTail 0) *
          periodicHypercubicEvenSpecialUnitaryWilsonLaterTailRemainder h N beta laterTail
      ∂(Measure.pi (fun _ : Fin (h + 1) =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N))) =
      ∫ laterTail : Fin (h + 1) →
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N,
        ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N,
          ((f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N)) p.1) *
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                (h + 1) N beta p.1 p.2 *
              (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                  (h + 1) N beta p.2 (laterTail 0) *
                periodicHypercubicEvenSpecialUnitaryWilsonLaterTailRemainder h N beta laterTail))
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (h + 1) N)
      ∂(Measure.pi (fun _ : Fin (h + 1) =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N)) := by
  rw [periodicHypercubicEvenSpecialUnitaryProjectedPhysicalCoefficient_integral_wilsonLaterTail]
  apply integral_congr_ae
  filter_upwards with laterTail
  unfold periodicHypercubicEvenSpecialUnitaryRawTwoSlabCoefficient
  rw [← MeasureTheory.integral_mul_const]
  apply integral_congr_ae
  filter_upwards with p
  ring

/-- Equivalently, the same physical recursion equals the complete literal
adjacent-slab product after `A₀`, written with `A₁ = p.2` and the actual later
path `A₂,A₃,…`. -/
theorem periodicHypercubicEvenSpecialUnitaryProjectedPhysicalCoefficient_integral_eq_literalWilsonProduct
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N) :
    (∫ laterTail : Fin (h + 1) →
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N,
        periodicHypercubicEvenSpecialUnitaryProjectedKernelRightPhysicalCoefficient
            (h + 1) N hN beta hbeta f (laterTail 0) *
          periodicHypercubicEvenSpecialUnitaryWilsonLaterTailRemainder h N beta laterTail
      ∂(Measure.pi (fun _ : Fin (h + 1) =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N))) =
      ∫ laterTail : Fin (h + 1) →
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N,
        ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N,
          ((f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N)) p.1) *
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                (h + 1) N beta p.1 p.2 *
              ∏ x : Fin (h + 1),
                periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                  (h + 1) N beta
                  ((Fin.cons p.2 laterTail : Fin ((h + 1) + 1) →
                    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N)
                    x.castSucc)
                  (laterTail x))
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (h + 1) N)
      ∂(Measure.pi (fun _ : Fin (h + 1) =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N)) := by
  rw [periodicHypercubicEvenSpecialUnitaryProjectedPhysicalCoefficient_integral_eq_rawWilsonPath]
  apply integral_congr_ae
  filter_upwards with laterTail
  apply integral_congr_ae
  filter_upwards with p
  rw [periodicHypercubicEvenSpecialUnitaryWilsonLaterTail_product_factor]

end

end MathlibAnalytic
end MGAP4D