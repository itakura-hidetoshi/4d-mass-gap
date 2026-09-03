import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2Transfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance oneSlabPairHaarL2TransferTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance oneSlabPairHaarL2TransferCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance oneSlabPairHaarL2TransferSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance oneSlabPairHaarL2TransferMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance oneSlabPairHaarL2TransferBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance oneSlabPairHaarL2TransferSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance oneSlabPairHaarL2TransferPairHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- Literal two-endpoint one-step Wilson kernel on ordered spatial-slice pairs.

For an initial endpoint pair `(A,B)` and a translated endpoint pair `(A',B')`,
this is exactly

`K₂((A,B),(A',B')) = K(A,A') * K(B,B')`.

No tensor-density or completion statement is used in this definition. -/
def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
    (H N : ℕ)
    (beta : ℝ)
    (p :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta p.1.1 p.2.1 *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta p.1.2 p.2.2

/-- The literal pair one-step kernel is jointly continuous on the four spatial
boundary variables. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_continuous
    (H N : ℕ)
    (beta : ℝ) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
        H N beta) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
  have hK :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta
  have h₁ : Continuous
      (fun p :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1.1 p.2.1) :=
    hK.comp₂
      (continuous_fst.comp continuous_fst)
      (continuous_fst.comp continuous_snd)
  have h₂ : Continuous
      (fun p :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1.2 p.2.2) :=
    hK.comp₂
      (continuous_snd.comp continuous_fst)
      (continuous_snd.comp continuous_snd)
  exact h₁.mul h₂

/-- At nonnegative coupling the pair one-step kernel has absolute value at most
one. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_abs_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (p :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)) :
    |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
        H N beta p| ≤ 1 := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel, abs_mul]
  have h₁ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H N hN beta hbeta p.1.1 p.2.1
  have h₂ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H N hN beta hbeta p.1.2 p.2.2
  calc
    |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1.1 p.2.1| *
        |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1.2 p.2.2| ≤ 1 * 1 := by
      exact mul_le_mul h₁ h₂ (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- The continuous literal pair kernel is almost-everywhere strongly measurable
for the actual pair-Haar product measure.  Keeping the measure explicit avoids
materializing a global four-fold-product `Measurable` theorem. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_aestronglyMeasurable
    (H N : ℕ)
    (beta : ℝ) :
    AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N beta)
      ((periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_continuous
      H N beta).aestronglyMeasurable

/-- The literal pair one-step Wilson kernel belongs to
`L²(pair-Haar × pair-Haar)` directly from finite Haar mass and the uniform
pointwise bound. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_memLp_two
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
        H N beta)
      2
      ((periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  letI : IsFiniteMeasure (μ.prod μ) := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  exact MemLp.of_bound
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_aestronglyMeasurable
      H N beta)
    1
    (Filter.Eventually.of_forall fun p => by
      simpa [Real.norm_eq_abs] using
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_abs_le_one
          H N hN beta hbeta p)

/-- The squared literal pair kernel is integrable on pair-Haar × pair-Haar.
This is now a consequence of the direct finite-measure `L²` theorem rather than
a separate four-fold measurability proof. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_norm_sq_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Integrable
      (fun p :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
          H N beta p‖ ^ 2)
      ((periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :=
  (memLp_two_iff_integrable_sq_norm
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_aestronglyMeasurable
      H N beta)).1
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_memLp_two
      H N hN beta hbeta)

/-- Canonical pair-Haar product-`L²` vector of the literal two-endpoint
one-step Wilson kernel. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2
      ((periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_memLp_two
    H N hN beta hbeta).toLp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N beta)

/-- The pair-kernel `L²` vector has the literal product Wilson kernel as its
a.e. representative. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (fun p =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
        H N hN beta hbeta p) =ᵐ[
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)]
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N beta :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_memLp_two
    H N hN beta hbeta).coeFn_toLp

/-- Bounded ambient one-step operator on ordered endpoint-pair Haar `L²`,
constructed from the literal product kernel by the existing Hilbert--Schmidt
Fréchet--Riesz operator. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) :=
  realL2HilbertSchmidtKernelOperator
    (μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
      H N hN beta hbeta)

/-- Exact arbitrary pair-Haar matrix coefficient of the ambient two-endpoint
one-step operator. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta f) g =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
          H N hN beta hbeta) f g := by
  exact realL2HilbertSchmidtKernelOperator_inner
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
      H N hN beta hbeta) f g

/-- Hilbert--Schmidt norm control of the ambient pair one-step operator. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
        H N hN beta hbeta‖ := by
  exact realL2HilbertSchmidtKernelOperator_norm_le
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
      H N hN beta hbeta)

end

end MathlibAnalytic
end MGAP4D