import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryFinitePhysicalTransferProjectedTail
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance oneSlabTransferHaarApplicationTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance oneSlabTransferHaarApplicationCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance oneSlabTransferHaarApplicationSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance oneSlabTransferHaarApplicationMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance oneSlabTransferHaarApplicationBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance oneSlabTransferHaarApplicationSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Literal right-boundary Haar integral obtained by applying the one-slab
Wilson kernel to an ambient spatial-slice Haar `L²` vector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralFunction
    (H N : ℕ) (beta : ℝ)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ∫ A,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B * f A
  ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

/-- The literal one-slab Haar integral is an `L²` function of the right
boundary.  The Wilson bound `|K| ≤ 1` reduces the estimate to the `L¹` norm of
the input, which is finite because normalized Haar is a probability measure. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralFunction_memLp_two
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralFunction
        H N beta f)
      2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hfInt : Integrable (fun A => f A) μ := by
    exact
      ((Lp.memLp f).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2) |>
        (memLp_one_iff_integrable.mp))
  have hpairMeas : AEStronglyMeasurable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 * f p.1)
      (μ.prod μ) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H N beta).measurable.aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f).comp_fst
  have hmeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralFunction
        H N beta f) μ := by
    simpa [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralFunction, μ]
      using hpairMeas.integral_prod_left'
  let C : ℝ := ∫ A, ‖f A‖ ∂μ
  refine MemLp.of_bound hmeas C ?_
  exact Filter.Eventually.of_forall fun B => by
    have hsectionMeas : AEStronglyMeasurable
        (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B * f A)
        μ := by
      exact
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
          H N beta B).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
    have hsectionInt : Integrable
        (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B * f A)
        μ := by
      apply hfInt.mono' hsectionMeas
      filter_upwards with A
      rw [norm_mul]
      have hk :
          ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B‖ ≤ 1 := by
        simpa [Real.norm_eq_abs] using
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
            H N hN beta hbeta A B
      simpa using mul_le_mul_of_nonneg_right hk (norm_nonneg (f A))
    change
      ‖∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B * f A
        ∂μ‖ ≤ C
    calc
      ‖∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B * f A
        ∂μ‖ ≤
          ∫ A,
            ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B * f A‖
          ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ A, ‖f A‖ ∂μ := by
        apply integral_mono_ae hsectionInt.norm hfInt.norm
        filter_upwards with A
        rw [norm_mul]
        have hk :
            ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B‖ ≤ 1 := by
          simpa [Real.norm_eq_abs] using
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
              H N hN beta hbeta A B
        simpa using mul_le_mul_of_nonneg_right hk (norm_nonneg (f A))
      _ = C := rfl

/-- Canonical ambient Haar-`L²` vector represented by the literal one-slab
kernel integral. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralFunction_memLp_two
    H N hN beta hbeta f).toLp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralFunction
        H N beta f)

/-- The packaged `L²` vector has the literal Haar-kernel integral as its
representative almost everywhere. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2_coeFn
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    (fun B =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2
        H N hN beta hbeta f B) =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralFunction
        H N beta f :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralFunction_memLp_two
    H N hN beta hbeta f).coeFn_toLp

/-- The Fréchet--Riesz one-slab transfer is exactly the `L²` vector represented
by the literal Haar kernel application.  This is the application-level bridge
needed to iterate the Wilson kernel as an actual transfer-operator power. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_apply_eq_integralL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta f =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2
        H N hN beta hbeta f := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  apply ext_inner_right ℝ
  intro g
  calc
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g =
      ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2 * (f p.1 * g p.2)
      ∂(μ.prod μ) := by
        simpa [μ, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner_eq_rawIntegral
            H N hN beta hbeta f g
    _ = ∫ B,
        (∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B * f A
        ∂μ) * g B
      ∂μ := by
        have hrawInt : Integrable
            (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                  H N beta p.1 p.2 * (f p.1 * g p.2))
            (μ.prod μ) := by
          exact
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_memLp_two
              H N hN beta hbeta).integrable_mul
              (realL2ExternalTensorFunction_memLp_two f g)
        rw [integral_prod_symm _ hrawInt]
        apply integral_congr_ae
        filter_upwards with B
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards with A
        ring
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2
          H N hN beta hbeta f) g := by
        rw [MeasureTheory.L2.inner_def]
        apply integral_congr_ae
        filter_upwards [
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2_coeFn
            H N hN beta hbeta f] with B hB
        rw [hB, periodicHypercubicEven_real_inner_eq_mul]
        rfl

/-- Physical packaging of the literal one-slab Haar-kernel application. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferIntegralVector
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  ⟨periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2
      H N hN beta hbeta
      (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)),
    by
      rw [← periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_apply_eq_integralL2]
      exact
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_preserves_GaussLaw
          H N hN beta hbeta f.property⟩

/-- The actual physical one-slab transfer is represented by the same literal
Haar-kernel application inside the closed Gauss-law subspace. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_apply_eq_integralVector
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferIntegralVector
        H N hN beta hbeta f := by
  apply Subtype.ext
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta
        (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralL2
        H N hN beta hbeta
        (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_apply_eq_integralL2
      H N hN beta hbeta
      (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

end

end MathlibAnalytic
end MGAP4D
