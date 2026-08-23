import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2TransferPositive
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtGramFactorizationOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

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

local instance periodicHypercubicEvenSpecialUnitarySpatialSliceHaarFactorization_sFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The actual one-slab Moore--Aronszajn analysis map before continuity is
bundled.  It sends a complete Haar-`L²` boundary vector to the Bochner
integral of that vector against the canonical continuous kernel feature. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisLinearMap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →ₗ[ℝ]
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let C :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
      H N hN beta hbeta
  refine
    { toFun := fun f => ∫ A, f A • C.feature A ∂μ
      map_add' := ?_
      map_smul' := ?_ }
  · intro f g
    have hf : Integrable (fun A => f A • C.feature A) μ := by
      simpa [μ, C] using
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_weighted_integrable
          H N hN beta hbeta f
    have hg : Integrable (fun A => g A • C.feature A) μ := by
      simpa [μ, C] using
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_weighted_integrable
          H N hN beta hbeta g
    rw [← integral_add hf hg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with A hA
    rw [hA]
    exact add_smul (f A) (g A) (C.feature A)
  · intro c f
    calc
      (∫ A, (c • f) A • C.feature A ∂μ) =
          ∫ A, c • (f A • C.feature A) ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with A hA
        rw [hA]
        simp [smul_smul]
      _ = c • ∫ A, f A • C.feature A ∂μ := by
        simpa using integral_smul c (fun A => f A • C.feature A)

/-- The unbundled analysis map evaluates to the literal Bochner feature
integral. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisLinearMap_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisLinearMap
        H N hN beta hbeta f =
      ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        f A •
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
            H N hN beta hbeta).feature A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  rfl

/-- The raw one-slab feature analysis map is bounded.  The deliberately simple
constant `‖K‖ + 1` avoids introducing square roots: the exact quadratic-form
identity and Hilbert--Schmidt Cauchy--Schwarz estimate suffice. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisLinearMap_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisLinearMap
        H N hN beta hbeta f‖ ≤
      (‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta‖ + 1) * ‖f‖ := by
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
    H N hN beta hbeta
  let A := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisLinearMap
    H N hN beta hbeta
  have hquad :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_self_eq_norm_integral_sq
      H N hN beta hbeta f
  have hsq : ‖A f‖ ^ 2 = realL2HilbertSchmidtKernelPairing K f f := by
    simpa [A, K] using hquad.symm
  have hnonneg : 0 ≤ realL2HilbertSchmidtKernelPairing K f f := by
    exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_nonnegative
        H N hN beta hbeta f
  have hpair := realL2HilbertSchmidtKernelPairing_norm_le K f f
  have habs :
      ‖realL2HilbertSchmidtKernelPairing K f f‖ =
        realL2HilbertSchmidtKernelPairing K f f := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [habs, ← hsq] at hpair
  have hx : 0 ≤ ‖A f‖ := norm_nonneg _
  have hy : 0 ≤ ‖f‖ := norm_nonneg _
  have hk : 0 ≤ ‖K‖ := norm_nonneg _
  have hC : 0 ≤ (‖K‖ + 1) * ‖f‖ :=
    mul_nonneg (by linarith) hy
  have hkC : ‖K‖ ≤ (‖K‖ + 1) ^ 2 := by
    nlinarith [sq_nonneg ‖K‖]
  have hsq' : ‖A f‖ ^ 2 ≤ ((‖K‖ + 1) * ‖f‖) ^ 2 := by
    calc
      ‖A f‖ ^ 2 ≤ ‖K‖ * ‖f‖ * ‖f‖ := hpair
      _ ≤ (‖K‖ + 1) ^ 2 * ‖f‖ ^ 2 := by
        nlinarith [sq_nonneg ‖f‖]
      _ = ((‖K‖ + 1) * ‖f‖) ^ 2 := by ring
  have hfinal : ‖A f‖ ≤ (‖K‖ + 1) * ‖f‖ := by
    nlinarith
  simpa [A, K] using hfinal

/-- Actual bounded one-slab feature analysis operator

`A : L²(spatial-slice Haar) → Φ.FeatureHilbert`.

No auxiliary measurable-feature hypothesis is introduced: continuity and
Bochner integrability were proved for the canonical Moore--Aronszajn feature
in the preceding positivity layer. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →L[ℝ]
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisLinearMap
    H N hN beta hbeta).mkContinuous
      (‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta‖ + 1)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisLinearMap_norm_le
        H N hN beta hbeta)

/-- The bounded feature analysis operator evaluates to the literal Bochner
integral. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
        H N hN beta hbeta f =
      ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        f A •
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
            H N hN beta hbeta).feature A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  rfl

/-- Exact Gram factorization of the complete one-slab Haar-`L²` kernel pairing
through the canonical bounded Moore--Aronszajn feature analysis operator. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_gramFactorization
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealL2HilbertSchmidtKernelPairingGramFactorization
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
        H N hN beta hbeta) := by
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
    H N hN beta hbeta
  let C := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
    H N hN beta hbeta
  let A := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
    H N hN beta hbeta
  apply realL2HilbertSchmidtKernelPairing_gramFactorization_of_symmetric_of_quadratic
    K C.FeatureHilbert A
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_symmetric
      H N hN beta hbeta)
  intro f
  calc
    realL2HilbertSchmidtKernelPairing K f f =
        ‖∫ x : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            f x • C.feature x
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)‖ ^ 2 := by
      simpa [K, C] using
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_self_eq_norm_integral_sq
          H N hN beta hbeta f
    _ = ‖A f‖ ^ 2 := by
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator_apply]
    _ = inner ℝ (A f) (A f) :=
      (real_inner_self_eq_norm_sq (A f)).symm

/-- The genuine one-slab compact `SU(N)` Haar-`L²` transfer is exactly the
adjoint square of its canonical Moore--Aronszajn feature analysis operator:

`T = A† A`.

This is an operator equality on the complete spatial-slice Haar Hilbert space,
not merely equality of pointwise kernels or quadratic forms. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_eq_adjoint_comp_analysis
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
          H N hN beta hbeta)†.comp
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
          H N hN beta hbeta) := by
  change
    realL2HilbertSchmidtKernelOperator
        (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta) =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
          H N hN beta hbeta)†.comp
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
          H N hN beta hbeta)
  exact
    realL2HilbertSchmidtKernelOperator_eq_adjoint_comp_of_gramFactorization
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_gramFactorization
        H N hN beta hbeta)

/-- Exact `C*` norm identity inherited from the `A† A` realization. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_norm_eq_analysis_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta‖ =
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
          H N hN beta hbeta‖ ^ 2 := by
  change
    ‖realL2HilbertSchmidtKernelOperator
        (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta)‖ =
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
          H N hN beta hbeta‖ ^ 2
  exact
    realL2HilbertSchmidtKernelOperator_norm_eq_analysis_sq_of_gramFactorization
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_gramFactorization
        H N hN beta hbeta)

/-- Audit-visible exact factorization receipt for the actual one-slab transfer. -/
structure PeriodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferFactorizationPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  gramFactorization :
    RealL2HilbertSchmidtKernelPairingGramFactorization
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
        H N hN beta hbeta)
  operatorEq :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
          H N hN beta hbeta)†.comp
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
          H N hN beta hbeta)
  operatorNormEq :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta‖ =
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
          H N hN beta hbeta‖ ^ 2

/-- Construct the exact one-slab Haar-`L²` factorization package. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferFactorizationPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferFactorizationPackage
      H N hN beta hbeta :=
  { gramFactorization :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_gramFactorization
        H N hN beta hbeta
    operatorEq :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_eq_adjoint_comp_analysis
        H N hN beta hbeta
    operatorNormEq :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_norm_eq_analysis_sq
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D