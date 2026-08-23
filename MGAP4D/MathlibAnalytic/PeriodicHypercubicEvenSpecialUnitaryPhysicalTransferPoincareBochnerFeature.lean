import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPoincareDefect

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- The physical one-slab feature-analysis vector on the Gauss-law Hilbert
space is literally the Bochner integral of the gauge-invariant boundary vector
against the canonical Wilson Moore--Aronszajn feature. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator_eq_bochnerIntegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
        H N hN beta hbeta f =
      ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        ((f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) A) •
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
            H N hN beta hbeta).feature A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator_apply]
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator_apply
      H N hN beta hbeta
      (f : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- The normalized physical Poincare defect on the orthogonal complement of
the full transfer top eigenspace is exactly the loss of the squared norm of the
literal Wilson feature Bochner integral. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect_eq_normalizedFeatureBochnerIntegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect
        H N hN beta hbeta f =
      ‖(f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ^ 2 -
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta‖ ^ 2)⁻¹ *
          ‖∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
              (((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
                Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) A) •
                (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
                  H N hN beta hbeta).feature A
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)‖ ^ 2 := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect_eq_normalizedFeatureAnalysis]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator_eq_bochnerIntegral]

/-- The canonical finite-volume transfer gap is a lower Poincare coefficient
for the literal normalized Wilson feature Bochner-integral defect. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap_mul_norm_sq_le_normalizedFeatureBochnerDefect
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta * ‖f‖ ^ 2 ≤
      ‖(f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ^ 2 -
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta‖ ^ 2)⁻¹ *
          ‖∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
              (((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
                Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) A) •
                (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
                  H N hN beta hbeta).feature A
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)‖ ^ 2 := by
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
          H N hN beta hbeta * ‖f‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect
          H N hN beta hbeta f :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap_mul_norm_sq_le_quadraticDefect
        H N hN beta hbeta f
    _ = _ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect_eq_normalizedFeatureBochnerIntegral
        H N hN beta hbeta f

/-- Conversely, any coefficient `δ ≤ 1` that uniformly lower-bounds the
literal normalized Wilson feature Bochner-integral defect is bounded above by
the canonical finite-volume transfer gap.  Thus the next missing model
estimate may be stated directly on this integral expression. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceBochnerPoincareCoefficient_le_transferGap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {δ : ℝ}
    (hδle : δ ≤ 1)
    (hdefect : ∀ f :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta,
      δ * ‖f‖ ^ 2 ≤
        ‖(f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ^ 2 -
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
            H N hN beta hbeta‖ ^ 2)⁻¹ *
            ‖∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
                (((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
                  Lp ℝ 2
                    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) A) •
                  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
                    H N hN beta hbeta).feature A
                ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)‖ ^ 2) :
    δ ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
      H N hN beta hbeta := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspacePoincareCoefficient_le_transferGap
      H N hN beta hbeta hδle
  intro f
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect_eq_normalizedFeatureBochnerIntegral]
  exact hdefect f

end

end MathlibAnalytic
end MGAP4D
