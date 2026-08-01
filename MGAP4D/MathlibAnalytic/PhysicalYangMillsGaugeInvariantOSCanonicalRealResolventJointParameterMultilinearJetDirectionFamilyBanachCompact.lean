import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterMultilinearJetDirectionFamilyBanachCompact
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterMultilinearJetDirectionFamilyCompactTrace
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic
namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Canonical OS compact-uniform complete carrier-rectangle convergence in the
actual finite dependent-product norm when the perturbation family moves. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearCarrierRectangularJet_tendsto_uniformOn_compact_directionFamily_norm
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (taylorOrder mixedOrder m : ℕ)
    (H : G.AdmissibleRescaledDefectTime → Fin m → (V →L[ℝ] V))
    (H0 : Fin m → (V →L[ℝ] V))
    (hH : Tendsto H G.admissibleRescaledDefectTimeFilter (𝓝 H0))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < G.mass / 2)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
          (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
          (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily
          m taylorOrder mixedOrder (H tau)
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily J Q taylorOrder
            (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily
          m taylorOrder mixedOrder H0
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily J Q taylorOrder
            (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda z)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventJointMultilinearCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_directionFamily_norm
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q taylorOrder mixedOrder m H H0 hH K hKcompact hKupper hupper
      Z margin hmargin hlimitMargin M hM hlimitNorm

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Canonical OS compact-uniform complete response-rectangle convergence in the
actual finite dependent-product norm when the perturbation family moves. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearResponseCarrierRectangularJet_tendsto_uniformOn_compact_directionFamily_norm
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (taylorOrder mixedOrder m : ℕ)
    (H : G.AdmissibleRescaledDefectTime → Fin m → (V →L[ℝ] V))
    (H0 : Fin m → (V →L[ℝ] V))
    (hH : Tendsto H G.admissibleRescaledDefectTimeFilter (𝓝 H0))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < G.mass / 2)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
          (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
          (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily
          φ m taylorOrder mixedOrder (H tau)
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily J Q taylorOrder
            (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily
          φ m taylorOrder mixedOrder H0
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily J Q taylorOrder
            (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda z)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventJointMultilinearResponseCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_directionFamily_norm
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q φ taylorOrder mixedOrder m H H0 hH K hKcompact hKupper hupper
      Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS compact-uniform complete trace-rectangle convergence in the
actual finite dependent-product norm when the perturbation family moves. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearTraceCarrierRectangularJet_tendsto_uniformOn_compact_directionFamily_norm
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (taylorOrder mixedOrder m : ℕ)
    (H : G.AdmissibleRescaledDefectTime → Fin m → (V →L[ℝ] V))
    (H0 : Fin m → (V →L[ℝ] V))
    (hH : Tendsto H G.admissibleRescaledDefectTimeFilter (𝓝 H0))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < G.mass / 2)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
          (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
          (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
          V m taylorOrder mixedOrder (H tau)
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily J Q taylorOrder
            (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
          V m taylorOrder mixedOrder H0
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily J Q taylorOrder
            (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda z)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventJointMultilinearTraceCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_directionFamily_norm
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q taylorOrder mixedOrder m H H0 hH K hKcompact hKupper hupper
      Z margin hmargin hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end MathlibAnalytic
end MGAP4D
