import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterMultilinearJetOperatorNormCompact
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventStabilityCompact
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

variable {V W : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Canonical OS compact-uniform operator-norm convergence of the complete
joint spectral/operator Fréchet multilinear carrier after arbitrary finite-
dimensional compression. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearCarrier_tendsto_uniformOn_compact
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k m n : ℕ) (H : Fin m → (V →L[ℝ] V)) (K : Set ℝ) (hKcompact : IsCompact K)
    {upper : ℝ} (hKupper : K ⊆ Set.Iic upper) (hupper : upper < G.mass / 2)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent
          T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent m n H
            (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric tau) lambda)) z) -
          continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent m n H
            (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf) lambda)) z)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventJointMultilinearCarrier_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q k m n H K hKcompact hKupper hupper Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Canonical OS simultaneous compact-uniform convergence of the complete
finite full-carrier jet. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearCarrier_tendsto_uniformOn_compact_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (taylorOrder mixedOrder m : ℕ) (H : Fin m → (V →L[ℝ] V))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < G.mass / 2)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1 (G.vacuumOrthogonalContinuumTaylorResolvent
          T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1 (G.vacuumOrthogonalContinuumTaylorResolvent
          T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ k : Fin (taylorOrder + 1), ∀ n : Fin (mixedOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent m n.1 H
            (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k.1 (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric tau) lambda)) z) -
          continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent m n.1 H
            (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k.1 (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf) lambda)) z)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventJointMultilinearCarrier_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q taylorOrder mixedOrder m H K hKcompact hKupper hupper Z
      margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS compact-uniform convergence of a complete Banach-valued
observation of the full joint Fréchet carrier. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearResponseCarrier_tendsto_uniformOn_compact
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (k m n : ℕ) (H : Fin m → (V →L[ℝ] V))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < G.mass / 2)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent
          T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
            φ m n H (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric tau) lambda)) z) -
          continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
            φ m n H (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf) lambda)) z)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventJointMultilinearResponseCarrier_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q φ k m n H K hKcompact hKupper hupper Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Canonical OS compact-uniform convergence of the complete basis-independent
trace carrier. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearTraceCarrier_tendsto_uniformOn_compact
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k m n : ℕ) (H : Fin m → (V →L[ℝ] V)) (K : Set ℝ) (hKcompact : IsCompact K)
    {upper : ℝ} (hKupper : K ⊆ Set.Iic upper) (hupper : upper < G.mass / 2)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent
          T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
            V m n H (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric tau) lambda)) z) -
          continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
            V m n H (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf) lambda)) z)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventJointMultilinearTraceCarrier_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q k m n H K hKcompact hKupper hupper Z margin hmargin
      hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
