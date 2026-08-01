import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterMultilinearJetSupCompact
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterMultilinearJetOperatorNormCompact
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

/-- Canonical OS compact-uniform convergence of the complete finite
Taylor-order by joint-Fréchet-order carrier jet in one rectangular maximum
norm after arbitrary finite-dimensional compression. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearCarrierRectangularJet_tendsto_uniformOn_compact_sup
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
      ∀ lambda ∈ K, ∀ z ∈ Z,
        continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance
          (continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily
            m taylorOrder mixedOrder H
            (fun k => continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k.1 (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric tau) lambda)) z))
          (continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily
            m taylorOrder mixedOrder H
            (fun k => continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k.1 (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf) lambda)) z)) < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventJointMultilinearCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_sup
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q taylorOrder mixedOrder m H K hKcompact hKupper hupper Z
      margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS compact-uniform convergence of the complete finite
Banach-valued response jet in one rectangular maximum norm. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearResponseCarrierRectangularJet_tendsto_uniformOn_compact_sup
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (taylorOrder mixedOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V))
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
      ∀ lambda ∈ K, ∀ z ∈ Z,
        continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance
          (continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily
            φ m taylorOrder mixedOrder H
            (fun k => continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k.1 (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric tau) lambda)) z))
          (continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily
            φ m taylorOrder mixedOrder H
            (fun k => continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k.1 (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf) lambda)) z)) < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventJointMultilinearResponseCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_sup
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q φ taylorOrder mixedOrder m H K hKcompact hKupper hupper Z
      margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS compact-uniform convergence of the complete finite
basis-independent trace jet in one rectangular maximum norm. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearTraceCarrierRectangularJet_tendsto_uniformOn_compact_sup
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
      ∀ lambda ∈ K, ∀ z ∈ Z,
        continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance
          (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
            V m taylorOrder mixedOrder H
            (fun k => continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k.1 (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric tau) lambda)) z))
          (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
            V m taylorOrder mixedOrder H
            (fun k => continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k.1 (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf) lambda)) z)) < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventJointMultilinearTraceCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_sup
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q taylorOrder mixedOrder m H K hKcompact hKupper hupper Z
      margin hmargin hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
