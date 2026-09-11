import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventOperatorMixedDysonCompact
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventStabilityCompact
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Canonical OS compact-uniform convergence of a fixed mixed-direction Dyson
polarization coefficient after arbitrary finite-dimensional compression. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolventOperatorMixedDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k mixedOrder : ℕ) (H : Fin mixedOrder → (V →L[ℝ] V)) (K : Set ℝ)
    (hKcompact : IsCompact K) {u : ℝ} (hKu : K ⊆ Set.Iic u)
    (hu : u < G.mass / 2) (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapRealResolventOperatorMixedDysonCoefficient mixedOrder
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) H z -
          continuousLinearMapRealResolventOperatorMixedDysonCoefficient mixedOrder
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) H z‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventOperatorMixedDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q k mixedOrder H K hKcompact hKu hu Z
      margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS simultaneous convergence on the finite Taylor-order by finite
mixed-direction polarization-order rectangle. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolventOperatorMixedDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (taylorOrder mixedOrder : ℕ)
    (H : ∀ n : Fin (mixedOrder + 1), Fin n.1 → (V →L[ℝ] V)) (K : Set ℝ)
    (hKcompact : IsCompact K) {u : ℝ} (hKu : K ⊆ Set.Iic u)
    (hu : u < G.mass / 2) (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
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
        ‖continuousLinearMapRealResolventOperatorMixedDysonCoefficient n.1
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) (H n) z -
          continuousLinearMapRealResolventOperatorMixedDysonCoefficient n.1
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) (H n) z‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventOperatorMixedDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q taylorOrder mixedOrder H K hKcompact hKu hu Z
      margin hmargin hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
