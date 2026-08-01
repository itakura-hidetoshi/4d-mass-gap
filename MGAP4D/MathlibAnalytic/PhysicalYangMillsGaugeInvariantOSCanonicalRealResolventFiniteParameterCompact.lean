import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterCompact
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

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Canonical OS compact-uniform convergence of a fixed finite-parameter mixed
resolvent derivative after arbitrary finite-dimensional compression. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolventFiniteParameterSymmetricDerivative_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k parameterDimension mixedOrder : ℕ) (H : Fin parameterDimension → (V →L[ℝ] V))
    (u : Fin mixedOrder → (Fin parameterDimension → ℝ))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < G.mass / 2)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivative parameterDimension mixedOrder
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) H z u -
          continuousLinearMapFiniteParameterRealResolventSymmetricDerivative parameterDimension mixedOrder
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) H z u‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventFiniteParameterSymmetricDerivative_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q k parameterDimension mixedOrder H u K hKcompact
      hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS simultaneous convergence on the finite Taylor-order by
finite-parameter mixed-order rectangle. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolventFiniteParameterSymmetricDerivative_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (parameterDimension taylorOrder mixedOrder : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V))
    (u : ∀ n : Fin (mixedOrder + 1), Fin n.1 → (Fin parameterDimension → ℝ))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < G.mass / 2)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
          (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ k : Fin (taylorOrder + 1), ∀ n : Fin (mixedOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivative parameterDimension n.1
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) H z (u n) -
          continuousLinearMapFiniteParameterRealResolventSymmetricDerivative parameterDimension n.1
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) H z (u n)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventFiniteParameterSymmetricDerivative_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q parameterDimension taylorOrder mixedOrder H u K hKcompact
      hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
