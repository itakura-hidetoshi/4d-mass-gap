import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterTaylorDysonCompact
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventOperatorDysonCompact
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

/-- Canonical OS compact-uniform convergence of a fixed finite-parameter
Taylor-Dyson coefficient after arbitrary finite-dimensional compression. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolventFiniteParameterTaylorDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V)) (h : Fin parameterDimension → ℝ)
    (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ} (hKu : K ⊆ Set.Iic u)
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
        ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient parameterOrder
            parameterDimension (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) H z 0 h -
          continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient parameterOrder
            parameterDimension (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) H z 0 h‖ < epsilon := by
  simpa [continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient,
    continuousLinearMapFiniteParameterOperatorIncrement] using
    G.canonicalRescaledDefectTaylorIteratedDeriv_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      T hP hInnerSymmetric hSelf J Q k parameterOrder
      (continuousLinearMapFiniteParameterDirectionSynthesis parameterDimension H h)
      K hKcompact hKu hu Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS simultaneous convergence on the finite ambient-Taylor-order
by finite parameter-Taylor-order rectangle. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolventFiniteParameterTaylorDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (taylorOrder parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V)) (h : Fin parameterDimension → ℝ)
    (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ} (hKu : K ⊆ Set.Iic u)
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
      ∀ k : Fin (taylorOrder + 1), ∀ n : Fin (parameterOrder + 1),
      ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient n.1
            parameterDimension (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) H z 0 h -
          continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient n.1
            parameterDimension (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) H z 0 h‖ < epsilon := by
  simpa [continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient,
    continuousLinearMapFiniteParameterOperatorIncrement] using
    G.canonicalRescaledDefectTaylorIteratedDeriv_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
      T hP hInnerSymmetric hSelf J Q taylorOrder parameterOrder
      (continuousLinearMapFiniteParameterDirectionSynthesis parameterDimension H h)
      K hKcompact hKu hu Z margin hmargin hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
