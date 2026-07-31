import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventNewtonHermiteCompactRectangular
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

variable {κ V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Canonical OS compact-uniform convergence of Newton-Hermite interpolants
and their exact remainders after arbitrary finite-dimensional compression. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolventNewtonHermitePair_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k interpolationDegree : ℕ) (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ}
    (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (nodes : κ → Fin (interpolationDegree + 1) → ℝ) (eval : κ → ℝ)
    (C : Set κ) (Z : Set ℝ) (hnodes : ∀ q ∈ C, ∀ j, nodes q j ∈ Z)
    (heval : ∀ q ∈ C, eval q ∈ Z) (R : ℝ) (hR : 0 ≤ R)
    (hdist : ∀ q ∈ C, ∀ j, |eval q - nodes q j| ≤ R)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
          (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k
          (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ lambda ∈ K, ∀ q ∈ C,
        ‖continuousLinearMapRealResolventNewtonHermitePair interpolationDegree
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda))
            (nodes q) (eval q) -
          continuousLinearMapRealResolventNewtonHermitePair interpolationDegree
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda))
            (nodes q) (eval q)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).
      iteratedDeriv_realResolventNewtonHermitePair_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
        rfl rfl J Q k interpolationDegree K hKcompact hKu hu nodes eval C Z
        hnodes heval R hR hdist margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS simultaneous convergence on the finite Taylor-order by
finite Newton-Hermite interpolation-degree rectangle. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolventNewtonHermitePair_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (taylorOrder interpolationOrder : ℕ) (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ}
    (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (nodes : ∀ d : Fin (interpolationOrder + 1), κ → Fin (d.1 + 1) → ℝ)
    (eval : Fin (interpolationOrder + 1) → κ → ℝ) (C : Set κ) (Z : Set ℝ)
    (hnodes : ∀ d q, q ∈ C → ∀ j, nodes d q j ∈ Z)
    (heval : ∀ d q, q ∈ C → eval d q ∈ Z) (R : ℝ) (hR : 0 ≤ R)
    (hdist : ∀ d q, q ∈ C → ∀ j, |eval d q - nodes d q j| ≤ R)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
          (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1
          (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ k : Fin (taylorOrder + 1), ∀ d : Fin (interpolationOrder + 1),
      ∀ lambda ∈ K, ∀ q ∈ C,
        ‖continuousLinearMapRealResolventNewtonHermitePair d.1
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda))
            (nodes d q) (eval d q) -
          continuousLinearMapRealResolventNewtonHermitePair d.1
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda))
            (nodes d q) (eval d q)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).
      iteratedDeriv_realResolventNewtonHermitePair_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
        rfl rfl J Q taylorOrder interpolationOrder K hKcompact hKu hu
        nodes eval C Z hnodes heval R hR hdist margin hmargin
        hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
