import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventTraceResponseCompact
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
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Canonical compact-uniform Newton-Hermite convergence for a finite family of
continuous-linear spectral responses. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolventNewtonHermiteLinearResponseFamilyPair_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k interpolationDegree : ℕ) {observableOrder : ℕ}
    (Phi : Fin (observableOrder + 1) → ((V →L[ℝ] V) →L[ℝ] ℝ))
    (responseBound : ℝ) (hresponseBound : 0 ≤ responseBound) (hPhi : ∀ r, ‖Phi r‖ ≤ responseBound)
    (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (nodes : κ → Fin (interpolationDegree + 1) → ℝ) (eval : κ → ℝ) (C : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ C, ∀ j, nodes q j ∈ Z) (heval : ∀ q ∈ C, eval q ∈ Z)
    (R : ℝ) (hR : 0 ≤ R) (hdist : ∀ q ∈ C, ∀ j, |eval q - nodes q j| ≤ R)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ lambda ∈ K, ∀ q ∈ C, ‖continuousLinearMapRealResolventLinearResponseFamilyPair Phi (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) (nodes q) (eval q)) - continuousLinearMapRealResolventLinearResponseFamilyPair Phi (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) (nodes q) (eval q))‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventNewtonHermiteLinearResponseFamilyPair_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q k interpolationDegree Phi responseBound hresponseBound hPhi
      K hKcompact hKu hu nodes eval C Z hnodes heval R hR hdist
      margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical compact-uniform convergence of trace interpolants and exact trace
remainders. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolventNewtonHermiteTracePair_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k interpolationDegree : ℕ) (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ}
    (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (nodes : κ → Fin (interpolationDegree + 1) → ℝ) (eval : κ → ℝ) (C : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ C, ∀ j, nodes q j ∈ Z) (heval : ∀ q ∈ C, eval q ∈ Z)
    (R : ℝ) (hR : 0 ≤ R) (hdist : ∀ q ∈ C, ∀ j, |eval q - nodes q j| ≤ R)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ lambda ∈ K, ∀ q ∈ C, ‖continuousLinearMapRealResolventTracePair (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) (nodes q) (eval q)) - continuousLinearMapRealResolventTracePair (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) (nodes q) (eval q))‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventNewtonHermiteTracePair_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q k interpolationDegree K hKcompact hKu hu nodes eval C Z
      hnodes heval R hR hdist margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical simultaneous response-family convergence over the finite Taylor
order by interpolation-degree rectangle. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolventNewtonHermiteLinearResponseFamilyPair_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (taylorOrder interpolationOrder : ℕ) {observableOrder : ℕ}
    (Phi : Fin (observableOrder + 1) → ((V →L[ℝ] V) →L[ℝ] ℝ)) (responseBound : ℝ)
    (hresponseBound : 0 ≤ responseBound) (hPhi : ∀ r, ‖Phi r‖ ≤ responseBound)
    (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (nodes : ∀ d : Fin (interpolationOrder + 1), κ → Fin (d.1 + 1) → ℝ)
    (eval : Fin (interpolationOrder + 1) → κ → ℝ) (C : Set κ) (Z : Set ℝ)
    (hnodes : ∀ d q, q ∈ C → ∀ j, nodes d q j ∈ Z) (heval : ∀ d q, q ∈ C → eval d q ∈ Z)
    (R : ℝ) (hR : 0 ≤ R) (hdist : ∀ d q, q ∈ C → ∀ j, |eval d q - nodes d q j| ≤ R)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ k : Fin (taylorOrder + 1), ∀ d : Fin (interpolationOrder + 1), ∀ lambda ∈ K, ∀ q ∈ C, ‖continuousLinearMapRealResolventLinearResponseFamilyPair Phi (continuousLinearMapRealResolventNewtonHermitePair d.1 (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) (nodes d q) (eval d q)) - continuousLinearMapRealResolventLinearResponseFamilyPair Phi (continuousLinearMapRealResolventNewtonHermitePair d.1 (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) (nodes d q) (eval d q))‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventNewtonHermiteLinearResponseFamilyPair_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q taylorOrder interpolationOrder Phi responseBound hresponseBound hPhi
      K hKcompact hKu hu nodes eval C Z hnodes heval R hR hdist
      margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical simultaneous trace convergence over the finite Taylor-order by
interpolation-degree rectangle. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_realResolventNewtonHermiteTracePair_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (taylorOrder interpolationOrder : ℕ) (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ}
    (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (nodes : ∀ d : Fin (interpolationOrder + 1), κ → Fin (d.1 + 1) → ℝ)
    (eval : Fin (interpolationOrder + 1) → κ → ℝ) (C : Set κ) (Z : Set ℝ)
    (hnodes : ∀ d q, q ∈ C → ∀ j, nodes d q j ∈ Z) (heval : ∀ d q, q ∈ C → eval d q ∈ Z)
    (R : ℝ) (hR : 0 ≤ R) (hdist : ∀ d q, q ∈ C → ∀ j, |eval d q - nodes d q j| ≤ R)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ k : Fin (taylorOrder + 1), ∀ d : Fin (interpolationOrder + 1), ∀ lambda ∈ K, ∀ q ∈ C, ‖continuousLinearMapRealResolventTracePair (continuousLinearMapRealResolventNewtonHermitePair d.1 (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) (nodes d q) (eval d q)) - continuousLinearMapRealResolventTracePair (continuousLinearMapRealResolventNewtonHermitePair d.1 (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) (nodes d q) (eval d q))‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).iteratedDeriv_realResolventNewtonHermiteTracePair_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q taylorOrder interpolationOrder K hKcompact hKu hu
      nodes eval C Z hnodes heval R hR hdist margin hmargin
      hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end MathlibAnalytic
end MGAP4D
