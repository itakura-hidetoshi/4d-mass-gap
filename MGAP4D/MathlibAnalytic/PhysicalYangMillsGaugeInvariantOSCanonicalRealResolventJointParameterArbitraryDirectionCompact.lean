import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterArbitraryDirectionCompact
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventFiniteParameterObservableCompact
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

/-- Canonical OS compact-uniform convergence of an arbitrary Banach-valued
observation of a fixed genuine joint Fréchet derivative. -/
theorem VacuumSemigroupGapSlope.canonicalJointArbitraryDirectionResponse_tendsto_uniformOn_compact
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (k m n : ℕ) (H : Fin m → (V →L[ℝ] V))
    (u : Fin n → (Fin (m + 1) → ℝ)) (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < G.mass / 2)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse φ m n
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) H z 0 0 u -
          continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse φ m n
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) H z 0 0 u‖ < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse,
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative] using
    G.canonicalFiniteParameterMixedResponse_tendsto_uniformOn_compact
      T hP hInnerSymmetric hSelf J Q φ k (m + 1) n
      (continuousLinearMapJointSpectralOperatorDirectionFamily m H) u
      K hKcompact hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS compact-uniform convergence of the complete finite
arbitrary-direction joint Fréchet response jet. -/
theorem VacuumSemigroupGapSlope.canonicalJointArbitraryDirectionResponse_tendsto_uniformOn_compact_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (taylorOrder mixedOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V))
    (u : ∀ n : Fin (mixedOrder + 1), Fin n.1 → (Fin (m + 1) → ℝ))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < G.mass / 2)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ k : Fin (taylorOrder + 1), ∀ n : Fin (mixedOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse φ m n.1
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) H z 0 0 (u n) -
          continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse φ m n.1
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) H z 0 0 (u n)‖ < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse,
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative] using
    G.canonicalFiniteParameterMixedResponse_tendsto_uniformOn_compact_rectangular
      T hP hInnerSymmetric hSelf J Q φ (m + 1) taylorOrder mixedOrder
      (continuousLinearMapJointSpectralOperatorDirectionFamily m H) u
      K hKcompact hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS compact-uniform convergence of the basis-independent trace of
a fixed genuine joint Fréchet derivative in arbitrary directions. -/
theorem VacuumSemigroupGapSlope.canonicalJointArbitraryDirectionTrace_tendsto_uniformOn_compact
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k m n : ℕ) (H : Fin m → (V →L[ℝ] V)) (u : Fin n → (Fin (m + 1) → ℝ))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < G.mass / 2)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapJointSpectralOperatorRealResolventSymmetricTraceDerivative V m n
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) lambda)) H z 0 0 u -
          continuousLinearMapJointSpectralOperatorRealResolventSymmetricTraceDerivative V m n
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf) lambda)) H z 0 0 u| < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventSymmetricTraceDerivative,
    Real.norm_eq_abs] using
    G.canonicalJointArbitraryDirectionResponse_tendsto_uniformOn_compact
      T hP hInnerSymmetric hSelf J Q (continuousLinearMapTrace (V := V))
      k m n H u K hKcompact hKupper hupper Z margin hmargin
      hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
