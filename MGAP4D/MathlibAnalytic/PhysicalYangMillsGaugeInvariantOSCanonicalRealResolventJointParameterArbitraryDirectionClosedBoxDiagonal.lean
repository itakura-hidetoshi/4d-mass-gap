import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterArbitraryDirectionClosedBox
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventFiniteParameterObservableClosedBoxDiagonal
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

/-- Canonical OS diagonal no-rate convergence of an arbitrary Banach-valued
observation of a fixed genuine joint Fréchet derivative. -/
theorem VacuumSemigroupGapSlope.canonicalJointArbitraryDirectionResponse_tendsto_uniform_closedBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (u : Fin n → (Fin (m + 1) → ℝ))
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
            φ m n (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau)
                p.center p.target (degree tau))) H z 0 0 u -
          continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
            φ m n (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf p.target)) H z 0 0 u‖ < epsilon := by
  exact
    G.canonicalJointArbitraryDirectionResponse_tendsto_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q φ m n H u (fun tau => tau) degree
      tendsto_id hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS diagonal no-rate convergence of the complete finite
arbitrary-direction joint Fréchet response jet. -/
theorem VacuumSemigroupGapSlope.canonicalJointArbitraryDirectionResponse_tendsto_uniform_closedBox_of_tendsto_degree_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (mixedOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V))
    (u : ∀ n : Fin (mixedOrder + 1), Fin n.1 → (Fin (m + 1) → ℝ))
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ n : Fin (mixedOrder + 1), ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
            φ m n.1 (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau)
                p.center p.target (degree tau))) H z 0 0 (u n) -
          continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
            φ m n.1 (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf p.target)) H z 0 0 (u n)‖ < epsilon := by
  exact
    G.canonicalJointArbitraryDirectionResponse_tendsto_uniform_closedBox_of_joint_rectangular
      T hP hInnerSymmetric hSelf J Q φ mixedOrder m H u
      (fun tau => tau) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Canonical OS diagonal no-rate convergence of the basis-independent trace
of a fixed genuine joint Fréchet derivative in arbitrary directions. -/
theorem VacuumSemigroupGapSlope.canonicalJointArbitraryDirectionTrace_tendsto_uniform_closedBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V) (m n : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (u : Fin n → (Fin (m + 1) → ℝ))
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        |continuousLinearMapJointSpectralOperatorRealResolventSymmetricTraceDerivative
            V m n (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau)
                p.center p.target (degree tau))) H z 0 0 u -
          continuousLinearMapJointSpectralOperatorRealResolventSymmetricTraceDerivative
            V m n (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf p.target)) H z 0 0 u| < epsilon := by
  exact
    G.canonicalJointArbitraryDirectionTrace_tendsto_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q m n H u (fun tau => tau) degree
      tendsto_id hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
