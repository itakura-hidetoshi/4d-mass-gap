import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventFiniteParameterObservableClosedBox
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
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Canonical OS diagonal no-rate convergence of an arbitrary observation of a
fixed finite-parameter mixed Fréchet derivative. -/
theorem VacuumSemigroupGapSlope.canonicalFiniteParameterMixedResponse_tendsto_uniform_closedBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterDimension mixedOrder : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V))
    (u : Fin mixedOrder → (Fin parameterDimension → ℝ))
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
          ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse
              φ parameterDimension mixedOrder
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) p.center p.target (degree tau))) H z u -
            continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse
              φ parameterDimension mixedOrder
              (continuousLinearMapCompression J Q
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf p.target)) H z u‖ < epsilon := by
  exact
    G.canonicalFiniteParameterMixedResponse_tendsto_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q φ parameterDimension mixedOrder H u
      (fun tau => tau) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Canonical OS diagonal no-rate convergence of the complete finite observed
mixed Fréchet jet. -/
theorem VacuumSemigroupGapSlope.canonicalFiniteParameterMixedResponse_tendsto_uniform_closedBox_of_tendsto_degree_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterDimension mixedOrder : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V))
    (u : ∀ n : Fin (mixedOrder + 1),
      Fin n.1 → (Fin parameterDimension → ℝ))
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
          ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse
              φ parameterDimension n.1
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) p.center p.target (degree tau))) H z (u n) -
            continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse
              φ parameterDimension n.1
              (continuousLinearMapCompression J Q
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf p.target)) H z (u n)‖ < epsilon := by
  exact
    G.canonicalFiniteParameterMixedResponse_tendsto_uniform_closedBox_of_joint_rectangular
      T hP hInnerSymmetric hSelf J Q φ parameterDimension mixedOrder H u
      (fun tau => tau) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Canonical OS diagonal no-rate convergence of an arbitrary observation of a
fixed finite-parameter Taylor-Dyson coefficient. -/
theorem VacuumSemigroupGapSlope.canonicalFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V))
    (h : Fin parameterDimension → ℝ)
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
          ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse
              φ parameterOrder parameterDimension
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) p.center p.target (degree tau))) H z 0 h -
            continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse
              φ parameterOrder parameterDimension
              (continuousLinearMapCompression J Q
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf p.target)) H z 0 h‖ < epsilon := by
  exact
    G.canonicalFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q φ parameterOrder parameterDimension H h
      (fun tau => tau) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Canonical OS diagonal no-rate convergence of the complete finite observed
Taylor-Dyson jet. -/
theorem VacuumSemigroupGapSlope.canonicalFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_tendsto_degree_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V))
    (h : Fin parameterDimension → ℝ)
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
        ∀ n : Fin (parameterOrder + 1), ∀ p, box.Contains p → ∀ z ∈ Z,
          ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse
              φ n.1 parameterDimension
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) p.center p.target (degree tau))) H z 0 h -
            continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse
              φ n.1 parameterDimension
              (continuousLinearMapCompression J Q
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf p.target)) H z 0 h‖ < epsilon := by
  exact
    G.canonicalFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_joint_rectangular
      T hP hInnerSymmetric hSelf J Q φ parameterOrder parameterDimension H h
      (fun tau => tau) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Canonical OS diagonal no-rate convergence of the basis-independent trace of
a fixed Taylor-Dyson coefficient. -/
theorem VacuumSemigroupGapSlope.canonicalFiniteParameterTaylorTrace_tendsto_uniform_closedBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V))
    (h : Fin parameterDimension → ℝ)
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
          |continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient
              V parameterOrder parameterDimension
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) p.center p.target (degree tau))) H z 0 h -
            continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient
              V parameterOrder parameterDimension
              (continuousLinearMapCompression J Q
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf p.target)) H z 0 h| < epsilon := by
  exact
    G.canonicalFiniteParameterTaylorTrace_tendsto_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q parameterOrder parameterDimension H h
      (fun tau => tau) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Canonical OS diagonal no-rate convergence of the complete finite
basis-independent trace Taylor-Dyson jet. -/
theorem VacuumSemigroupGapSlope.canonicalFiniteParameterTaylorTrace_tendsto_uniform_closedBox_of_tendsto_degree_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V))
    (h : Fin parameterDimension → ℝ)
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
        ∀ n : Fin (parameterOrder + 1), ∀ p, box.Contains p → ∀ z ∈ Z,
          |continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient
              V n.1 parameterDimension
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) p.center p.target (degree tau))) H z 0 h -
            continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient
              V n.1 parameterDimension
              (continuousLinearMapCompression J Q
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf p.target)) H z 0 h| < epsilon := by
  exact
    G.canonicalFiniteParameterTaylorTrace_tendsto_uniform_closedBox_of_joint_rectangular
      T hP hInnerSymmetric hSelf J Q parameterOrder parameterDimension H h
      (fun tau => tau) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
