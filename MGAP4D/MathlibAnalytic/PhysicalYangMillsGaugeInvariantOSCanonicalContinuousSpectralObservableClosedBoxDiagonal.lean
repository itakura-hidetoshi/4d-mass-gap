import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalContinuousSpectralObservableClosedBoxAlgebraic
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

variable {V W : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

section DiagonalClosedBox

variable (T : P.StronglyContinuousPhysicalSemigroup)
variable (G : T.VacuumSemigroupGapSlope)
variable (hP : P.IsNormalized)
variable (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
variable (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
variable (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
variable (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
variable (degree : G.AdmissibleRescaledDefectTime → ℕ)
variable (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
variable (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))

include hdegree

/-- Diagonal canonical OS form for every continuous observable: the Taylor
degree may depend arbitrarily on admissible time with no speed relation. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_tendsto_degree
    (Phi : (V →L[ℝ] V) → W) (hPhi : Continuous Phi) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ p, box.Contains p →
          ‖Phi (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) p.center p.target (degree tau))) -
            Phi (continuousLinearMapCompression J Q
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf p.target))‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q Phi hPhi degree hdegree box

/-- Diagonal determinant convergence on the complete closed half-mass box. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_det_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_tendsto_degree :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ p, box.Contains p →
          |(continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) p.center p.target (degree tau))).det -
            (continuousLinearMapCompression J Q
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf p.target)).det| < epsilon := by
  simpa [Real.norm_eq_abs] using
    G.admissibleRescaledDefectTaylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_tendsto_degree
      T hP hInnerSymmetric hSelf J Q degree hdegree box
      (fun A : V →L[ℝ] V => A.det) ContinuousLinearMap.continuous_det

/-- Diagonal finite operator-polynomial convergence on the complete box. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_polynomial_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_tendsto_degree
    (coeff : ℕ → ℝ) (polynomialDegree : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ p, box.Contains p →
          ‖continuousLinearMapPolynomial coeff polynomialDegree
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) p.center p.target (degree tau))) -
            continuousLinearMapPolynomial coeff polynomialDegree
              (continuousLinearMapCompression J Q
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf p.target))‖ < epsilon := by
  exact
    G.admissibleRescaledDefectTaylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_tendsto_degree
      T hP hInnerSymmetric hSelf J Q degree hdegree box
      (continuousLinearMapPolynomial coeff polynomialDegree)
      (continuous_continuousLinearMapPolynomial coeff polynomialDegree)

/-- Diagonal finite spectral-moment-vector convergence on the complete box. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_spectralMomentJet_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_tendsto_degree
    (momentOrder : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ p, box.Contains p →
          ‖continuousLinearMapSpectralMomentJet momentOrder
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) p.center p.target (degree tau))) -
            continuousLinearMapSpectralMomentJet momentOrder
              (continuousLinearMapCompression J Q
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf p.target))‖ < epsilon := by
  exact
    G.admissibleRescaledDefectTaylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_tendsto_degree
      T hP hInnerSymmetric hSelf J Q degree hdegree box
      (continuousLinearMapSpectralMomentJet momentOrder)
      (continuous_continuousLinearMapSpectralMomentJet momentOrder)

end DiagonalClosedBox

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
