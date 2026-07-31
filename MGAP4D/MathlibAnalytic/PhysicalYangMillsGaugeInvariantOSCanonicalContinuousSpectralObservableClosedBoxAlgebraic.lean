import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalContinuousSpectralObservableClosedBox
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

section JointClosedBoxAlgebraic

variable (T : P.StronglyContinuousPhysicalSemigroup)
variable (G : T.VacuumSemigroupGapSlope)
variable (hP : P.IsNormalized)
variable (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
variable (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
variable (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
variable (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
variable {β : Type*} {m : Filter β}
variable (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
variable (htau : Tendsto tau m G.admissibleRescaledDefectTimeFilter)
variable (hdegree : Tendsto degree m atTop)
variable (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))

/-- Canonical OS finite operator polynomials converge uniformly on every full
closed half-mass Taylor box. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_polynomial_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_joint
    (coeff : ℕ → ℝ) (polynomialDegree : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p →
      ‖continuousLinearMapPolynomial coeff polynomialDegree
          (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric (tau b)) p.center p.target (degree b))) -
        continuousLinearMapPolynomial coeff polynomialDegree
          (continuousLinearMapCompression J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf p.target))‖ < epsilon := by
  exact
    G.canonicalRescaledDefectTaylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q
      (continuousLinearMapPolynomial coeff polynomialDegree)
      (continuous_continuousLinearMapPolynomial coeff polynomialDegree)
      tau degree htau hdegree box

/-- Canonical OS polynomial traces converge uniformly on every full closed
half-mass Taylor box. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_polynomialTrace_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_joint
    (coeff : ℕ → ℝ) (polynomialDegree : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p →
      |continuousLinearMapPolynomialTrace coeff polynomialDegree
          (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric (tau b)) p.center p.target (degree b))) -
        continuousLinearMapPolynomialTrace coeff polynomialDegree
          (continuousLinearMapCompression J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf p.target))| < epsilon := by
  simpa [Real.norm_eq_abs] using
    G.canonicalRescaledDefectTaylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q
      (continuousLinearMapPolynomialTrace coeff polynomialDegree)
      (continuous_continuousLinearMapPolynomialTrace coeff polynomialDegree)
      tau degree htau hdegree box

/-- Canonical OS polynomial determinants converge uniformly on every full
closed half-mass Taylor box. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_polynomialDet_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_joint
    (coeff : ℕ → ℝ) (polynomialDegree : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p →
      |continuousLinearMapPolynomialDet coeff polynomialDegree
          (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric (tau b)) p.center p.target (degree b))) -
        continuousLinearMapPolynomialDet coeff polynomialDegree
          (continuousLinearMapCompression J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf p.target))| < epsilon := by
  simpa [Real.norm_eq_abs] using
    G.canonicalRescaledDefectTaylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q
      (continuousLinearMapPolynomialDet coeff polynomialDegree)
      (continuous_continuousLinearMapPolynomialDet coeff polynomialDegree)
      tau degree htau hdegree box

/-- Every finite canonical OS spectral-moment vector converges uniformly on
every full closed half-mass Taylor box. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_spectralMomentJet_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_joint
    (momentOrder : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p →
      ‖continuousLinearMapSpectralMomentJet momentOrder
          (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric (tau b)) p.center p.target (degree b))) -
        continuousLinearMapSpectralMomentJet momentOrder
          (continuousLinearMapCompression J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf p.target))‖ < epsilon := by
  exact
    G.canonicalRescaledDefectTaylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q
      (continuousLinearMapSpectralMomentJet momentOrder)
      (continuous_continuousLinearMapSpectralMomentJet momentOrder)
      tau degree htau hdegree box

end JointClosedBoxAlgebraic

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
