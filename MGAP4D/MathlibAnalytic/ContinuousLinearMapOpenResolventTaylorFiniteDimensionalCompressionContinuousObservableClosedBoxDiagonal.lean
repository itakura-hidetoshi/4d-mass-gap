import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionContinuousObservableClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E V W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Diagonal form: Taylor degree may depend arbitrarily on the original filter
variable, with no rate relation, for every continuous observable. -/
theorem taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (Phi : (V →L[ℝ] V) → W) (hPhi : Continuous Phi)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ p, box.Contains p →
      ‖Phi (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (F a) p.center p.target (degree a))) -
        Phi (continuousLinearMapCompression J Q
            (S.limitResolvent p.target))‖ < epsilon :=
  S.taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    B L hLgap hLresolvent J Q Phi hPhi
    (fun a => a) degree tendsto_id hdegree box

section Consequences

variable {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
variable (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
variable (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
variable (L : ContinuousLinearMapOpenResolventNormBoundData E)
variable (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
variable (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
variable (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
variable (box : ContinuousLinearMapClosedTaylorParameterBox gap)

/-- Diagonal determinant convergence on the full closed box. -/
theorem taylorPartialSum_det_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ p, box.Contains p →
      |(continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (F a) p.center p.target (degree a))).det -
        (continuousLinearMapCompression J Q
            (S.limitResolvent p.target)).det| < epsilon := by
  simpa [Real.norm_eq_abs] using
    S.taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
      B L hLgap hLresolvent J Q (fun A : V →L[ℝ] V => A.det)
      ContinuousLinearMap.continuous_det degree hdegree box

/-- Diagonal operator-polynomial convergence on the full closed box. -/
theorem taylorPartialSum_polynomial_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    (coeff : ℕ → ℝ) (polynomialDegree : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ p, box.Contains p →
      ‖continuousLinearMapPolynomial coeff polynomialDegree
          (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (F a) p.center p.target (degree a))) -
        continuousLinearMapPolynomial coeff polynomialDegree
          (continuousLinearMapCompression J Q
            (S.limitResolvent p.target))‖ < epsilon :=
  S.taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    B L hLgap hLresolvent J Q
    (continuousLinearMapPolynomial coeff polynomialDegree)
    (continuous_continuousLinearMapPolynomial coeff polynomialDegree)
    degree hdegree box

/-- Diagonal finite spectral-moment-vector convergence. -/
theorem taylorPartialSum_spectralMomentJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    (momentOrder : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ p, box.Contains p →
      ‖continuousLinearMapSpectralMomentJet momentOrder
          (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (F a) p.center p.target (degree a))) -
        continuousLinearMapSpectralMomentJet momentOrder
          (continuousLinearMapCompression J Q
            (S.limitResolvent p.target))‖ < epsilon :=
  S.taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    B L hLgap hLresolvent J Q
    (continuousLinearMapSpectralMomentJet momentOrder)
    (continuous_continuousLinearMapSpectralMomentJet momentOrder)
    degree hdegree box

end Consequences

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
