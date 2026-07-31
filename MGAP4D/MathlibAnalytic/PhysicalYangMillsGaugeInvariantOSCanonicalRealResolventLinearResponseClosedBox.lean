import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventTraceResponseClosedBox
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventStabilityClosedBox
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

/-- Canonical joint-net convergence of finite continuous-linear response
families on complete closed half-mass Taylor boxes. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_realResolventNewtonHermiteLinearResponseFamilyPair_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (interpolationDegree : ℕ) {observableOrder : ℕ}
    (Phi : Fin (observableOrder + 1) → ((V →L[ℝ] V) →L[ℝ] ℝ)) (responseBound : ℝ)
    (hresponseBound : 0 ≤ responseBound) (hPhi : ∀ r, ‖Phi r‖ ≤ responseBound)
    {β : Type*} {m : Filter β} (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau m G.admissibleRescaledDefectTimeFilter) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (nodes : κ → Fin (interpolationDegree + 1) → ℝ) (eval : κ → ℝ) (C : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ C, ∀ j, nodes q j ∈ Z) (heval : ∀ q ∈ C, eval q ∈ Z)
    (R : ℝ) (hR : 0 ≤ R) (hdist : ∀ q ∈ C, ∀ j, |eval q - nodes q j| ≤ R)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p → ∀ q ∈ C, ‖continuousLinearMapRealResolventLinearResponseFamilyPair Phi (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric (tau b)) p.center p.target (degree b))) (nodes q) (eval q)) - continuousLinearMapRealResolventLinearResponseFamilyPair Phi (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) (nodes q) (eval q))‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).taylorPartialSum_realResolventNewtonHermiteLinearResponseFamilyPair_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q interpolationDegree Phi responseBound hresponseBound hPhi
      tau degree htau hdegree box nodes eval C Z hnodes heval R hR hdist
      margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical joint-net convergence of trace interpolants and exact trace
remainders on complete closed half-mass Taylor boxes. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_realResolventNewtonHermiteTracePair_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (interpolationDegree : ℕ) {β : Type*} {m : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau m G.admissibleRescaledDefectTimeFilter) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (nodes : κ → Fin (interpolationDegree + 1) → ℝ) (eval : κ → ℝ) (C : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ C, ∀ j, nodes q j ∈ Z) (heval : ∀ q ∈ C, eval q ∈ Z)
    (R : ℝ) (hR : 0 ≤ R) (hdist : ∀ q ∈ C, ∀ j, |eval q - nodes q j| ≤ R)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p → ∀ q ∈ C, ‖continuousLinearMapRealResolventTracePair (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric (tau b)) p.center p.target (degree b))) (nodes q) (eval q)) - continuousLinearMapRealResolventTracePair (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) (nodes q) (eval q))‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).taylorPartialSum_realResolventNewtonHermiteTracePair_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q interpolationDegree tau degree htau hdegree box nodes eval C Z
      hnodes heval R hR hdist margin hmargin hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end MathlibAnalytic
end MGAP4D
