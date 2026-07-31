import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventLinearResponseClosedBoxDiagonal
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventTraceResponseClosedBoxDiagonal
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventLinearResponseClosedBox
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

/-- Diagonal canonical no-rate convergence for a finite family of
continuous-linear Newton-Hermite spectral responses. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_realResolventNewtonHermiteLinearResponseFamilyPair_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (interpolationDegree : ℕ) {observableOrder : ℕ}
    (Phi : Fin (observableOrder + 1) → ((V →L[ℝ] V) →L[ℝ] ℝ)) (responseBound : ℝ)
    (hresponseBound : 0 ≤ responseBound) (hPhi : ∀ r, ‖Phi r‖ ≤ responseBound)
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (nodes : κ → Fin (interpolationDegree + 1) → ℝ) (eval : κ → ℝ) (C : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ C, ∀ j, nodes q j ∈ Z) (heval : ∀ q ∈ C, eval q ∈ Z)
    (R : ℝ) (hR : 0 ≤ R) (hdist : ∀ q ∈ C, ∀ j, |eval q - nodes q j| ≤ R)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ p, box.Contains p → ∀ q ∈ C, ‖continuousLinearMapRealResolventLinearResponseFamilyPair Phi (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) p.center p.target (degree tau))) (nodes q) (eval q)) - continuousLinearMapRealResolventLinearResponseFamilyPair Phi (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) (nodes q) (eval q))‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).taylorPartialSum_realResolventNewtonHermiteLinearResponseFamilyPair_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q interpolationDegree Phi responseBound hresponseBound hPhi degree hdegree
      box nodes eval C Z hnodes heval R hR hdist margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Diagonal canonical no-rate convergence of trace interpolants and exact
trace remainders. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_realResolventNewtonHermiteTracePair_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (interpolationDegree : ℕ) (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (nodes : κ → Fin (interpolationDegree + 1) → ℝ) (eval : κ → ℝ) (C : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ C, ∀ j, nodes q j ∈ Z) (heval : ∀ q ∈ C, eval q ∈ Z)
    (R : ℝ) (hR : 0 ≤ R) (hdist : ∀ q ∈ C, ∀ j, |eval q - nodes q j| ≤ R)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ p, box.Contains p → ∀ q ∈ C, ‖continuousLinearMapRealResolventTracePair (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) p.center p.target (degree tau))) (nodes q) (eval q)) - continuousLinearMapRealResolventTracePair (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) (nodes q) (eval q))‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).taylorPartialSum_realResolventNewtonHermiteTracePair_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q interpolationDegree degree hdegree box nodes eval C Z
      hnodes heval R hR hdist margin hmargin hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end MathlibAnalytic
end MGAP4D
