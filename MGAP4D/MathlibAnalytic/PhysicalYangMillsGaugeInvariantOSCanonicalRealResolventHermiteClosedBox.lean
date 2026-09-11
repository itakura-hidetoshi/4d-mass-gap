import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventHermiteClosedBox
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
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Canonical OS convergence of a normalized multipoint Hermite coefficient on
a complete closed half-mass Taylor box for arbitrary joint nets. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_realResolventHermiteCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (order : ℕ) {β : Type*} {m : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau m G.admissibleRescaledDefectTimeFilter)
    (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (nodes : κ → Fin (order + 1) → ℝ) (C : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ C, ∀ j, nodes q j ∈ Z) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p → ∀ q ∈ C,
      ‖continuousLinearMapRealResolventHermiteCoefficient order (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric (tau b)) p.center p.target (degree b))) (nodes q) - continuousLinearMapRealResolventHermiteCoefficient order (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) (nodes q)‖ < epsilon := by
  exact (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).taylorPartialSum_realResolventHermiteCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
    (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
    rfl rfl J Q order tau degree htau hdegree box nodes C Z hnodes margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS simultaneous convergence of the complete normalized Hermite
jet on a complete closed half-mass Taylor box for arbitrary joint nets. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_realResolventHermiteJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (order : ℕ) {β : Type*} {m : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau m G.admissibleRescaledDefectTimeFilter)
    (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (nodes : κ → Fin (order + 1) → ℝ) (C : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ C, ∀ j, nodes q j ∈ Z) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p → ∀ q ∈ C,
      ‖continuousLinearMapRealResolventHermiteJet order (fun j => continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric (tau b)) p.center p.target (degree b))) (nodes q j)) - continuousLinearMapRealResolventHermiteJet order (fun j => continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) (nodes q j))‖ < epsilon := by
  exact (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).taylorPartialSum_realResolventHermiteJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
    (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
    rfl rfl J Q order tau degree htau hdegree box nodes C Z hnodes margin hmargin hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
