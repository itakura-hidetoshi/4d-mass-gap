import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventSpectralJetClosedBoxDiagonal
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventSpectralJetClosedBox
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

/-- Diagonal canonical OS convergence of a fixed algebraic spectral jet on a
complete closed half-mass Taylor box, with no rate relation. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_realResolventSpectralJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (spectralOrder : ℕ) (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2)) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapRealResolventSpectralJet spectralOrder (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) p.center p.target (degree tau))) z) - continuousLinearMapRealResolventSpectralJet spectralOrder (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z)‖ < epsilon := by
  exact (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).taylorPartialSum_realResolventSpectralJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
    (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
    rfl rfl J Q spectralOrder degree hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Diagonal canonical OS simultaneous convergence of every spectral jet
through a fixed finite order, with no rate relation. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_realResolventSpectralJetVector_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (spectralOrder : ℕ) (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2)) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapRealResolventSpectralJetVector spectralOrder (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) p.center p.target (degree tau))) z) - continuousLinearMapRealResolventSpectralJetVector spectralOrder (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z)‖ < epsilon := by
  exact (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).taylorPartialSum_realResolventSpectralJetVector_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
    (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
    rfl rfl J Q spectralOrder degree hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Diagonal canonical OS convergence of the true operator-norm spectral
derivatives on an open common real spectral region, with no rate relation. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_realResolvent_iteratedSpectralDeriv_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (spectralOrder : ℕ) (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (U : Set ℝ) (hU : IsOpen U) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ U, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ U, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ p, box.Contains p → ∀ z ∈ U,
      ‖_root_.iteratedDeriv spectralOrder (fun w => continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau) p.center p.target (degree tau))) w) z - _root_.iteratedDeriv spectralOrder (fun w => continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) w) z‖ < epsilon := by
  exact (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).taylorPartialSum_realResolvent_iteratedSpectralDeriv_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
    (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
    rfl rfl J Q spectralOrder degree hdegree box U hU margin hmargin hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
