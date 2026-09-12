import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorJetLocallyUniformFiniteDimensionalCompressionLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRescaledDefectResolventTaylorJetLocallyUniformMatrixElementLimit
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Every fixed canonical OS Taylor-jet level converges uniformly in operator
norm after compression through an arbitrary finite-dimensional test space. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ lambda ∈ K,
          ‖continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k
                (G.admissibleRescaledDefectTaylorResolvent
                  T hInnerSymmetric tau) lambda) -
            continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf) lambda)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q k K hKcompact hKu hu

/-- Every finite canonical OS Taylor jet converges uniformly in compressed
operator norm on compact strict half-mass spectral sets. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact_jet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (order : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ k ≤ order, ∀ lambda ∈ K,
          ‖continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k
                (G.admissibleRescaledDefectTaylorResolvent
                  T hInnerSymmetric tau) lambda) -
            continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf) lambda)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression_jet
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q order K hKcompact hKu hu

/-- Rate-independent finite-time/Taylor-degree joint convergence in compressed
operator norm on the full closed Taylor parameter box. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_finiteDimensionalCompression_tendsto_continuum_uniform_parameterBox_of_joint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    {β : Type*} {m : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime)
    (degree : β → ℕ)
    (htau : Tendsto tau m G.admissibleRescaledDefectTimeFilter)
    (hdegree : Tendsto degree m atTop)
    {deltaMin lambdaMin lambdaMax rMax : ℝ}
    (hdelta : deltaMin ≤ G.mass / 2)
    (hlambdaBounds : lambdaMin ≤ lambdaMax)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ lambda r mu : ℝ,
        lambdaMin ≤ lambda → lambda ≤ lambdaMax →
        0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
        ‖continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric (tau b)) lambda mu (degree b)) -
          continuousLinearMapCompression J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf mu)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).taylorPartialSum_tendsto_limitResolvent_finiteDimensionalCompression_uniform_parameterBox_of_joint
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q tau degree htau hdegree
        hdelta hlambdaBounds hlambdaMax hrMax0 hrMaxlt

/-- Diagonal finite-dimensional-compression form: the Taylor degree may depend
arbitrarily on admissible time, with no speed relation. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_finiteDimensionalCompression_tendsto_continuum_uniform_parameterBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    {deltaMin lambdaMin lambdaMax rMax : ℝ}
    (hdelta : deltaMin ≤ G.mass / 2)
    (hlambdaBounds : lambdaMin ≤ lambdaMax)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ lambda r mu : ℝ,
          lambdaMin ≤ lambda → lambda ≤ lambdaMax →
          0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
          ‖continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (G.admissibleRescaledDefectTaylorResolvent
                  T hInnerSymmetric tau) lambda mu (degree tau)) -
            continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf mu)‖ < epsilon := by
  exact
    G.canonicalRescaledDefectTaylorPartialSum_finiteDimensionalCompression_tendsto_continuum_uniform_parameterBox_of_joint
      T hP hInnerSymmetric hSelf J Q
      (fun tau => tau) degree tendsto_id hdegree
      hdelta hlambdaBounds hlambdaMax hrMax0 hrMaxlt

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
