import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorJetFiniteDimensionalCompressionTraceDeterminantLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRescaledDefectResolventTaylorJetLocallyUniformFiniteDimensionalCompressionLimit
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

/-- Every fixed canonical OS Taylor-jet trace converges uniformly after
finite-dimensional compression on compact strict half-mass spectral sets. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_trace_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ lambda ∈ K,
        |continuousLinearMapTrace
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k
                (G.admissibleRescaledDefectTaylorResolvent
                  T hInnerSymmetric tau) lambda)) -
          continuousLinearMapTrace
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf) lambda))| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_trace_finiteDimensionalCompression_tendsto_uniformOn_compact
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q k K hKcompact hKu hu

/-- Every finite canonical OS Taylor jet has simultaneously convergent
compressed traces on compact strict half-mass spectral sets. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_trace_finiteDimensionalCompression_tendsto_continuum_uniformOn_compact_jet
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
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
          |continuousLinearMapTrace
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) lambda)) -
            continuousLinearMapTrace
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k
                  (G.vacuumOrthogonalContinuumTaylorResolvent
                    T hP hInnerSymmetric hSelf) lambda))| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_trace_finiteDimensionalCompression_tendsto_uniformOn_compact_jet
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q order K hKcompact hKu hu

/-- At every fixed strict half-mass spectral point, determinants of compressed
canonical OS Taylor jets converge to the continuum determinant. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorIteratedDeriv_det_finiteDimensionalCompression_tendsto_continuum
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (k : ℕ) {lambda : ℝ} (hlambda : lambda < G.mass / 2) :
    Tendsto
      (fun tau =>
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k
            (G.admissibleRescaledDefectTaylorResolvent
              T hInnerSymmetric tau) lambda)).det)
      G.admissibleRescaledDefectTimeFilter
      (𝓝 ((continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf) lambda)).det)) := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).iteratedDeriv_det_finiteDimensionalCompression_tendsto
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q k hlambda

/-- Rate-independent joint convergence of compressed canonical OS Taylor
partial-sum traces on the full closed Taylor parameter box. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_trace_finiteDimensionalCompression_tendsto_continuum_uniform_parameterBox_of_joint
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    {β : Type*} {m : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau m G.admissibleRescaledDefectTimeFilter)
    (hdegree : Tendsto degree m atTop)
    {deltaMin lambdaMin lambdaMax rMax : ℝ}
    (hdelta : deltaMin ≤ G.mass / 2)
    (hlambdaBounds : lambdaMin ≤ lambdaMax)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax) (hrMaxlt : rMax < deltaMin - lambdaMax) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ lambda r mu : ℝ,
        lambdaMin ≤ lambda → lambda ≤ lambdaMax →
        0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
        |continuousLinearMapTrace
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (G.admissibleRescaledDefectTaylorResolvent
                  T hInnerSymmetric (tau b)) lambda mu (degree b))) -
          continuousLinearMapTrace
            (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf mu))| < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).taylorPartialSum_trace_finiteDimensionalCompression_tendsto_limitResolvent_uniform_parameterBox_of_joint
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q tau degree htau hdegree
        hdelta hlambdaBounds hlambdaMax hrMax0 hrMaxlt

/-- At every fixed valid Taylor-box point, determinants of compressed canonical
OS Taylor partial sums converge along arbitrary joint time/degree nets. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_det_finiteDimensionalCompression_tendsto_continuum_of_joint
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    {β : Type*} {m : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau m G.admissibleRescaledDefectTimeFilter)
    (hdegree : Tendsto degree m atTop)
    {deltaMin lambdaMin lambdaMax rMax lambda r mu : ℝ}
    (hdelta : deltaMin ≤ G.mass / 2)
    (hlambdaBounds : lambdaMin ≤ lambdaMax)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax) (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hlambdaMin : lambdaMin ≤ lambda) (hlambdaMax' : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax) (hmu : ‖mu - lambda‖ ≤ r) :
    Tendsto
      (fun b =>
        (continuousLinearMapCompression J Q
          (continuousLinearMapTaylorPartialSum
            (G.admissibleRescaledDefectTaylorResolvent
              T hInnerSymmetric (tau b)) lambda mu (degree b))).det)
      m
      (𝓝 ((continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent
          T hP hInnerSymmetric hSelf mu)).det)) := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).taylorPartialSum_det_finiteDimensionalCompression_tendsto_limitResolvent_of_joint
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q tau degree htau hdegree
        hdelta hlambdaBounds hlambdaMax hrMax0 hrMaxlt
        hlambdaMin hlambdaMax' hr0 hr hmu

/-- Diagonal trace form: Taylor degree may depend arbitrarily on admissible time,
with no speed relation, while convergence remains uniform on the closed box. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_trace_finiteDimensionalCompression_tendsto_continuum_uniform_parameterBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
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
    (hrMax0 : 0 ≤ rMax) (hrMaxlt : rMax < deltaMin - lambdaMax) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter, ∀ lambda r mu : ℝ,
        lambdaMin ≤ lambda → lambda ≤ lambdaMax →
        0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
        |continuousLinearMapTrace
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (G.admissibleRescaledDefectTaylorResolvent
                  T hInnerSymmetric tau) lambda mu (degree tau))) -
          continuousLinearMapTrace
            (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf mu))| < epsilon := by
  exact
    G.canonicalRescaledDefectTaylorPartialSum_trace_finiteDimensionalCompression_tendsto_continuum_uniform_parameterBox_of_joint
      T hP hInnerSymmetric hSelf J Q
      (fun tau => tau) degree tendsto_id hdegree
      hdelta hlambdaBounds hlambdaMax hrMax0 hrMaxlt

/-- Diagonal determinant form at a fixed valid Taylor-box point. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_det_finiteDimensionalCompression_tendsto_continuum_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
    (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    {deltaMin lambdaMin lambdaMax rMax lambda r mu : ℝ}
    (hdelta : deltaMin ≤ G.mass / 2)
    (hlambdaBounds : lambdaMin ≤ lambdaMax)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax) (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hlambdaMin : lambdaMin ≤ lambda) (hlambdaMax' : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax) (hmu : ‖mu - lambda‖ ≤ r) :
    Tendsto
      (fun tau =>
        (continuousLinearMapCompression J Q
          (continuousLinearMapTaylorPartialSum
            (G.admissibleRescaledDefectTaylorResolvent
              T hInnerSymmetric tau) lambda mu (degree tau))).det)
      G.admissibleRescaledDefectTimeFilter
      (𝓝 ((continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent
          T hP hInnerSymmetric hSelf mu)).det)) := by
  exact
    G.canonicalRescaledDefectTaylorPartialSum_det_finiteDimensionalCompression_tendsto_continuum_of_joint
      T hP hInnerSymmetric hSelf J Q
      (fun tau => tau) degree tendsto_id hdegree
      hdelta hlambdaBounds hlambdaMax hrMax0 hrMaxlt
      hlambdaMin hlambdaMax' hr0 hr hmu

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
