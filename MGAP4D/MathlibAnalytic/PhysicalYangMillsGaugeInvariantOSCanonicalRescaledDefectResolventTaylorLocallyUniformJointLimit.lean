import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorLocallyUniformJointLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRescaledDefectResolventTaylorJointLimit
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 4000000

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The actual canonical finite-time resolvents converge strongly to the
continuum excitation resolvent uniformly on every compact spectral-parameter
set contained in a strict half-mass sublevel. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorResolvent_tendsto_continuum_uniformOn_compact_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < G.mass / 2)
    (x : P.VacuumOrthogonalHilbert) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ mu ∈ K,
          ‖G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric tau mu x -
            G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf mu x‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).value_tendsto_uniformOn_compact_apply
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl K hKcompact hKu hu x

/-- Rate-independent finite-time/Taylor joint convergence is uniform on the
entire closed spectral parameter box. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_tendsto_continuum_apply_uniform_parameterBox_of_joint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
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
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (x : P.VacuumOrthogonalHilbert) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ lambda r mu : ℝ,
        lambdaMin ≤ lambda → lambda ≤ lambdaMax →
        0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
        ‖(continuousLinearMapTaylorPartialSum
            (G.admissibleRescaledDefectTaylorResolvent
              T hInnerSymmetric (tau b)) lambda mu (degree b)) x -
          G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf mu x‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).taylorPartialSum_tendsto_limitResolvent_apply_uniform_parameterBox_of_joint
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl tau degree htau hdegree
        hdelta hlambdaBounds hlambdaMax hrMax0 hrMaxlt x

/-- Diagonal locally uniform form: the Taylor degree may depend arbitrarily on
the admissible time, provided it tends to infinity along the canonical filter. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_tendsto_continuum_apply_uniform_parameterBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    {deltaMin lambdaMin lambdaMax rMax : ℝ}
    (hdelta : deltaMin ≤ G.mass / 2)
    (hlambdaBounds : lambdaMin ≤ lambdaMax)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (x : P.VacuumOrthogonalHilbert) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ lambda r mu : ℝ,
          lambdaMin ≤ lambda → lambda ≤ lambdaMax →
          0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
          ‖(continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric tau) lambda mu (degree tau)) x -
            G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf mu x‖ < epsilon := by
  exact
    G.canonicalRescaledDefectTaylorPartialSum_tendsto_continuum_apply_uniform_parameterBox_of_joint
      T hP hInnerSymmetric hSelf
      (fun tau => tau) degree tendsto_id hdegree
      hdelta hlambdaBounds hlambdaMax hrMax0 hrMaxlt x

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
