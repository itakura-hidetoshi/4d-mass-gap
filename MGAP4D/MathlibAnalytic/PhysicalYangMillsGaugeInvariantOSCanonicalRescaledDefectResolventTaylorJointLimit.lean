import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorJointStrongLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRescaledDefectResolventTaylorParameterBoxCertificate
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 3200000

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- All admissible finite-time resolvents form one norm-bounded family at the
common half-mass threshold. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectOpenResolventNormBoundFamilyData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    ContinuousLinearMapOpenResolventNormBoundFamilyData
      (G.mass / 2)
      (fun tau : G.AdmissibleRescaledDefectTime =>
        G.admissibleRescaledDefectTaylorResolvent
          T hInnerSymmetric tau) where
  normBoundData := fun tau =>
    G.admissibleRescaledDefectOpenResolventNormBoundData
      T hInnerSymmetric tau
  gap_eq := by
    intro tau
    rfl
  resolvent_eq := by
    intro tau
    exact
      G.admissibleRescaledDefectOpenResolventNormBoundData_resolvent
        T hInnerSymmetric tau

/-- At every fixed admissible time, Taylor partial sums converge in operator
norm to the finite-time resolvent. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_tendsto_resolvent_atTop
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda r mu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hr0 : 0 ≤ r) (hrlt : r < G.mass / 2 - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) :
    Tendsto
      (fun N : ℕ =>
        continuousLinearMapTaylorPartialSum
          (G.admissibleRescaledDefectTaylorResolvent
            T hInnerSymmetric tau) lambda mu N)
      atTop
      (𝓝 (G.admissibleRescaledDefectTaylorResolvent
        T hInnerSymmetric tau mu)) := by
  simpa only [
    G.admissibleRescaledDefectOpenResolventNormBoundData_resolvent
      T hInnerSymmetric tau] using
    (G.admissibleRescaledDefectOpenResolventNormBoundData
      T hInnerSymmetric tau).taylorPartialSum_tendsto_resolvent_atTop
        hlambda hr0 hrlt hmu

/-- The continuum vacuum-orthogonal Taylor series converges in operator norm to
the continuum resolvent on every strict half-mass ball. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumTaylorPartialSum_tendsto_resolvent_atTop
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda r mu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hr0 : 0 ≤ r) (hrlt : r < G.mass / 2 - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) :
    Tendsto
      (fun N : ℕ =>
        continuousLinearMapTaylorPartialSum
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf) lambda mu N)
      atTop
      (𝓝 (G.vacuumOrthogonalContinuumTaylorResolvent
        T hP hInnerSymmetric hSelf mu)) := by
  simpa only [
    G.vacuumOrthogonalContinuumOpenResolventNormBoundData_resolvent
      T hP hInnerSymmetric hSelf] using
    (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
      T hP hInnerSymmetric hSelf).taylorPartialSum_tendsto_resolvent_atTop
        hlambda hr0 hrlt hmu

/-- For any finite-time selection net, every cofinal Taylor-degree net drives
the finite-time Taylor remainder to zero uniformly in operator norm. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorRemainder_tendsto_zero_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {β : Type*} {m : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime)
    (degree : β → ℕ) (hdegree : Tendsto degree m atTop)
    {deltaMin lambdaMax rMax : ℝ}
    (hdelta : deltaMin ≤ G.mass / 2)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    {lambda r : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    Tendsto
      (fun b =>
        G.admissibleRescaledDefectTaylorResolvent
            T hInnerSymmetric (tau b) mu -
          continuousLinearMapTaylorPartialSum
            (G.admissibleRescaledDefectTaylorResolvent
              T hInnerSymmetric (tau b)) lambda mu (degree b))
      m (𝓝 0) := by
  exact
    (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
      T hInnerSymmetric).taylorRemainder_tendsto_zero_of_tendsto_degree
        tau degree hdegree hdelta hlambdaMax hrMax0 hrMaxlt
        hlambda hr0 hr mu hmu

/-- The finite-time and Taylor-degree limits commute in the strongest
rate-independent form needed here: any joint net tending to the canonical time
filter and to infinite degree converges strongly to the continuum resolvent. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_tendsto_continuum_apply_of_joint
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
    {deltaMin lambdaMax rMax : ℝ}
    (hdelta : deltaMin ≤ G.mass / 2)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    {lambda r mu : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hmu : ‖mu - lambda‖ ≤ r)
    (x : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun b =>
        (continuousLinearMapTaylorPartialSum
          (G.admissibleRescaledDefectTaylorResolvent
            T hInnerSymmetric (tau b)) lambda mu (degree b)) x)
      m
      (𝓝 (G.vacuumOrthogonalContinuumTaylorResolvent
        T hP hInnerSymmetric hSelf mu x)) := by
  have hmuGap : mu < G.mass / 2 := by
    have hle : mu - lambda ≤ ‖mu - lambda‖ := by
      simpa [Real.norm_eq_abs] using le_abs_self (mu - lambda)
    linarith
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).taylorPartialSum_tendsto_limitResolvent_apply_of_joint
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        tau degree htau hdegree hdelta hlambdaMax hrMax0 hrMaxlt
        hlambda hr0 hr hmu hmuGap x

/-- Diagonal form: the Taylor degree may depend arbitrarily on the admissible
time, provided it tends to infinity along the canonical time filter. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_tendsto_continuum_apply_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    {deltaMin lambdaMax rMax : ℝ}
    (hdelta : deltaMin ≤ G.mass / 2)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    {lambda r mu : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hmu : ‖mu - lambda‖ ≤ r)
    (x : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        (continuousLinearMapTaylorPartialSum
          (G.admissibleRescaledDefectTaylorResolvent
            T hInnerSymmetric tau) lambda mu (degree tau)) x)
      G.admissibleRescaledDefectTimeFilter
      (𝓝 (G.vacuumOrthogonalContinuumTaylorResolvent
        T hP hInnerSymmetric hSelf mu x)) := by
  exact G.canonicalRescaledDefectTaylorPartialSum_tendsto_continuum_apply_of_joint
    T hP hInnerSymmetric hSelf
    (fun tau => tau) degree tendsto_id hdegree
    hdelta hlambdaMax hrMax0 hrMaxlt hlambda hr0 hr hmu x

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
