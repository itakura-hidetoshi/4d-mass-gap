import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorParameterBoxCertificate
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRescaledDefectResolventTaylorStrongLimit
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

/-- Every admissible finite-time rescaled-defect resolvent carries the common
half-mass reciprocal-gap norm bound. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectOpenResolventNormBoundData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime) :
    ContinuousLinearMapOpenResolventNormBoundData
      P.VacuumOrthogonalHilbert :=
  ContinuousLinearMapOpenResolventNormBoundData.ofBelowGapFamily
    (G.mass / 2)
    (fun _ hlambda =>
      G.admissibleRescaledDefectResolvent hInnerSymmetric tau hlambda)
    (G.admissibleRescaledDefectResolvent_sub_norm_le
      T hInnerSymmetric tau)
    (G.admissibleRescaledDefectResolvent_identity
      T hInnerSymmetric tau)
    (fun hlambda =>
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_le
        (G.admissibleRescaledDefectData hInnerSymmetric tau) hlambda)

@[simp]
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectOpenResolventNormBoundData_resolvent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime) :
    (G.admissibleRescaledDefectOpenResolventNormBoundData
      T hInnerSymmetric tau).resolvent =
      G.admissibleRescaledDefectTaylorResolvent
        T hInnerSymmetric tau := by
  rfl

/-- The continuum excitation resolvent has the same reciprocal half-mass gap
operator-norm bound. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent_norm_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass / 2) :
    ‖G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda‖ ≤
      (G.mass / 2 - lambda)⁻¹ := by
  let A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
  let hASelf :=
    T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
      hP hSelf
  let hGap :=
    G.vacuumOrthogonalClosedRightHamiltonian_halfGap
      T hP hInnerSymmetric hSelf
  apply ContinuousLinearMap.opNorm_le_bound
  · exact inv_nonneg.mpr (sub_pos.mpr hlambda).le
  · intro y
    simpa only [
      VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent,
      LinearPMap.realResolvent_apply,
      LinearPMap.realResolventLinearMap_apply,
      A, hASelf, hGap] using
      A.realResolventLinearMap_norm_bound hASelf hlambda hGap y

/-- Norm-bounded open-resolvent data for the continuum excitation Hamiltonian. -/
noncomputable def VacuumSemigroupGapSlope.vacuumOrthogonalContinuumOpenResolventNormBoundData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    ContinuousLinearMapOpenResolventNormBoundData
      P.VacuumOrthogonalHilbert :=
  ContinuousLinearMapOpenResolventNormBoundData.ofBelowGapFamily
    (G.mass / 2)
    (fun _ hlambda =>
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda)
    (G.vacuumOrthogonalContinuumRealResolvent_sub_norm_le
      T hP hInnerSymmetric hSelf)
    (G.vacuumOrthogonalContinuumRealResolvent_identity
      T hP hInnerSymmetric hSelf)
    (G.vacuumOrthogonalContinuumRealResolvent_norm_le
      T hP hInnerSymmetric hSelf)

@[simp]
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumOpenResolventNormBoundData_resolvent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
      T hP hInnerSymmetric hSelf).resolvent =
      G.vacuumOrthogonalContinuumTaylorResolvent
        T hP hInnerSymmetric hSelf := by
  rfl

/-- One worst-corner sharp degree controls every admissible finite-time
resolvent throughout the full parameter box. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylor_operatorNorm_error_lt_parameterBox
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {deltaMin lambdaMax rMax epsilonMin : ℝ}
    (hdelta : deltaMin ≤ G.mass / 2)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    {N : ℕ}
    (hN : resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
      deltaMin lambdaMax rMax epsilonMin ≤ N)
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖G.admissibleRescaledDefectTaylorResolvent
          T hInnerSymmetric tau mu -
        continuousLinearMapTaylorPartialSum
          (G.admissibleRescaledDefectTaylorResolvent
            T hInnerSymmetric tau) lambda mu N‖ < epsilon := by
  simpa only [
    G.admissibleRescaledDefectOpenResolventNormBoundData_resolvent
      T hInnerSymmetric tau] using
    (G.admissibleRescaledDefectOpenResolventNormBoundData
      T hInnerSymmetric tau).taylor_operatorNorm_error_lt_parameterBox_of_worstCorner
        hdelta hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr
        hepsilon hN mu hmu

/-- The exact worst-corner degree controls every admissible finite time. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylor_operatorNorm_error_lt_parameterBox_at_worstCorner
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {deltaMin lambdaMax rMax epsilonMin : ℝ}
    (hdelta : deltaMin ≤ G.mass / 2)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖G.admissibleRescaledDefectTaylorResolvent
          T hInnerSymmetric tau mu -
        continuousLinearMapTaylorPartialSum
          (G.admissibleRescaledDefectTaylorResolvent
            T hInnerSymmetric tau) lambda mu
          (resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
            deltaMin lambdaMax rMax epsilonMin)‖ < epsilon := by
  exact G.admissibleRescaledDefectTaylor_operatorNorm_error_lt_parameterBox
    T hInnerSymmetric tau hdelta hlambdaMax hrMax0 hrMaxlt hepsilonMin
    hlambda hr0 hr hepsilon le_rfl mu hmu

/-- The same worst-corner degree directly certifies the continuum excitation
resolvent in operator norm. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumTaylor_operatorNorm_error_lt_parameterBox
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {deltaMin lambdaMax rMax epsilonMin : ℝ}
    (hdelta : deltaMin ≤ G.mass / 2)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    {N : ℕ}
    (hN : resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
      deltaMin lambdaMax rMax epsilonMin ≤ N)
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖G.vacuumOrthogonalContinuumTaylorResolvent
          T hP hInnerSymmetric hSelf mu -
        continuousLinearMapTaylorPartialSum
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf) lambda mu N‖ < epsilon := by
  simpa only [
    G.vacuumOrthogonalContinuumOpenResolventNormBoundData_resolvent
      T hP hInnerSymmetric hSelf] using
    (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
      T hP hInnerSymmetric hSelf).taylor_operatorNorm_error_lt_parameterBox_of_worstCorner
        hdelta hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr
        hepsilon hN mu hmu

/-- The exact worst-corner degree directly certifies the continuum resolvent. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumTaylor_operatorNorm_error_lt_parameterBox_at_worstCorner
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {deltaMin lambdaMax rMax epsilonMin : ℝ}
    (hdelta : deltaMin ≤ G.mass / 2)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖G.vacuumOrthogonalContinuumTaylorResolvent
          T hP hInnerSymmetric hSelf mu -
        continuousLinearMapTaylorPartialSum
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf) lambda mu
          (resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
            deltaMin lambdaMax rMax epsilonMin)‖ < epsilon := by
  exact G.vacuumOrthogonalContinuumTaylor_operatorNorm_error_lt_parameterBox
    T hP hInnerSymmetric hSelf hdelta hlambdaMax hrMax0 hrMaxlt
    hepsilonMin hlambda hr0 hr hepsilon le_rfl mu hmu

/-- Every fixed finite Taylor partial sum of the actual finite-time resolvents
converges strongly to the continuum Taylor partial sum. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_tendsto_continuum_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (N : ℕ) {lambda : ℝ} (hlambda : lambda < G.mass / 2)
    (mu : ℝ) (x : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        (continuousLinearMapTaylorPartialSum
          (G.admissibleRescaledDefectTaylorResolvent
            T hInnerSymmetric tau) lambda mu N) x)
      G.admissibleRescaledDefectTimeFilter
      (𝓝 ((continuousLinearMapTaylorPartialSum
        (G.vacuumOrthogonalContinuumTaylorResolvent
          T hP hInnerSymmetric hSelf) lambda mu N) x)) := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).taylorPartialSum_tendsto_apply
        N hlambda mu x

/-- The corresponding actual Taylor remainders converge strongly on every
fixed excitation vector. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorRemainder_tendsto_continuum_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (N : ℕ) {lambda mu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hmu : mu < G.mass / 2)
    (x : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ((G.admissibleRescaledDefectTaylorResolvent
            T hInnerSymmetric tau mu -
          continuousLinearMapTaylorPartialSum
            (G.admissibleRescaledDefectTaylorResolvent
              T hInnerSymmetric tau) lambda mu N) x))
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        ((G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf mu -
          continuousLinearMapTaylorPartialSum
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf) lambda mu N) x)) := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).taylorRemainder_tendsto_apply
        N hlambda hmu x

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
