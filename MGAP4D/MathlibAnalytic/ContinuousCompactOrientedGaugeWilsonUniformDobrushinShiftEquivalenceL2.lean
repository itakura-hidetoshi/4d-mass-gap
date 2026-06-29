import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformDobrushinResolventNormL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The shifted restricted Hamiltonian at every family index, selected using the
uniform Dobrushin gap, as a continuous linear equivalence. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData.uniformShiftEquivalenceL2
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    (U.system i).VacuumOrthogonalL2 ≃L[ℝ]
      (U.system i).VacuumOrthogonalL2 :=
  (U.system i).restrictedEnergyShiftEquivalenceL2
    (U.certificate i)
    (continuous_compact_oriented_uniformDobrushin_lambda_lt_localGap
      U i hlambda)

/-- The uniformly selected equivalence acts by the shifted restricted
Hamiltonian `Hᵢ - lambda I`. -/
theorem continuous_compact_oriented_uniformShiftEquivalenceL2_apply
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U)
    (f : (U.system i).VacuumOrthogonalL2) :
    U.uniformShiftEquivalenceL2 i hlambda f =
      (U.system i).restrictedEnergyShiftL2 lambda f := by
  unfold
    ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData.uniformShiftEquivalenceL2
  exact continuous_compact_oriented_restrictedEnergyShiftEquivalenceL2_apply
    (U.system i) (U.certificate i)
    (continuous_compact_oriented_uniformDobrushin_lambda_lt_localGap
      U i hlambda) f

/-- The inverse of the uniform shifted equivalence is exactly the previously
constructed uniform resolvent. -/
theorem continuous_compact_oriented_uniformShiftEquivalenceL2_symm_eq_resolvent
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    (U.uniformShiftEquivalenceL2 i hlambda).symm.toContinuousLinearMap =
      U.uniformResolventL2 i hlambda := by
  rfl

/-- The inverse equivalences satisfy the same family-uniform resolvent norm
bound. -/
theorem continuous_compact_oriented_uniformShiftEquivalenceL2_symm_norm_le
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    ‖(U.uniformShiftEquivalenceL2 i hlambda).symm.toContinuousLinearMap‖ ≤
      (continuousCompactOrientedUniformDobrushinGap U - lambda)⁻¹ := by
  rw [continuous_compact_oriented_uniformShiftEquivalenceL2_symm_eq_resolvent]
  exact continuous_compact_oriented_uniformResolventL2_norm_le
    U i hlambda

/-- Uniform equivalence package for the shifted vacuum-orthogonal Hamiltonians
throughout an indexed compact Wilson family. -/
theorem continuous_compact_oriented_uniformDobrushin_shiftEquivalence_package
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    ∀ i : ι,
      ∃ E : (U.system i).VacuumOrthogonalL2 ≃L[ℝ]
          (U.system i).VacuumOrthogonalL2,
        (∀ f, E f = (U.system i).restrictedEnergyShiftL2 lambda f) ∧
        ‖E.symm.toContinuousLinearMap‖ ≤
          (continuousCompactOrientedUniformDobrushinGap U - lambda)⁻¹ := by
  intro i
  refine ⟨U.uniformShiftEquivalenceL2 i hlambda, ?_, ?_⟩
  · exact continuous_compact_oriented_uniformShiftEquivalenceL2_apply
      U i hlambda
  · exact continuous_compact_oriented_uniformShiftEquivalenceL2_symm_norm_le
      U i hlambda

end

end MathlibAnalytic
end MGAP4D
