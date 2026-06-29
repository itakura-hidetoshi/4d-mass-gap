import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformDobrushinShiftEquivalenceL2
import Mathlib.Analysis.Normed.Algebra.Spectrum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every real parameter below the uniform Dobrushin gap belongs to the
resolvent set of each vacuum-orthogonal finite-volume Hamiltonian. -/
theorem continuous_compact_oriented_uniformDobrushin_mem_resolventSet
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    lambda ∈ resolventSet ℝ
      (U.system i).heatBathHamiltonianVacuumOrthogonalL2 := by
  let R : (U.system i).VacuumOrthogonalL2 →L[ℝ]
      (U.system i).VacuumOrthogonalL2 :=
    U.uniformResolventL2 i hlambda
  refine spectrum.mem_resolventSet_of_left_right_inverse
    (b := -R) (c := -R) ?_ ?_
  · apply ContinuousLinearMap.ext
    intro y
    have h := continuous_compact_oriented_uniformResolvent_shift_apply
      U i hlambda y
    change
      lambda • (-R y) -
          (U.system i).heatBathHamiltonianVacuumOrthogonalL2 (-R y) = y
    simpa [ContinuousCompactOrientedGaugeWilsonSystem.restrictedEnergyShiftL2,
      R, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  · apply ContinuousLinearMap.ext
    intro y
    have h := continuous_compact_oriented_uniformResolvent_apply_shift
      U i hlambda y
    change
      -R
          (lambda • y -
            (U.system i).heatBathHamiltonianVacuumOrthogonalL2 y) = y
    simpa [ContinuousCompactOrientedGaugeWilsonSystem.restrictedEnergyShiftL2,
      R, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

/-- No spectral value of a vacuum-orthogonal finite-volume Hamiltonian lies
strictly below the uniform Dobrushin gap. -/
theorem continuous_compact_oriented_uniformDobrushin_not_mem_spectrum
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    lambda ∉ spectrum ℝ
      (U.system i).heatBathHamiltonianVacuumOrthogonalL2 := by
  exact
    spectrum.notMem_iff.mpr
      (spectrum.mem_resolventSet_iff.mp
        (continuous_compact_oriented_uniformDobrushin_mem_resolventSet
          U i hlambda))

/-- Uniform lower spectral enclosure for every vacuum-orthogonal Hamiltonian in
the indexed compact Wilson family. -/
theorem continuous_compact_oriented_uniformDobrushin_spectrum_subset_Ici
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι) :
    spectrum ℝ (U.system i).heatBathHamiltonianVacuumOrthogonalL2 ⊆
      Set.Ici (continuousCompactOrientedUniformDobrushinGap U) := by
  intro lambda hlambdaSpectrum
  by_contra hlambdaLower
  have hlambda :
      lambda < continuousCompactOrientedUniformDobrushinGap U :=
    lt_of_not_ge hlambdaLower
  exact
    (continuous_compact_oriented_uniformDobrushin_not_mem_spectrum
      U i hlambda) hlambdaSpectrum

end

end MathlibAnalytic
end MGAP4D
