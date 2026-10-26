import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRotationalBoundaryWitnessV5_PZ37N
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRawTwoSlabLiteralKernelV5_PJ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37O — genuine Wilson seventh coefficient gives the true third gap

The genuine rank-two physical moment pivot is kept explicit in this lemma.
PZ37N gives, at every nonminimal even period, one actual three-boundary
SU(2) Wilson minor that remains nonzero for every sufficiently small positive
fine coupling. PJ/PI/PH then identifies that same literal minor with the true
third Hankel-Schur gap of the original Gauss-law physical transfer.

This does not replace the genuine Haar kernel, assume rank three, introduce a
new axiom, or claim any volume-uniform estimate. The independently proven
small-positive pivot and true posterior-fiber connection are joined separately.
-/

namespace MGAP4D.MathlibAnalytic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000

namespace GroundStatePosteriorJoint

/-- The literal original Wilson minor of PZ37N forces a positive *true*
third physical Hankel-Schur gap on the original pivot-positive interval.
The sole remaining hypothesis is the genuine second-moment pivot at that
same beta, NOT a third-rank premise. -/
theorem p4Q2PZ37O_originalNonminimal_smallPositive_thirdGap_of_twoPivot
    (H : ℕ) (hH : 1 ≤ H) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (t : ℝ) (ht : 0 ≤ t), 0 < t → t < delta →
        0 < p4Q2PD_originalWilsonTwoMomentDet H t ht →
          0 < p4Q2PD_originalWilsonThirdMomentGap H t ht := by
  obtain ⟨A, B, C, delta, hdelta, hMinor⟩ :=
    p4Q2PZ37N_originalNonminimalLiteralMinor_exists_nonzero_smallPositive
      H hH
  refine ⟨delta, hdelta, ?_⟩
  intro t ht hpos hsmall hTwo
  exact
    (p4Q2PJ_originalThirdMoment_pos_iff_exists_literalWilsonKernelMinor
      H t ht hTwo).mpr ⟨A, B, C, hMinor t hpos hsmall⟩

/-- The same quantitative small-positive interval makes the *literal*
three-by-three moment Hankel determinant strictly positive whenever the
original physical rank-two pivot is positive. -/
theorem p4Q2PZ37O_originalNonminimal_smallPositive_hankelDet_of_twoPivot
    (H : ℕ) (hH : 1 ≤ H) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (t : ℝ) (ht : 0 ≤ t), 0 < t → t < delta →
        0 < p4Q2PD_originalWilsonTwoMomentDet H t ht →
          0 < (p4Q2PD_originalWilsonThreeHankel H t ht).det := by
  obtain ⟨delta, hdelta, hGap⟩ :=
    p4Q2PZ37O_originalNonminimal_smallPositive_thirdGap_of_twoPivot H hH
  refine ⟨delta, hdelta, ?_⟩
  intro t ht hpos hsmall hTwo
  rw [p4Q2PD_originalWilsonThreeHankel_det_eq_gap]
  exact hGap t ht hpos hsmall hTwo

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37O_originalNonminimal_smallPositive_thirdGap_of_twoPivot
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37O_originalNonminimal_smallPositive_hankelDet_of_twoPivot
