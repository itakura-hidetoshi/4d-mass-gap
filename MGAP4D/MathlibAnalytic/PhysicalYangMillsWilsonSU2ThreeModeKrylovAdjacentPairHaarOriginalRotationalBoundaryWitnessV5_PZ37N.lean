import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalNonminimalMinorNonzeroV5_PZ37N
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonCenterWitnessV5_IY
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyInfiniteRange
import Mathlib.Tactic

/-!
# PZ37N — three genuine boundary action values from the SU(2) rotation path

Rotate a single actual canonical primary spatial link inside the original SU(2)
boundary configuration. The path is continuous; its endpoints are the true
identity configuration and the previously certified primary center twist.
The intermediate value theorem supplies an actual boundary with spatial
Wilson action exactly one. This is not an artificial scalar boundary action.
-/

namespace MGAP4D.MathlibAnalytic
open scoped Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000

namespace GroundStatePosteriorJoint

local notation "SU" => SpecialUnitaryMatrixGroup 2

private theorem p4Q2PZ37N_rotation_continuous :
    Continuous (specialUnitaryTwoRotation : ℝ → SU) := by
  refine Continuous.subtype_mk ?_ (fun t => (specialUnitaryTwoRotation t).property)
  change Continuous (fun t : ℝ => specialUnitaryTwoRotationMatrix t)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] <;>
    fun_prop

private theorem p4Q2PZ37N_rotation_zero :
    specialUnitaryTwoRotation 0 = (1 : SU) := by
  apply Subtype.ext
  change specialUnitaryTwoRotationMatrix 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [specialUnitaryTwoRotationMatrix, Matrix.one_apply]

private theorem p4Q2PZ37N_rotation_pi_center :
    specialUnitaryTwoRotation Real.pi = specialUnitaryTwoNegativeIdentity := by
  apply Subtype.ext
  change specialUnitaryTwoRotationMatrix Real.pi =
    -(1 : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [specialUnitaryTwoRotationMatrix, Matrix.one_apply, Real.cos_pi, Real.sin_pi]

/-- The true one-link SU(2) rotation in the original four-dimensional
physical-link carrier, prior to canonical spatial-slice restriction. -/
noncomputable def p4Q2PZ37N_primaryLinkRotation (H : ℕ) (t : ℝ) :
    PeriodicHypercubicEvenEdge H → SU :=
  Function.update
    (fun _ => (1 : SU))
    (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 0)
    (specialUnitaryTwoRotation t)

/-- Genuine right spatial boundary associated with the rotated physical link. -/
noncomputable def p4Q2PZ37N_rotatedBoundary (H : ℕ) (t : ℝ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 :=
  periodicHypercubicEvenSpatialSliceRestriction
    (p4Q2PZ37N_primaryLinkRotation H t)

private theorem p4Q2PZ37N_boundary_continuous (H : ℕ) :
    Continuous (p4Q2PZ37N_rotatedBoundary H) := by
  classical
  apply continuous_pi
  intro e
  change Continuous (fun t : ℝ =>
    p4Q2PZ37N_primaryLinkRotation H t
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H e))
  unfold p4Q2PZ37N_primaryLinkRotation
  by_cases h :
      periodicHypercubicEvenSpatialSliceLinkEmbedding H e =
        periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 0
  · simpa [Function.update_apply, h] using
      p4Q2PZ37N_rotation_continuous
  · simpa [Function.update_apply, h] using
      (continuous_const : Continuous (fun _ : ℝ => (1 : SU)))

private theorem p4Q2PZ37N_boundary_zero (H : ℕ) :
    p4Q2PZ37N_rotatedBoundary H 0 =
      (fun _ => (1 : SU)) := by
  funext e
  simp [p4Q2PZ37N_rotatedBoundary,
    p4Q2PZ37N_primaryLinkRotation, p4Q2PZ37N_rotation_zero]

private theorem p4Q2PZ37N_boundary_pi (H : ℕ) :
    p4Q2PZ37N_rotatedBoundary H Real.pi =
      periodicHypercubicEvenSpatialSliceRestriction
        (p4Q2IY_onePrimaryLinkCentralTwist H) := by
  simp [p4Q2PZ37N_rotatedBoundary, p4Q2PZ37N_primaryLinkRotation,
    p4Q2IY_onePrimaryLinkCentralTwist, p4Q2PZ37N_rotation_pi_center]

/-- Every finite even spatial lattice has three ACTUAL SU(2) boundaries
with strictly ordered original half-spatial Wilson energies.
The middle boundary comes from a rotation angle selected by the IVT,
not from postulating an arbitrary real-valued action. -/
theorem p4Q2PZ37N_originalThreeBoundaryStrictHalfActions (H : ℕ) :
    ∃ A B C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      p4Q2PS_originalHalfSpatialAction H A <
        p4Q2PS_originalHalfSpatialAction H B ∧
      p4Q2PS_originalHalfSpatialAction H B <
        p4Q2PS_originalHalfSpatialAction H C := by
  let W := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
  let w := p4Q2PS_originalHalfSpatialAction H
  let f : ℝ → ℝ := fun t => W (p4Q2PZ37N_rotatedBoundary H t)
  have hf : Continuous f :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2).comp
      (p4Q2PZ37N_boundary_continuous H)
  have hfzero : f 0 = 0 := by
    change W (p4Q2PZ37N_rotatedBoundary H 0) = 0
    rw [p4Q2PZ37N_boundary_zero H]
    exact p4Q2IY_allOneSpatialWilsonAction_zero H
  have hfpi : (2 : ℝ) ≤ f Real.pi := by
    change (2 : ℝ) ≤ W (p4Q2PZ37N_rotatedBoundary H Real.pi)
    rw [p4Q2PZ37N_boundary_pi H]
    exact p4Q2IY_actualSpatialWilsonAction_twist_ge_two H
  have hOneIcc : (1 : ℝ) ∈ Set.Icc (f 0) (f Real.pi) := by
    rw [hfzero]
    exact ⟨by norm_num, by linarith⟩
  obtain ⟨t, _ht, hft⟩ :=
    (intermediate_value_Icc (le_of_lt Real.pi_pos) hf.continuousOn) hOneIcc
  have hwzero :
      w (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => (1 : SU)) = 0 := by
    change (1 / 2 : ℝ) * W (fun _ => (1 : SU)) = 0
    rw [p4Q2IY_allOneSpatialWilsonAction_zero H]
    ring
  have hwmid : w (p4Q2PZ37N_rotatedBoundary H t) = (1 / 2 : ℝ) := by
    change (1 / 2 : ℝ) * f t = 1 / 2
    rw [hft]
    ring
  have hwpi : (1 : ℝ) ≤ w (p4Q2PZ37N_rotatedBoundary H Real.pi) := by
    change (1 : ℝ) ≤ (1 / 2 : ℝ) * f Real.pi
    linarith
  refine ⟨(fun _ => (1 : SU)),
    p4Q2PZ37N_rotatedBoundary H t,
    p4Q2PZ37N_rotatedBoundary H Real.pi, ?_, ?_⟩
  · rw [hwzero, hwmid]
    norm_num
  · rw [hwmid]
    linarith

/-- Unconditional finite-volume three-boundary witness: the original
interacting Wilson minor is nonzero for sufficiently small positive beta.
The small-coupling radius is not asserted to be volume-uniform. -/
theorem p4Q2PZ37N_originalNonminimalLiteralMinor_exists_nonzero_smallPositive
    (H : ℕ) (hH : 1 ≤ H) :
    ∃ A B C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      ∃ epsilon : ℝ, 0 < epsilon ∧
        ∀ beta : ℝ, 0 < beta → beta < epsilon →
          p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C ≠ 0 := by
  obtain ⟨A, B, C, hAB, hBC⟩ :=
    p4Q2PZ37N_originalThreeBoundaryStrictHalfActions H
  have hAC := lt_trans hAB hBC
  obtain ⟨epsilon, hepsilon, hnonzero⟩ :=
    p4Q2PZ37N_originalNonminimalLiteralMinor_nonzero_smallPositive
      H hH A B C hAB.ne hAC.ne hBC.ne
  exact ⟨A, B, C, epsilon, hepsilon, hnonzero⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37N_originalThreeBoundaryStrictHalfActions
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37N_originalNonminimalLiteralMinor_exists_nonzero_smallPositive
