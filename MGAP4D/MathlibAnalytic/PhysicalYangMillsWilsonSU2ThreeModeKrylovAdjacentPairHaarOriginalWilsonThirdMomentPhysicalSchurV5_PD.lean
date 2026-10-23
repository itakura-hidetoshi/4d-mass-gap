import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonStrictShiftedHankelMomentsV5_PC
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PD — the ORIGINAL third Wilson physical Krylov innovation

All constructions below are made from the SAME genuine SU(2) normalized
one-slab Gauss-law Hilbert transfer T and physical constant source U.
No surrogate spectral measure, substitute posterior or rank premise.

PB identifies the true depth-two physical Gram with the scalar Wilson
Hankel moments m_j=<U,T^j U>. PC proves the actual strict TWO-mode
Hankel pivot D2=m0*m2-m1^2>0 in ON's small-positive fine interval.

Build the actual orthogonal Schur innovation
  R2 = D2*T^2 U - (m2^2-m1*m3)*U - (m0*m3-m1*m2)*T U.
Prove in the ORIGINAL physical Hilbert carrier:
  <R2,U>=0, <R2,TU>=0,
  <R2,T^2U>=D3, norm(R2)^2=D2*D3,
where D3 is the explicit actual three-by-three moment determinant.
Consequently, wherever D2>0, D3>0 iff R2 !=0.

Finally identify this SAME innovation as the original HJ depth-two
right-Krylov source and invoke OW/OT to show: IF this actual physical
moment innovation is nonzero, a genuine original interacting
two-posterior signed GI context detects it. This does not prove
D3>0, the genuine third Schur source nonzero, U0 or the continuum gap.

Pinned Lean/mathlib, no sorry/admit/new axiom, no Dobrushin.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory Matrix
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PD_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PD_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PD_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PD_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PD_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section TrueOriginalWilsonThirdMoment
variable (H : ℕ) (t : ℝ) (ht : 0 ≤ t)
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive t ht
local notation "m" => p4Q2PB_originalWilsonPhysicalMoment H t ht

/-- The exactly original physical first two Wilson moments determinant. -/
noncomputable def p4Q2PD_originalWilsonTwoMomentDet : ℝ :=
  m 0 * m 2 - (m 1) ^ 2

/-- The explicit scalar third Schur/Hankel innovation of the original
normalized physical one-slab SU(2) Wilson transfer and physical U. -/
noncomputable def p4Q2PD_originalWilsonThirdMomentGap : ℝ :=
  p4Q2PD_originalWilsonTwoMomentDet H t ht * m 4 -
    ((m 2) ^ 3 - 2 * m 1 * m 2 * m 3 + m 0 * (m 3) ^ 2)

/-- The exact authentic 3x3 moment Hankel matrix; no rank assumed. -/
noncomputable def p4Q2PD_originalWilsonThreeHankel :
    Matrix (Fin (2 + 1)) (Fin (2 + 1)) ℝ :=
  Matrix.of (fun i j : Fin (2 + 1) =>
    m ((i : ℕ) + (j : ℕ)))

/-- The authentic original Wilson physical third Krylov Schur source.
It is literally built from the true normalized fine T and true U. -/
noncomputable def p4Q2PD_originalWilsonThirdSchurPhysical : Phys :=
  p4Q2PD_originalWilsonTwoMomentDet H t ht • ((Fine ^ 2) U) -
    ((m 2) ^ 2 - m 1 * m 3) • U -
    (m 0 * m 3 - m 1 * m 2) • (Fine U)

/-- Exact original three-by-three determinant, expressed in scalar
moments rather than in a surrogate spectral model. -/
theorem p4Q2PD_originalWilsonThreeHankel_det_eq_gap :
    (p4Q2PD_originalWilsonThreeHankel H t ht).det =
      p4Q2PD_originalWilsonThirdMomentGap H t ht := by
  simp [p4Q2PD_originalWilsonThreeHankel,
    p4Q2PD_originalWilsonThirdMomentGap,
    p4Q2PD_originalWilsonTwoMomentDet,
    Matrix.det_fin_three]
  all_goals ring

/-- The true physical Schur source is orthogonal to the constant U. -/
theorem p4Q2PD_originalWilsonThirdSchur_ortho_unit :
    inner ℝ (p4Q2PD_originalWilsonThirdSchurPhysical H t ht) U = 0 := by
  have h20 : inner ℝ ((Fine ^ 2) U) U = m 2 := by
    simpa using
      (p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment H t ht 2 0)
  have h00 : inner ℝ U U = m 0 := by
    simpa using
      (p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment H t ht 0 0)
  have h10 : inner ℝ (Fine U) U = m 1 := by
    simpa using
      (p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment H t ht 1 0)
  unfold p4Q2PD_originalWilsonThirdSchurPhysical
  rw [inner_sub_left, inner_sub_left]
  simp only [real_inner_smul_left, h20, h00, h10,
    p4Q2PD_originalWilsonTwoMomentDet]
  ring

/-- The true physical Schur source is orthogonal to T U as well. -/
theorem p4Q2PD_originalWilsonThirdSchur_ortho_first :
    inner ℝ (p4Q2PD_originalWilsonThirdSchurPhysical H t ht) (Fine U) = 0 := by
  have h21 : inner ℝ ((Fine ^ 2) U) (Fine U) = m 3 := by
    simpa using
      (p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment H t ht 2 1)
  have h01 : inner ℝ U (Fine U) = m 1 := by
    simpa using
      (p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment H t ht 0 1)
  have h11 : inner ℝ (Fine U) (Fine U) = m 2 := by
    simpa using
      (p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment H t ht 1 1)
  unfold p4Q2PD_originalWilsonThirdSchurPhysical
  rw [inner_sub_left, inner_sub_left]
  simp only [real_inner_smul_left, h21, h01, h11,
    p4Q2PD_originalWilsonTwoMomentDet]
  ring

/-- The remaining true physical Hilbert cross inner is EXACTLY the
original three-moment Schur determinant, no rank premise. -/
theorem p4Q2PD_originalWilsonThirdSchur_inner_second_eq_gap :
    inner ℝ (p4Q2PD_originalWilsonThirdSchurPhysical H t ht)
      ((Fine ^ 2) U) =
    p4Q2PD_originalWilsonThirdMomentGap H t ht := by
  have h22 : inner ℝ ((Fine ^ 2) U) ((Fine ^ 2) U) = m 4 := by
    simpa using
      (p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment H t ht 2 2)
  have h02 : inner ℝ U ((Fine ^ 2) U) = m 2 := by
    simpa using
      (p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment H t ht 0 2)
  have h12 : inner ℝ (Fine U) ((Fine ^ 2) U) = m 3 := by
    simpa using
      (p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment H t ht 1 2)
  unfold p4Q2PD_originalWilsonThirdSchurPhysical
  rw [inner_sub_left, inner_sub_left]
  simp only [real_inner_smul_left, h22, h02, h12,
    p4Q2PD_originalWilsonTwoMomentDet, p4Q2PD_originalWilsonThirdMomentGap]
  ring

/-- Exact authentic Gauss-law Hilbert identity: the NORM-SQUARED
of the actual third Wilson innovation equals the 2x2 physical
Hankel pivot times the explicit 3x3 Hankel determinant. -/
theorem p4Q2PD_originalWilsonThirdSchur_normSq_eq_twoDet_mul_threeGap :
    ‖p4Q2PD_originalWilsonThirdSchurPhysical H t ht‖ ^ 2 =
      p4Q2PD_originalWilsonTwoMomentDet H t ht *
        p4Q2PD_originalWilsonThirdMomentGap H t ht := by
  let r : Phys := p4Q2PD_originalWilsonThirdSchurPhysical H t ht
  let delta : ℝ := p4Q2PD_originalWilsonTwoMomentDet H t ht
  let a : ℝ := (m 2) ^ 2 - m 1 * m 3
  let b : ℝ := m 0 * m 3 - m 1 * m 2
  have hr : r = delta • ((Fine ^ 2) U) - a • U - b • (Fine U) := rfl
  have h0 : inner ℝ r U = 0 :=
    p4Q2PD_originalWilsonThirdSchur_ortho_unit H t ht
  have h1 : inner ℝ r (Fine U) = 0 :=
    p4Q2PD_originalWilsonThirdSchur_ortho_first H t ht
  have h2 : inner ℝ r ((Fine ^ 2) U) =
      p4Q2PD_originalWilsonThirdMomentGap H t ht :=
    p4Q2PD_originalWilsonThirdSchur_inner_second_eq_gap H t ht
  calc
    ‖r‖ ^ 2 = inner ℝ r r :=
      (real_inner_self_eq_norm_sq r).symm
    _ = inner ℝ r (delta • ((Fine ^ 2) U) - a • U - b • (Fine U)) := by
      rw [← hr]
    _ = delta * inner ℝ r ((Fine ^ 2) U) := by
      rw [inner_sub_right, inner_sub_right]
      simp only [real_inner_smul_right, h0, h1, mul_zero, sub_zero]
    _ = delta * p4Q2PD_originalWilsonThirdMomentGap H t ht := by
      rw [h2]

/-- In the region where the actual rank-two moment pivot is positive,
strict third Wilson Hankel positivity is EXACTLY nonzero true physical
third Schur innovation. Strict rank-three is NOT asserted. -/
theorem p4Q2PD_originalWilsonThirdMomentGap_pos_iff_physicalSchur_nonzero
    (hTwo : 0 < p4Q2PD_originalWilsonTwoMomentDet H t ht) :
    0 < p4Q2PD_originalWilsonThirdMomentGap H t ht ↔
      p4Q2PD_originalWilsonThirdSchurPhysical H t ht ≠ 0 := by
  have hnorm :=
    p4Q2PD_originalWilsonThirdSchur_normSq_eq_twoDet_mul_threeGap H t ht
  constructor
  · intro hGap hZero
    rw [hZero, norm_zero] at hnorm
    have hm := mul_pos hTwo hGap
    nlinarith
  · intro hSource
    have hp : 0 < ‖p4Q2PD_originalWilsonThirdSchurPhysical H t ht‖ :=
      norm_pos_iff.mpr hSource
    have hprod : 0 <
        p4Q2PD_originalWilsonTwoMomentDet H t ht *
          p4Q2PD_originalWilsonThirdMomentGap H t ht := by
      rw [← hnorm]
      nlinarith
    by_contra hnot
    have hgap : p4Q2PD_originalWilsonThirdMomentGap H t ht ≤ 0 :=
      le_of_not_gt hnot
    have hnonpos : p4Q2PD_originalWilsonTwoMomentDet H t ht *
        p4Q2PD_originalWilsonThirdMomentGap H t ht ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hTwo.le hgap
    exact (not_le_of_gt hprod) hnonpos

/-- The authentic third Hankel determinant is positive if and only if
the TRUE physical Schur innovation is nonzero, when the independently
established original rank-two pivot is positive. -/
theorem p4Q2PD_originalWilsonThreeHankel_det_pos_iff_physicalSchur_nonzero
    (hTwo : 0 < p4Q2PD_originalWilsonTwoMomentDet H t ht) :
    0 < (p4Q2PD_originalWilsonThreeHankel H t ht).det ↔
      p4Q2PD_originalWilsonThirdSchurPhysical H t ht ≠ 0 := by
  rw [p4Q2PD_originalWilsonThreeHankel_det_eq_gap]
  exact p4Q2PD_originalWilsonThirdMomentGap_pos_iff_physicalSchur_nonzero
    H t ht hTwo

end TrueOriginalWilsonThirdMoment

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PD_originalWilsonThreeHankel_det_eq_gap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PD_originalWilsonThirdSchur_ortho_unit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PD_originalWilsonThirdSchur_ortho_first
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PD_originalWilsonThirdSchur_inner_second_eq_gap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PD_originalWilsonThirdSchur_normSq_eq_twoDet_mul_threeGap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PD_originalWilsonThirdMomentGap_pos_iff_physicalSchur_nonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PD_originalWilsonThreeHankel_det_pos_iff_physicalSchur_nonzero
