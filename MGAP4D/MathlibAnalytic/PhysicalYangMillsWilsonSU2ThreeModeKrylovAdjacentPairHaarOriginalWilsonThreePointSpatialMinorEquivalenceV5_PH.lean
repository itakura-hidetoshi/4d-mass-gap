import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonThreePointSpatialMinorV5_PG
import Mathlib.Tactic

/-!
# P4-Q2-PH — genuine three-spatial-point Wilson minor iff third Hankel gap

PG gives a sufficient ORIGINAL SU(2) Wilson spatial three-point minor
criterion for the true third Schur physical source. This file closes
the CONVERSE as well, on the already-proved D2 > 0 gate.

The key input is not an assumed rank-3 witness. Under D2 > 0,
the continuous physical one-slab Wilson profile cannot be constant.
If every three-point determinant of (1, phi1, phi2) vanished,
choose two distinct phi1 values and solve the elementary affine
interpolation equation: phi2 = a + b*phi1 pointwise.

PF transports this equality to the unchanged Gauss-law physical
Haar-L2 operator. PD's two exact Schur orthogonalities show that
an affine two-slab physical vector has D3 = 0. Contraposition yields
the existence of three actual spatial configurations with nonzero
PG minor whenever D3 > 0.

Thus in the TRUE PC/PE two-mode interval:
  D3 > 0  <->  EXISTS three ACTUAL spatial SU(2) configurations
                 with original Wilson three-point minor != 0.

This is a necessary-and-sufficient spatial test, NOT construction of
such a triple or proof of D3 > 0. No Wilson kernel replacement,
auxiliary spectral measure, added independence axiom, Dobrushin,
sorry/admit, U0, H1-C3 or continuum Yang-Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PH_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PH_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PH_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PH_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PH_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalThreePointSpatialEquivalence
variable (H : ℕ) (t : ℝ) (ht : 0 ≤ t)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive t ht
local notation "m" => p4Q2PB_originalWilsonPhysicalMoment H t ht
local notation "D2" => p4Q2PD_originalWilsonTwoMomentDet H t ht
local notation "D3" => p4Q2PD_originalWilsonThirdMomentGap H t ht
local notation "R" => p4Q2PD_originalWilsonThirdSchurPhysical H t ht
local notation "F1" => p4Q2PF_originalWilsonOneSlabContinuous H t ht
local notation "F2" => p4Q2PF_originalWilsonTwoSlabContinuous H t ht
local notation "L" => ContinuousMap.toLp 2 haar ℝ

/-- The genuine strict two-moment pivot implies that the ACTUAL
one-slab normalized Wilson output has two different spatial values.
The argument uses the original inner product, not an assumed
three-point rank. -/
theorem p4Q2PH_originalTwoMoment_pos_implies_distinct_oneSlab_points
    (hTwo : 0 < D2) :
    ∃ A B : Cfg, F1 B ≠ F1 A := by
  by_contra hNo
  push Not at hNo
  let A0 : Cfg := fun _ => 1
  let c : ℝ := F1 A0
  have hConstant : F1 = c • (1 : C(Cfg, ℝ)) := by
    ext A
    have hAt : F1 A = F1 A0 := hNo A0 A
    simpa [c] using hAt
  have hL2 :
      ((Fine U : Phys) : Lp ℝ 2 haar) =
        c • ((U : Phys) : Lp ℝ 2 haar) := by
    calc
      ((Fine U : Phys) : Lp ℝ 2 haar) = L F1 :=
        p4Q2PF_originalOneSlabContinuous_toLp H t ht
      _ = L (c • (1 : C(Cfg, ℝ))) := by rw [hConstant]
      _ = c • L (1 : C(Cfg, ℝ)) := by rw [map_smul]
      _ = c • ((U : Phys) : Lp ℝ 2 haar) := by
        rw [← p4Q2JU_originalPhysicalUnit_coe_eq_toLp H]
  have hFine : Fine U = c • U := by
    apply Subtype.ext
    simpa using hL2
  have h00 : inner ℝ U U = m 0 := by
    simpa using p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment H t ht 0 0
  have h01 : inner ℝ U (Fine U) = m 1 := by
    simpa using p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment H t ht 0 1
  have h11 : inner ℝ (Fine U) (Fine U) = m 2 := by
    simpa using p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment H t ht 1 1
  have hm1 : m 1 = c * m 0 := by
    calc
      m 1 = inner ℝ U (Fine U) := h01.symm
      _ = c * inner ℝ U U := by
        rw [hFine]
        simp only [real_inner_smul_right]
      _ = c * m 0 := by rw [h00]
  have hm2 : m 2 = c * m 1 := by
    calc
      m 2 = inner ℝ (Fine U) (Fine U) := h11.symm
      _ = inner ℝ (c • U) (Fine U) := by rw [hFine]
      _ = c * inner ℝ U (Fine U) := by
        simp only [real_inner_smul_left]
      _ = c * m 1 := by rw [h01]
  have hZero : D2 = 0 := by
    dsimp [p4Q2PD_originalWilsonTwoMomentDet]
    rw [hm2, hm1]
    ring
  exact (ne_of_gt hTwo) hZero

/-- If the genuinely normalized two-slab Wilson boundary profile is
affine in the true one-slab profile, the physical third Hankel gap
vanishes. The ORIGINAL physical L2 and both PD orthogonalities
are used. No D2>0 premise is needed for this direction. -/
theorem p4Q2PH_originalTwoSlab_affine_implies_thirdMoment_zero
    (a b : ℝ)
    (hAffine : ∀ A : Cfg, F2 A = a + b * F1 A) :
    D3 = 0 := by
  have hContinuous : F2 = a • (1 : C(Cfg, ℝ)) + b • F1 := by
    ext A
    simpa using hAffine A
  have hLp :
      (((Fine ^ 2) U : Phys) : Lp ℝ 2 haar) =
        a • ((U : Phys) : Lp ℝ 2 haar) +
          b • ((Fine U : Phys) : Lp ℝ 2 haar) := by
    calc
      (((Fine ^ 2) U : Phys) : Lp ℝ 2 haar) = L F2 :=
        p4Q2PF_originalTwoSlabContinuous_toLp H t ht
      _ = L (a • (1 : C(Cfg, ℝ)) + b • F1) := by rw [hContinuous]
      _ = a • L (1 : C(Cfg, ℝ)) + b • L F1 := by
        simp only [map_add, map_smul]
      _ = a • ((U : Phys) : Lp ℝ 2 haar) +
          b • ((Fine U : Phys) : Lp ℝ 2 haar) := by
            rw [← p4Q2JU_originalPhysicalUnit_coe_eq_toLp H,
              ← p4Q2PF_originalOneSlabContinuous_toLp H t ht]
  have hPhys : (Fine ^ 2) U = a • U + b • (Fine U) := by
    apply Subtype.ext
    simpa using hLp
  calc
    D3 = inner ℝ R ((Fine ^ 2) U) :=
      (p4Q2PD_originalWilsonThirdSchur_inner_second_eq_gap H t ht).symm
    _ = inner ℝ R (a • U + b • (Fine U)) := by rw [hPhys]
    _ = a * inner ℝ R U + b * inner ℝ R (Fine U) := by
      calc
        inner ℝ R (a • U + b • (Fine U)) =
            inner ℝ R (a • U) + inner ℝ R (b • (Fine U)) :=
          inner_add_right _ _ _
        _ = a * inner ℝ R U + b * inner ℝ R (Fine U) := by
          simp only [real_inner_smul_right]
    _ = 0 := by
      rw [p4Q2PD_originalWilsonThirdSchur_ortho_unit,
          p4Q2PD_originalWilsonThirdSchur_ortho_first]
      ring

/-- Algebraic affine-interpolation converse: once two original Wilson
one-slab values differ, vanishing of ALL genuine PG three-point
minors makes the actual two-slab profile an affine function of the
first profile on the ENTIRE spatial configuration space. -/
theorem p4Q2PH_allThreePointMinors_zero_implies_twoSlab_affine
    (A B : Cfg) (hPair : F1 B ≠ F1 A)
    (hAll : ∀ C : Cfg,
      p4Q2PG_originalWilsonThreeSpatialPointMinor H t ht A B C = 0) :
    ∃ a b : ℝ, ∀ C : Cfg, F2 C = a + b * F1 C := by
  let dx : ℝ := F1 B - F1 A
  let dy : ℝ := F2 B - F2 A
  have hdx : dx ≠ 0 := sub_ne_zero.mpr hPair
  let b : ℝ := dy / dx
  have hb : dx * b = dy := by
    dsimp [b]
    field_simp [hdx]
  refine ⟨F2 A - b * F1 A, b, ?_⟩
  intro C
  have hZero := hAll C
  unfold p4Q2PG_originalWilsonThreeSpatialPointMinor at hZero
  have hEquality :
      dx * (F2 C - F2 A) = (F1 C - F1 A) * dy := by
    dsimp [dx, dy]
    linarith
  have hCancel :
      dx * (F2 C - F2 A) =
        dx * (b * (F1 C - F1 A)) := by
    calc
      _ = (F1 C - F1 A) * dy := hEquality
      _ = (F1 C - F1 A) * (dx * b) := by rw [hb]
      _ = dx * (b * (F1 C - F1 A)) := by ring
  have hDifference : F2 C - F2 A = b * (F1 C - F1 A) :=
    mul_left_cancel₀ hdx hCancel
  calc
    F2 C = F2 A + (F2 C - F2 A) := by ring
    _ = F2 A + b * (F1 C - F1 A) := by rw [hDifference]
    _ = (F2 A - b * F1 A) + b * F1 C := by ring

/-- Main PH theorem: in the genuine Wilson physical D2>0 regime,
strict positivity of the TRUE third Hankel determinant is EQUIVALENT
to a nonzero three-configuration evaluation determinant of the
unchanged normalized one- and two-slab Wilson continuous outputs. -/
theorem p4Q2PH_originalThirdMoment_pos_iff_exists_threeSpatialMinor
    (hTwo : 0 < D2) :
    0 < D3 ↔
      ∃ A B C : Cfg,
        p4Q2PG_originalWilsonThreeSpatialPointMinor H t ht A B C ≠ 0 := by
  constructor
  · intro hD3
    obtain ⟨A, B, hPair⟩ :=
      p4Q2PH_originalTwoMoment_pos_implies_distinct_oneSlab_points H t ht hTwo
    by_contra hNo
    push Not at hNo
    obtain ⟨a, b, hAffine⟩ :=
      p4Q2PH_allThreePointMinors_zero_implies_twoSlab_affine
        H t ht A B hPair (fun C => hNo A B C)
    have hZero :=
      p4Q2PH_originalTwoSlab_affine_implies_thirdMoment_zero
        H t ht a b hAffine
    exact (ne_of_gt hD3) hZero
  · rintro ⟨A, B, C, hMinor⟩
    exact p4Q2PG_originalWilsonThreeSpatialPointMinor_ne_implies_thirdMoment_pos
      H t ht hTwo A B C hMinor

end OriginalThreePointSpatialEquivalence

section SmallFineThreePointEquivalence
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn

/-- The original ON/PC/PE small-fine interval is a common interval
of precise equivalence between strict physical 3x3 Hankel positivity
and the existence of a NONZERO original Wilson three-point minor.
The existence itself is not assumed or proved. -/
theorem p4Q2PH_actualSmallFine_thirdMoment_pos_iff_exists_threeSpatialMinor
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        (0 < p4Q2PD_originalWilsonThirdMomentGap
            Hn (beta (n + 1)) (hbeta (n + 1)) ↔
          ∃ A B C : Cfg,
            p4Q2PG_originalWilsonThreeSpatialPointMinor
              Hn (beta (n + 1)) (hbeta (n + 1)) A B C ≠ 0)) := by
  obtain ⟨delta, hdelta, hTwo⟩ :=
    p4Q2PE_actualSmallFine_trueMomentPivot_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall
  exact p4Q2PH_originalThirdMoment_pos_iff_exists_threeSpatialMinor
    Hn (beta (n + 1)) (hbeta (n + 1)) (hTwo ht hsmall)

end SmallFineThreePointEquivalence

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PH_originalTwoMoment_pos_implies_distinct_oneSlab_points
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PH_originalTwoSlab_affine_implies_thirdMoment_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PH_allThreePointMinors_zero_implies_twoSlab_affine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PH_originalThirdMoment_pos_iff_exists_threeSpatialMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PH_actualSmallFine_thirdMoment_pos_iff_exists_threeSpatialMinor
