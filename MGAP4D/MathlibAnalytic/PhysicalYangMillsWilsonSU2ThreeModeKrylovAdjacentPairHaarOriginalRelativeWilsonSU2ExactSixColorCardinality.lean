import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2ActualPhysicalColorGrowth
import Mathlib.Tactic

/-!
# P4-Q2-ES: Exact original Wilson spatial six-color cardinalities

Count the ACTUAL original reflection-fixed time-zero spatial slice, not
a substituted Haar carrier or synthetic graph. Its three spatial coordinates
are periodic modulo n = 2*(H+1). A unit spatial shift gives a bijection
between the two original checkerboard parity fibers. Each spatial direction
and parity is a genuine Wilson boundary six-color.

The target exact count for each physical color is 4*(H+1)^3. This is a
finite-volume geometric identity. Combined with EQ it sharpens the
necessary relative AW/D12 Wilson witness coefficient to 3/(H+1)^3.
No assertion is made about an absolute physical spectral gap or the
continuum four-dimensional Yang-Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

/-- Finite original primary-reflection-plane vertex carrier, installed
explicitly so the subtype's noncomputable decidability is available. -/
private noncomputable instance p4Q2ES_spatialSliceFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := by
  classical
  unfold PeriodicHypercubicEvenSpatialSliceVertex
  infer_instance

/-- An exact equivalence between ACTUAL original primary-reflection-plane
vertices and the three non-time periodic spatial coordinates. -/
private noncomputable def p4Q2ES_spatialVertexEquiv (H : ℕ) :
    PeriodicHypercubicEvenSpatialSliceVertex H ≃
      (PeriodicHypercubicEvenSpatialDirection →
        ZMod (PeriodicHypercubicEvenSideLength H)) where
  toFun v := fun i => v.1 i.1
  invFun f :=
    ⟨fun i => if h : i = 0 then 0 else f ⟨i, h⟩,
      by
        simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    by_cases hi : i = 0
    · subst i
      simpa [periodicHypercubicEvenOnPrimaryReflectionPlane] using v.2.symm
    · simp [hi]
  right_inv f := by
    funext i
    simp [i.2]

/-- The genuine original spatial vertex cardinality is the cube of the
actual even-periodic spatial side length. -/
theorem p4Q2ES_originalSpatialVertex_card (H : ℕ) :
    Fintype.card (PeriodicHypercubicEvenSpatialSliceVertex H) =
      (2 * (H + 1)) ^ 3 := by
  classical
  calc
    Fintype.card (PeriodicHypercubicEvenSpatialSliceVertex H) =
        Fintype.card
          (PeriodicHypercubicEvenSpatialDirection →
            ZMod (PeriodicHypercubicEvenSideLength H)) :=
      Fintype.card_congr (p4Q2ES_spatialVertexEquiv H)
    _ = (2 * (H + 1)) ^ 3 := by
      rw [Fintype.card_fun]
      rw [periodicHypercubicOtherAxis_card]
      simp [PeriodicHypercubicEvenSideLength]

/-- One actual non-temporal spatial axis for a unit color-parity flip. -/
private def p4Q2ES_referenceSpatialDirection :
    PeriodicHypercubicEvenSpatialDirection :=
  ⟨1, by decide⟩

/-- Translation by one physical spatial unit is an actual equivalence
of the original primary-reflection-plane spatial vertex carrier. -/
private noncomputable def p4Q2ES_shiftEquiv (H : ℕ) :
    PeriodicHypercubicEvenSpatialSliceVertex H ≃
      PeriodicHypercubicEvenSpatialSliceVertex H where
  toFun v :=
    periodicHypercubicEvenSpatialSliceShift H v p4Q2ES_referenceSpatialDirection
  invFun v :=
    ⟨periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
        v.1 p4Q2ES_referenceSpatialDirection.1,
      by
        have hAxis :
            (0 : PeriodicHypercubicAxis) ≠ p4Q2ES_referenceSpatialDirection.1 := by decide
        simpa [periodicHypercubicEvenOnPrimaryReflectionPlane,
          periodicHypercubicUnshift, periodicHypercubicUnit, hAxis] using v.2⟩
  left_inv v := by
    apply Subtype.ext
    exact periodicHypercubicUnshift_shift
      (PeriodicHypercubicEvenSideLength H) v.1
      p4Q2ES_referenceSpatialDirection.1
  right_inv v := by
    apply Subtype.ext
    exact periodicHypercubicShift_unshift
      (PeriodicHypercubicEvenSideLength H) v.1
      p4Q2ES_referenceSpatialDirection.1

/-- The REAL spatial unit translation flips original checkerboard parity. -/
private theorem p4Q2ES_shiftEquiv_parity (H : ℕ)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    periodicHypercubicEvenCheckerboardParity H (p4Q2ES_shiftEquiv H v).1 =
      periodicHypercubicEvenCheckerboardParity H v.1 + 1 := by
  change periodicHypercubicEvenCheckerboardParity H
      (periodicHypercubicEvenSpatialSliceShift H v
        p4Q2ES_referenceSpatialDirection).1 =
      periodicHypercubicEvenCheckerboardParity H v.1 + 1
  rw [periodicHypercubicEvenSpatialSliceShift_coe]
  exact periodicHypercubicEvenCheckerboardParity_shift
    H v.1 p4Q2ES_referenceSpatialDirection.1

private abbrev p4Q2ES_parityFiber (H : ℕ) (p : ZMod 2) : Type :=
  {v : PeriodicHypercubicEvenSpatialSliceVertex H //
    periodicHypercubicEvenCheckerboardParity H v.1 = p}

/-- Fintype of the genuine original Wilson spatial checkerboard fiber. -/
private noncomputable instance p4Q2ES_parityFiberFintype (H : ℕ) (p : ZMod 2) :
    Fintype (p4Q2ES_parityFiber H p) := by
  classical
  unfold p4Q2ES_parityFiber
  infer_instance

/-- The spatial unit shift bijects ORIGINAL parity p vertices
with original parity p+1 vertices; no probability law is involved. -/
private noncomputable def p4Q2ES_parityFiberShiftEquiv (H : ℕ) (p : ZMod 2) :
    p4Q2ES_parityFiber H p ≃ p4Q2ES_parityFiber H (p + 1) where
  toFun v :=
    ⟨p4Q2ES_shiftEquiv H v.1, by
      rw [p4Q2ES_shiftEquiv_parity H v.1, v.2]⟩
  invFun v :=
    ⟨(p4Q2ES_shiftEquiv H).symm v.1, by
      have h := p4Q2ES_shiftEquiv_parity H
        ((p4Q2ES_shiftEquiv H).symm v.1)
      rw [Equiv.apply_symm_apply] at h
      have hp :
          periodicHypercubicEvenCheckerboardParity H
              ((p4Q2ES_shiftEquiv H).symm v.1).1 + 1 = p + 1 :=
        h.symm.trans v.2
      exact add_right_cancel hp⟩
  left_inv v := by
    apply Subtype.ext
    exact Equiv.symm_apply_apply (p4Q2ES_shiftEquiv H) v.1
  right_inv v := by
    apply Subtype.ext
    exact Equiv.apply_symm_apply (p4Q2ES_shiftEquiv H) v.1

/-- All ZMod-two checkerboard values are either zero or one. -/
private theorem p4Q2ES_parity_zero_or_one (p : ZMod 2) :
    p = 0 ∨ p = 1 := by
  classical
  fin_cases p <;> norm_num

private theorem p4Q2ES_parity_eq_one_of_ne_zero (p : ZMod 2) (hp : p ≠ 0) :
    p = 1 := by
  rcases p4Q2ES_parity_zero_or_one p with h0 | h1
  · exact (hp h0).elim
  · exact h1

/-- Actual parity-one vertices are the complement of parity-zero
vertices in the ORIGINAL spatial slice. -/
private noncomputable def p4Q2ES_parityOneNotZeroEquiv (H : ℕ) :
    p4Q2ES_parityFiber H 1 ≃
      {v : PeriodicHypercubicEvenSpatialSliceVertex H //
        ¬ periodicHypercubicEvenCheckerboardParity H v.1 = 0} where
  toFun v := ⟨v.1, by
    intro hz
    exact zero_ne_one (hz.symm.trans v.2)⟩
  invFun v := ⟨v.1,
    p4Q2ES_parity_eq_one_of_ne_zero
      (periodicHypercubicEvenCheckerboardParity H v.1) v.2⟩
  left_inv v := by apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; rfl

/-- Each original parity class has exactly four times the cube of
the lattice half-period sites. -/
private theorem p4Q2ES_parityZero_card (H : ℕ) :
    Fintype.card (p4Q2ES_parityFiber H 0) = 4 * (H + 1) ^ 3 := by
  classical
  have h01 :
      Fintype.card (p4Q2ES_parityFiber H 0) =
        Fintype.card (p4Q2ES_parityFiber H 1) := by
    simpa using Fintype.card_congr
      (p4Q2ES_parityFiberShiftEquiv H (0 : ZMod 2))
  have hComplement :
      Fintype.card (p4Q2ES_parityFiber H 1) =
        Fintype.card (PeriodicHypercubicEvenSpatialSliceVertex H) -
          Fintype.card (p4Q2ES_parityFiber H 0) := by
    calc
      Fintype.card (p4Q2ES_parityFiber H 1) =
          Fintype.card
            {v : PeriodicHypercubicEvenSpatialSliceVertex H //
              ¬ periodicHypercubicEvenCheckerboardParity H v.1 = 0} :=
        Fintype.card_congr (p4Q2ES_parityOneNotZeroEquiv H)
      _ = _ := Fintype.card_subtype_compl
        (fun v : PeriodicHypercubicEvenSpatialSliceVertex H =>
          periodicHypercubicEvenCheckerboardParity H v.1 = 0)
  have hSub :
      Fintype.card (p4Q2ES_parityFiber H 0) ≤
        Fintype.card (PeriodicHypercubicEvenSpatialSliceVertex H) :=
    Fintype.card_subtype_le
      (fun v : PeriodicHypercubicEvenSpatialSliceVertex H =>
        periodicHypercubicEvenCheckerboardParity H v.1 = 0)
  have hSum :
      Fintype.card (p4Q2ES_parityFiber H 0) +
        Fintype.card (p4Q2ES_parityFiber H 1) =
          Fintype.card (PeriodicHypercubicEvenSpatialSliceVertex H) := by
    omega
  have hTwice :
      2 * Fintype.card (p4Q2ES_parityFiber H 0) =
        2 * (4 * (H + 1) ^ 3) := by
    calc
      2 * Fintype.card (p4Q2ES_parityFiber H 0) =
          Fintype.card (p4Q2ES_parityFiber H 0) +
            Fintype.card (p4Q2ES_parityFiber H 0) := by omega
      _ = Fintype.card (p4Q2ES_parityFiber H 0) +
          Fintype.card (p4Q2ES_parityFiber H 1) := by rw [h01]
      _ = Fintype.card (PeriodicHypercubicEvenSpatialSliceVertex H) := hSum
      _ = (2 * (H + 1)) ^ 3 := p4Q2ES_originalSpatialVertex_card H
      _ = 2 * (4 * (H + 1) ^ 3) := by ring
  omega

/-- BOTH original checkerboard parity fibers have EXACTLY the same
physical cubic size. -/
theorem p4Q2ES_parityFiber_card (H : ℕ) (p : ZMod 2) :
    Fintype.card (p4Q2ES_parityFiber H p) = 4 * (H + 1) ^ 3 := by
  have h0 := p4Q2ES_parityZero_card H
  have h01 := Fintype.card_congr
    (p4Q2ES_parityFiberShiftEquiv H (0 : ZMod 2))
  fin_cases p
  · simpa using h0
  · simpa [h0] using h01.symm

/-- A TRUE original physical spatial-boundary color c (direction,parity)
has precisely the checkerboard-parity vertex fiber as its link carrier. -/
private noncomputable def p4Q2ES_originalColorLinkEquiv
    (H : ℕ) (c : PeriodicHypercubicEvenSpatialBoundaryColor) :
    PeriodicHypercubicEvenFixedSpatialColorLink H c ≃
      p4Q2ES_parityFiber H c.2 where
  toFun e :=
    ⟨e.1.1, congrArg Prod.snd e.2⟩
  invFun v :=
    ⟨(v.1, c.1), by
      change (c.1, periodicHypercubicEvenCheckerboardParity H v.1.1) = c
      exact Prod.ext rfl v.2⟩
  left_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (congrArg Prod.fst e.2).symm
  right_inv v := by apply Subtype.ext; rfl

/-- The exact link count for EVERY actual original physical six-color class:
one spatial direction and one checkerboard parity. -/
theorem p4Q2ES_actualSixColorLinkCard_exact
    (H : ℕ) (c : Fin 6) :
    Fintype.card (p4Q2BA_ColorLinks H c) =
      4 * (H + 1) ^ 3 := by
  classical
  change Fintype.card
      (PeriodicHypercubicEvenFixedSpatialColorLink H
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)) = _
  calc
    Fintype.card
        (PeriodicHypercubicEvenFixedSpatialColorLink H
          (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)) =
        Fintype.card
          (p4Q2ES_parityFiber H
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c).2) :=
      Fintype.card_congr (p4Q2ES_originalColorLinkEquiv H
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c))
    _ = _ := p4Q2ES_parityFiber_card H _

/-- Exact actual physical selected six-color count for EACH real SU(2)
relative-link witness used in EQ and ER. -/
theorem p4Q2ES_selectedPhysicalColorLinkCard_exact
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e =
      4 * (H + 1) ^ 3 := by
  unfold p4Q2EQ_SU2_selectedPhysicalColorLinkCard
  exact p4Q2ES_actualSixColorLinkCard_exact H _

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2ES_originalSpatialVertex_card
#print axioms MGAP4D.MathlibAnalytic.p4Q2ES_parityFiber_card
#print axioms MGAP4D.MathlibAnalytic.p4Q2ES_actualSixColorLinkCard_exact
#print axioms MGAP4D.MathlibAnalytic.p4Q2ES_selectedPhysicalColorLinkCard_exact
