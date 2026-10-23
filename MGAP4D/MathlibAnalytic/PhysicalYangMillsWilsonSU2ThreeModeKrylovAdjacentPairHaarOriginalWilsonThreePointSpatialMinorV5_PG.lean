import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonThirdMomentSpatialPointWitnessV5_PF
import Mathlib.Tactic

/-!
# P4-Q2-PG — original Wilson three-configuration spatial minor certificate

PF proves that the canonical third Schur residual is represented by
a continuous function ψ on the ACTUAL spatial SU(2) gauge-configuration
space, and that its pointwise nonvanishing is equivalent to D3 > 0
in the already-established D2 > 0 physical interval.

A useful more geometric criterion avoids evaluating the unknown
moment coefficients m3 and m4 at test configurations. For three
ACTUAL spatial boundaries A,B,C, put

  X1(A) = (original normalized one-slab Wilson transfer of U)(A),
  X2(A) = (original normalized two-slab Wilson transfer of U)(A),

  M(A,B,C) =
     (X1(B)-X1(A))*(X2(C)-X2(A))
   - (X1(C)-X1(A))*(X2(B)-X2(A)).

This is the true 3x3 evaluation determinant of 1, X1, X2.
The Schur profile ψ=D2*X2-a-b*X1 satisfies the exact identity

  D2*M(A,B,C) =
     (X1(B)-X1(A))*(ψ(C)-ψ(A))
   - (X1(C)-X1(A))*(ψ(B)-ψ(A)).

Thus any NONZERO original three-configuration minor is a genuine,
fully coefficient-free sufficient witness for D3 > 0, physical
third-rank and the actual two-interacting-posterior signed GI receiver,
under PF's proven D2 > 0 premise.

Crucial OPEN gate: this file does NOT claim to have constructed three
specific boundaries with nonzero M. The exact original Wilson kernel
and the nontrivial small-fine asymptotic needed to construct such a
triple remain under investigation. This is a certified reduction and
not an unconditional third-moment result. No surrogate posterior,
added rank axiom, sorry/admit, Dobrushin or continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PG_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PG_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PG_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PG_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PG_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalSpatialThreePointMinor
variable (H : ℕ) (t : ℝ) (ht : 0 ≤ t)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "F1" =>
  p4Q2PF_originalWilsonOneSlabContinuous H t ht
local notation "F2" =>
  p4Q2PF_originalWilsonTwoSlabContinuous H t ht
local notation "Q" =>
  p4Q2PF_originalWilsonThirdSchurContinuous H t ht
local notation "D2" => p4Q2PD_originalWilsonTwoMomentDet H t ht
local notation "D3" => p4Q2PD_originalWilsonThirdMomentGap H t ht
local notation "m" => p4Q2PB_originalWilsonPhysicalMoment H t ht
local notation "R" => p4Q2PD_originalWilsonThirdSchurPhysical H t ht

/-- Scalar determinant of the ACTUAL Wilson continuous one-/two-slab
outputs at three concrete spatial boundaries. Unlike the Schur
profile, this test itself needs no moments or Gram inverses. -/
noncomputable def p4Q2PG_originalWilsonThreeSpatialPointMinor
    (A B C : Cfg) : ℝ :=
  (F1 B - F1 A) * (F2 C - F2 A) -
    (F1 C - F1 A) * (F2 B - F2 A)

/-- The actual normalized Wilson third physical Schur profile evaluated
at a spatial boundary, with all three original moment coefficients. -/
theorem p4Q2PG_originalThirdSchur_pointValue (A : Cfg) :
    Q A =
      D2 * F2 A - ((m 2) ^ 2 - m 1 * m 3) -
        (m 0 * m 3 - m 1 * m 2) * F1 A := by
  simp [p4Q2PF_originalWilsonThirdSchurContinuous]

/-- Pure algebra identifying an affine-translation-invariant 3-row
Wilson evaluation determinant with its canonical Schur residual. -/
theorem p4Q2PG_originalWilsonThreeSpatialPointMinor_schurIdentity
    (A B C : Cfg) :
    D2 * p4Q2PG_originalWilsonThreeSpatialPointMinor H t ht A B C =
      (F1 B - F1 A) * (Q C - Q A) -
        (F1 C - F1 A) * (Q B - Q A) := by
  have hA := p4Q2PG_originalThirdSchur_pointValue H t ht A
  have hB := p4Q2PG_originalThirdSchur_pointValue H t ht B
  have hC := p4Q2PG_originalThirdSchur_pointValue H t ht C
  rw [hA, hB, hC]
  unfold p4Q2PG_originalWilsonThreeSpatialPointMinor
  ring

/-- A NONZERO genuine three-boundary determinant necessarily produces
some actual spatial SU(2) boundary on which the canonical original
Wilson physical Schur representative is nonzero. -/
theorem p4Q2PG_originalWilsonThreeSpatialPointMinor_ne_implies_pointWitness
    (hTwo : 0 < D2) (A B C : Cfg)
    (hMinor : p4Q2PG_originalWilsonThreeSpatialPointMinor
      H t ht A B C ≠ 0) :
    ∃ X : Cfg, Q X ≠ 0 := by
  by_contra hNo
  have hZero : ∀ X : Cfg, Q X = 0 := by
    intro X
    by_contra hx
    exact hNo ⟨X, hx⟩
  have hIdentity :=
    p4Q2PG_originalWilsonThreeSpatialPointMinor_schurIdentity
      H t ht A B C
  have hProductZero :
      D2 * p4Q2PG_originalWilsonThreeSpatialPointMinor
        H t ht A B C = 0 := by
    simpa [hZero A, hZero B, hZero C] using hIdentity
  exact (mul_ne_zero (ne_of_gt hTwo) hMinor) hProductZero

/-- A fully ORIGINAL geometric 3-point minor, once made nonzero by
concrete Wilson-kernel analysis, certifies strict TRUE physical 3x3
Hankel positivity. Neither the existence of this minor nor D3>0
is postulated. -/
theorem p4Q2PG_originalWilsonThreeSpatialPointMinor_ne_implies_thirdMoment_pos
    (hTwo : 0 < D2) (A B C : Cfg)
    (hMinor : p4Q2PG_originalWilsonThreeSpatialPointMinor
      H t ht A B C ≠ 0) :
    0 < D3 := by
  exact
    (p4Q2PF_originalThirdMoment_pos_iff_exists_trueSpatialPoint
      H t ht hTwo).mpr
      (p4Q2PG_originalWilsonThreeSpatialPointMinor_ne_implies_pointWitness
        H t ht hTwo A B C hMinor)

/-- The very same literal original Wilson 3-point minor forces a
TRUE signed two-interacting-posterior GI response of the SAME exact
Schur physical source, not a replacement Haar-posterior receiver. -/
theorem p4Q2PG_originalWilsonThreeSpatialPointMinor_ne_implies_trueGI
    (hTwo : 0 < D2)
    (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ : Cfg)
    (A B C : Cfg)
    (hMinor : p4Q2PG_originalWilsonThreeSpatialPointMinor
      H t ht A B C ≠ 0) :
    ∃ z : Cfg × Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le R e z ≠ 0 := by
  obtain ⟨X, hX⟩ :=
    p4Q2PG_originalWilsonThreeSpatialPointMinor_ne_implies_pointWitness
      H t ht hTwo A B C hMinor
  exact p4Q2PF_originalThirdSpatialPoint_implies_trueSignedGI
    H t ht b hb e left₀ X hX

end OriginalSpatialThreePointMinor

section ActualSmallPositiveFine
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn

/-- A radius in which EVERY genuine nonzero original Wilson 3-point
evaluation minor implies strict TRUE 3x3 physical Hankel positivity.
The radius is obtained from the already-proven original ON/PE
two-mode pivot: NO third-mode premise is inserted. The concrete
construction of a nonzero 3-point minor is still OPEN. -/
theorem p4Q2PG_actualSmallFine_threePointMinor_implies_thirdMoment_pos
    (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        ∀ A B C : Cfg,
          p4Q2PG_originalWilsonThreeSpatialPointMinor
            Hn (beta (n + 1)) (hbeta (n + 1)) A B C ≠ 0 →
          0 < p4Q2PD_originalWilsonThirdMomentGap
            Hn (beta (n + 1)) (hbeta (n + 1))) := by
  obtain ⟨delta, hdelta, hTwo⟩ :=
    p4Q2PE_actualSmallFine_trueMomentPivot_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall A B C hMinor
  exact p4Q2PG_originalWilsonThreeSpatialPointMinor_ne_implies_thirdMoment_pos
    Hn (beta (n + 1)) (hbeta (n + 1))
    (hTwo ht hsmall) A B C hMinor

end ActualSmallPositiveFine

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PG_originalThirdSchur_pointValue
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PG_originalWilsonThreeSpatialPointMinor_schurIdentity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PG_originalWilsonThreeSpatialPointMinor_ne_implies_pointWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PG_originalWilsonThreeSpatialPointMinor_ne_implies_thirdMoment_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PG_originalWilsonThreeSpatialPointMinor_ne_implies_trueGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PG_actualSmallFine_threePointMinor_implies_thirdMoment_pos
