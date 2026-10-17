import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2Transfer
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteWilsonClassFunction
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectorySpecialUnitaryTwoStapleOscillationSeparationBCF
import Mathlib.Tactic

/-!
# P4-Q2-IY: genuine spatial SU(2) Wilson action is not constant

Use the physical canonical primary spatial plaquette. Its four oriented
physical edges are genuinely distinct on every even periodic lattice,
including the smallest side length 2.  Compare the all-identity spatial
configuration with a physical full-link configuration twisted by the
actual SU(2) center element -I on the first primary plaquette edge.
The primary spatial plaquette has Wilson energy exactly 2 after the
twist while every plaquette term has nonnegative Wilson energy.

The result concerns the original spatial plaquette action that enters the
one-slab Wilson kernel, not an independent model or a synthetic measure.
The separate exact derivative and Haar invariance results will be used to
lift this witness to small-positive-beta nonconstancy in a later stage.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3100000

namespace GroundStatePosteriorJoint

/-- The canonical primary spatial plaquette expressed in the actual intrinsic
spatial-slice plaquette carrier, using the physical (axes 1,2) square. -/
noncomputable def p4Q2IY_primarySpatialSlicePlaquette (H : ℕ) :
    PeriodicHypercubicEvenSpatialSlicePlaquette H :=
  (⟨0, by simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(⟨1, by decide⟩, ⟨2, by decide⟩), by decide⟩)

/-- This intrinsic square is literally the existing 4D primary spatial square
after the canonical spatial embedding. -/
theorem p4Q2IY_primarySpatialSlicePlaquette_embedding (H : ℕ) :
    periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H
      (p4Q2IY_primarySpatialSlicePlaquette H) =
        periodicHypercubicEvenPrimarySpatialPlaquette H := by
  rfl

/-- Change one actual physical 4D link of the canonical primary plaquette
from identity to the genuine rank-two center element -I. -/
noncomputable def p4Q2IY_onePrimaryLinkCentralTwist (H : ℕ) :
    PeriodicHypercubicEvenEdge H → SpecialUnitaryMatrixGroup 2 :=
  Function.update
    (fun _ => (1 : SpecialUnitaryMatrixGroup 2))
    (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 0)
    specialUnitaryTwoNegativeIdentity

@[simp] theorem p4Q2IY_onePrimaryLinkCentralTwist_zero (H : ℕ) :
    p4Q2IY_onePrimaryLinkCentralTwist H
      (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 0) =
        specialUnitaryTwoNegativeIdentity := by
  simp [p4Q2IY_onePrimaryLinkCentralTwist]

/-- No other physical edge of the same actual plaquette is changed; the
original geometric four-edge injectivity excludes periodic collisions. -/
theorem p4Q2IY_onePrimaryLinkCentralTwist_other
    (H : ℕ) (k : Fin 4) (hk : k ≠ 0) :
    p4Q2IY_onePrimaryLinkCentralTwist H
      (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k) = 1 := by
  have hne :
      periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k ≠
        periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 0 :=
    (periodicHypercubicEvenPrimarySpatialPlaquetteEdge_injective H).ne hk
  simp [p4Q2IY_onePrimaryLinkCentralTwist, hne]

/-- The complete physical plaquette word is exactly -I after changing only
its first oriented edge, since all remaining three edges are identity. -/
theorem p4Q2IY_primaryFullPlaquetteHolonomy_twist_eq_center (H : ℕ) :
    periodicHypercubicPlaquetteHolonomy
      (p4Q2IY_onePrimaryLinkCentralTwist H)
      (periodicHypercubicEvenPrimarySpatialPlaquette H) =
        specialUnitaryTwoNegativeIdentity := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteHolonomy_eq_orientedFourEdge]
  change
    p4Q2IY_onePrimaryLinkCentralTwist H
        (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 0) *
      p4Q2IY_onePrimaryLinkCentralTwist H
        (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 1) *
      (p4Q2IY_onePrimaryLinkCentralTwist H
        (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 2))⁻¹ *
      (p4Q2IY_onePrimaryLinkCentralTwist H
        (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 3))⁻¹ =
          specialUnitaryTwoNegativeIdentity
  rw [p4Q2IY_onePrimaryLinkCentralTwist_zero,
    p4Q2IY_onePrimaryLinkCentralTwist_other H 1 (by decide),
    p4Q2IY_onePrimaryLinkCentralTwist_other H 2 (by decide),
    p4Q2IY_onePrimaryLinkCentralTwist_other H 3 (by decide)]
  simp

/-- The genuine intrinsic spatial-slice plaquette carries precisely the same
nontrivial SU(2) holonomy as the corresponding full 4D link field. -/
theorem p4Q2IY_primarySpatialPlaquetteHolonomy_twist_eq_center (H : ℕ) :
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
      (periodicHypercubicEvenSpatialSliceRestriction
        (p4Q2IY_onePrimaryLinkCentralTwist H))
      (p4Q2IY_primarySpatialSlicePlaquette H) =
        specialUnitaryTwoNegativeIdentity := by
  rw [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_restriction_eq]
  rw [p4Q2IY_primarySpatialSlicePlaquette_embedding]
  exact p4Q2IY_primaryFullPlaquetteHolonomy_twist_eq_center H

/-- The untouched actual all-identity SU(2) spatial configuration has
exactly zero total physical Wilson plaquette action. -/
theorem p4Q2IY_allOneSpatialWilsonAction_zero (H : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
      (fun _ => (1 : SpecialUnitaryMatrixGroup 2)) = 0 := by
  simp [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction,
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy,
    specialUnitaryWilsonPlaquetteEnergy_two_one]

/-- The twisted genuine spatial configuration has Wilson action at least 2,
because the primary square has energy 2 and every other square contributes a
nonnegative original Wilson plaquette energy. -/
theorem p4Q2IY_actualSpatialWilsonAction_twist_ge_two (H : ℕ) :
    (2 : ℝ) ≤
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
        (periodicHypercubicEvenSpatialSliceRestriction
          (p4Q2IY_onePrimaryLinkCentralTwist H)) := by
  classical
  let B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 :=
    periodicHypercubicEvenSpatialSliceRestriction
      (p4Q2IY_onePrimaryLinkCentralTwist H)
  let p : PeriodicHypercubicEvenSpatialSlicePlaquette H :=
    p4Q2IY_primarySpatialSlicePlaquette H
  let E : PeriodicHypercubicEvenSpatialSlicePlaquette H → ℝ :=
    fun q => specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B q)
  have hprimary : E p = 2 := by
    dsimp [E, B, p]
    rw [p4Q2IY_primarySpatialPlaquetteHolonomy_twist_eq_center]
    exact specialUnitaryWilsonPlaquetteEnergy_two_negativeIdentity
  have hnonneg (q : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
      0 ≤ E q :=
    specialUnitaryWilsonPlaquetteEnergy_nonneg (by decide) _
  have hle : E p ≤ ∑ q : PeriodicHypercubicEvenSpatialSlicePlaquette H, E q :=
    Finset.single_le_sum (by simp [hnonneg]) (Finset.mem_univ p)
  have hAction :
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 B =
        ∑ q : PeriodicHypercubicEvenSpatialSlicePlaquette H, E q := by
    simp [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction,
      periodicHypercubicEvenSpatialSlicePlaquetteList, E]
  rw [← hAction] at hle
  exact (hprimary.symm ▸ hle)

/-- Two literal physical SU(2) spatial right boundaries have different
original Wilson action at EVERY finite even-periodic spatial volume. -/
theorem p4Q2IY_originalSpatialWilsonAction_not_constant (H : ℕ) :
    ∃ B₀ B₁ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 B₀ ≠
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 B₁ := by
  refine ⟨(fun _ => 1),
    periodicHypercubicEvenSpatialSliceRestriction
      (p4Q2IY_onePrimaryLinkCentralTwist H), ?_⟩
  rw [p4Q2IY_allOneSpatialWilsonAction_zero]
  have h := p4Q2IY_actualSpatialWilsonAction_twist_ge_two H
  intro hEq
  rw [← hEq] at h
  norm_num at h

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IY_primarySpatialSlicePlaquette_embedding
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IY_primaryFullPlaquetteHolonomy_twist_eq_center
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IY_primarySpatialPlaquetteHolonomy_twist_eq_center
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IY_allOneSpatialWilsonAction_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IY_actualSpatialWilsonAction_twist_ge_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IY_originalSpatialWilsonAction_not_constant
