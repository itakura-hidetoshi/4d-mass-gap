import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2BCFPhysicalL2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSplitUpdateMeanIdentification
import Mathlib.Tactic

/-!
# P4-Q2-EF: true two-coordinate support of the gauge-invariant SU(2) relative link

EE constructed a concrete gauge-invariant BCF `F_e(A,B)` on the actual two
spatial boundaries, its TRUE original physical Wilson joint L² class and
its distinct independent pair-Haar L² class. The relative-link observable
depends on the pair of genuine joint spatial coordinates
    Sum.inl e (left boundary), Sum.inr e (right boundary).

Here the actual canonical pair-coordinate measurable equivalence is used
to prove a pointwise invariance when ANY OTHER left/right link coordinate
is replaced by arbitrary SU(2) group element. The literal ACTUAL one-link
Haar coordinate mean CU therefore fixes the concrete EE witness.

The established DA identity between that literal independent pair-Haar
coordinate mean and the ACTUAL CR L² orthogonal projection then gives:
    P_i f_e = f_e
    ||f_e - P_i f_e||² = 0
for every genuine i distinct from BOTH Sum.inl e and Sum.inr e.

This is a REAL support certificate on the original left/right spatial
pair-Haar L² carrier. It does NOT prove that either selected coordinate
defect is nonzero; it does NOT assert this independence for the distinct
interacting Wilson conditional expectations, or prove an original Wilson
mass-weighted Haar reference energy identity or uniform mass gap.
No new probability measure, no sorry/admit/axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

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

section ActualPairHaarLocalSupport

variable (H : ℕ)
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Joint" => Cfg × Cfg
local notation "I" => PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "E" =>
  periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv H 2
local notation "F" => p4Q2EE_SU2_relativeWilsonEnergyBCF H
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H 2
local notation "f" => p4Q2EE_SU2_pairHaarJointL2 H

/-- Replacing any ACTUAL pair-coordinate other than the left and right
copies of e changes neither of the TWO relative-link variables.
This is an identity on the original physical pair configurations. -/
theorem p4Q2EF_SU2_relativeWilsonEnergy_otherCoordinate_update_eq
    (e : Link) (i : I)
    (hL : i ≠ Sum.inl e) (hR : i ≠ Sum.inr e)
    (z : Joint) (u : G) :
    F e (E.symm (Function.update (E z) i u)) = F e z := by
  classical
  let z' : Joint := E.symm (Function.update (E z) i u)
  have hApply : E z' = Function.update (E z) i u := by
    exact E.apply_symm_apply _
  have hCL :
      (Function.update (E z) i u) (Sum.inl e) =
        (E z) (Sum.inl e) := by
    simp [Function.update, hL, Ne.symm hL]
  have hCR :
      (Function.update (E z) i u) (Sum.inr e) =
        (E z) (Sum.inr e) := by
    simp [Function.update, hR, Ne.symm hR]
  have hLeft : z'.1 e = z.1 e := by
    have hc : (E z') (Sum.inl e) = (E z) (Sum.inl e) := by
      rw [hApply]
      exact hCL
    simpa only [
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_apply_inl
    ] using hc
  have hRight : z'.2 e = z.2 e := by
    have hc : (E z') (Sum.inr e) = (E z) (Sum.inr e) := by
      rw [hApply]
      exact hCR
    simpa only [
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_apply_inr
    ] using hc
  change F e z' = F e z
  rw [p4Q2EE_SU2_relativeWilsonEnergyBCF_apply,
    p4Q2EE_SU2_relativeWilsonEnergyBCF_apply, hLeft, hRight]

/-- The LITERAL one-link Haar coordinate mean (not an assumed Wilson
conditional expectation) fixes the actual bounded concrete SU(2)
relative-link observable for every off-support left/right coordinate. -/
theorem p4Q2EF_SU2_relativeWilsonEnergy_otherCoordinate_HaarMean_eq
    (e : Link) (i : I)
    (hL : i ≠ Sum.inl e) (hR : i ≠ Sum.inr e) (z : Joint) :
    p4Q2CU_actualPairHaarCoordinateMean H 2 i
      (fun w : Joint => F e w) z = F e z := by
  classical
  change (∫ u : G, F e (E.symm (Function.update (E z) i u))
      ∂normalizedCompactHaar G) = F e z
  have hInt :
      (fun u : G => F e (E.symm (Function.update (E z) i u))) =
      (fun _ : G => F e z) := by
    funext u
    exact p4Q2EF_SU2_relativeWilsonEnergy_otherCoordinate_update_eq
      H e i hL hR z u
  rw [hInt]
  simp

/-- On the ACTUAL INDEPENDENT pair-Haar real L² quotient, the original
CR off-coordinate orthogonal projection fixes the genuine EE
two-boundary relative-link SU(2) Wilson-energy class whenever its
coordinate is neither of the two copies of the selected physical link. -/
theorem p4Q2EF_SU2_relativeWilsonEnergy_otherCoordinate_projection_fixed
    (e : Link) (i : I)
    (hL : i ≠ Sum.inl e) (hR : i ≠ Sum.inr e) :
    P i (f e) = f e := by
  let F' : Joint → ℝ := fun z => F e z
  have hStrong : StronglyMeasurable F' :=
    (F e).continuous.stronglyMeasurable
  have hBound : ∀ z : Joint, ‖F' z‖ ≤ (2 : ℝ) := by
    intro z
    have hz := p4Q2EE_SU2_relativeWilsonEnergyBCF_mem_Icc H e z
    have hAbs : |F e z| ≤ (2 : ℝ) :=
      abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
    simpa [F', Real.norm_eq_abs] using hAbs
  have hAE :
      F' =ᵐ[muPair] ((f e : Lp ℝ 2 muPair) : Joint → ℝ) :=
    (p4Q2EE_SU2_pairHaarJointL2_ae_eq H e).symm
  have hProject :=
    p4Q2DA_actualPairHaarProjection_ae_eq_CUmean
      H 2 i (f e) F' hStrong 2 hBound hAE
  apply Lp.ext
  exact hProject.trans
    ((Filter.Eventually.of_forall
      (p4Q2EF_SU2_relativeWilsonEnergy_otherCoordinate_HaarMean_eq
        H e i hL hR)).trans hAE)

/-- The exact squared L² coordinate residual is ZERO on every
genuine pair-Haar coordinate other than Sum.inl e / Sum.inr e.
No statement is made about the two selected defect sizes. -/
theorem p4Q2EF_SU2_relativeWilsonEnergy_otherCoordinate_defect_sq_zero
    (e : Link) (i : I)
    (hL : i ≠ Sum.inl e) (hR : i ≠ Sum.inr e) :
    ‖f e - P i (f e)‖ ^ 2 = (0 : ℝ) := by
  rw [p4Q2EF_SU2_relativeWilsonEnergy_otherCoordinate_projection_fixed
    H e i hL hR]
  simp

end ActualPairHaarLocalSupport
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EF_SU2_relativeWilsonEnergy_otherCoordinate_update_eq
#print axioms MGAP4D.MathlibAnalytic.p4Q2EF_SU2_relativeWilsonEnergy_otherCoordinate_HaarMean_eq
#print axioms MGAP4D.MathlibAnalytic.p4Q2EF_SU2_relativeWilsonEnergy_otherCoordinate_projection_fixed
#print axioms MGAP4D.MathlibAnalytic.p4Q2EF_SU2_relativeWilsonEnergy_otherCoordinate_defect_sq_zero
