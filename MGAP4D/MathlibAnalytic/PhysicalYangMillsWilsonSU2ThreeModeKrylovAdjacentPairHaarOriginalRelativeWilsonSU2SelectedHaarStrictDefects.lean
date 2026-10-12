import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2TwoCoordinateHaarReference
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergyInversion
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-!
# P4-Q2-EH: selected SU(2) pair-Haar coordinate means

The original SU(2) gauge-invariant relative-link BCF from EE has exactly
two potentially nonzero pair-Haar coordinate defects (EF, EG).
We compute their literal selected-coordinate normalized Haar means using
the genuine SU(2) Haar invariance and Wilson-energy inversion symmetry.
This file never identifies pair-Haar CR projections with interacting
Wilson conditional expectations and does not claim a uniform mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section
set_option maxHeartbeats 1900000
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

section ActualHaar

variable (H : ℕ)
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Joint" => Cfg × Cfg
local notation "muH" => normalizedCompactHaar G
local notation "muPair" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "E" => periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv H 2
local notation "F" => p4Q2EE_SU2_relativeWilsonEnergyBCF H
local notation "f" => p4Q2EE_SU2_pairHaarJointL2 H
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H 2

local instance p4Q2EH_leftInvariant :
    Measure.IsMulLeftInvariant muH := by
  dsimp [normalizedCompactHaar]
  infer_instance

noncomputable def p4Q2EH_groupWilsonHaarMean : ℝ :=
  ∫ u : G, specialUnitaryWilsonPlaquetteEnergy 2 u ∂muH

/-- Actual RIGHT-coordinate update retains the genuine left-link value. -/
theorem p4Q2EH_rightUpdate (e : Link) (z : Joint) (u : G) :
    F e (E.symm (Function.update (E z) (Sum.inr e) u)) =
      specialUnitaryWilsonPlaquetteEnergy 2 ((z.1 e)⁻¹ * u) := by
  classical
  let z' : Joint := E.symm (Function.update (E z) (Sum.inr e) u)
  have hE : E z' = Function.update (E z) (Sum.inr e) u := E.apply_symm_apply _
  have hLeft : z'.1 e = z.1 e := by
    have hc : (E z') (Sum.inl e) = (E z) (Sum.inl e) := by
      rw [hE]
      simp [Function.update]
    simpa only [
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_apply_inl
    ] using hc
  have hRight : z'.2 e = u := by
    have hc : (E z') (Sum.inr e) = u := by
      rw [hE]
      simp
    simpa only [
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_apply_inr
    ] using hc
  change F e z' = _
  rw [p4Q2EE_SU2_relativeWilsonEnergyBCF_apply, hLeft, hRight]

/-- Actual LEFT-coordinate update retains the genuine right-link value. -/
theorem p4Q2EH_leftUpdate (e : Link) (z : Joint) (u : G) :
    F e (E.symm (Function.update (E z) (Sum.inl e) u)) =
      specialUnitaryWilsonPlaquetteEnergy 2 (u⁻¹ * z.2 e) := by
  classical
  let z' : Joint := E.symm (Function.update (E z) (Sum.inl e) u)
  have hE : E z' = Function.update (E z) (Sum.inl e) u := E.apply_symm_apply _
  have hLeft : z'.1 e = u := by
    have hc : (E z') (Sum.inl e) = u := by
      rw [hE]
      simp
    simpa only [
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_apply_inl
    ] using hc
  have hRight : z'.2 e = z.2 e := by
    have hc : (E z') (Sum.inr e) = (E z) (Sum.inr e) := by
      rw [hE]
      simp [Function.update]
    simpa only [
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_apply_inr
    ] using hc
  change F e z' = _
  rw [p4Q2EE_SU2_relativeWilsonEnergyBCF_apply, hLeft, hRight]


/-- Genuine SU(2) normalized Haar invariance makes the selected RIGHT
coordinate mean independent of every original pair-Haar background. -/
theorem p4Q2EH_rightSelectedMean_eq_groupMean (e : Link) (z : Joint) :
    p4Q2CU_actualPairHaarCoordinateMean H 2 (Sum.inr e)
        (fun w : Joint => F e w) z =
      p4Q2EH_groupWilsonHaarMean H := by
  change (∫ u : G, F e (E.symm (Function.update (E z) (Sum.inr e) u))
      ∂muH) = _
  have hEq :
      (fun u : G => F e (E.symm (Function.update (E z) (Sum.inr e) u))) =
        (fun u : G => specialUnitaryWilsonPlaquetteEnergy 2 ((z.1 e)⁻¹ * u)) := by
    funext u
    exact p4Q2EH_rightUpdate H e z u
  rw [hEq]
  exact integral_mul_left_eq_self
    (fun g : G => specialUnitaryWilsonPlaquetteEnergy 2 g) ((z.1 e)⁻¹)

/-- Genuine SU(2) Wilson energy is inversion invariant. The LEFT Haar
coordinate mean is the same fixed normalized SU(2) group mean. -/
theorem p4Q2EH_leftSelectedMean_eq_groupMean (e : Link) (z : Joint) :
    p4Q2CU_actualPairHaarCoordinateMean H 2 (Sum.inl e)
        (fun w : Joint => F e w) z =
      p4Q2EH_groupWilsonHaarMean H := by
  change (∫ u : G, F e (E.symm (Function.update (E z) (Sum.inl e) u))
      ∂muH) = _
  have hEq :
      (fun u : G => F e (E.symm (Function.update (E z) (Sum.inl e) u))) =
        (fun u : G => specialUnitaryWilsonPlaquetteEnergy 2 ((z.2 e)⁻¹ * u)) := by
    funext u
    rw [p4Q2EH_leftUpdate H e z u]
    have hInv := specialUnitaryWilsonPlaquetteEnergy_inv (u⁻¹ * z.2 e)
    simpa only [mul_inv_rev, inv_inv] using hInv.symm
  rw [hEq]
  exact integral_mul_left_eq_self
    (fun g : G => specialUnitaryWilsonPlaquetteEnergy 2 g) ((z.2 e)⁻¹)

/-- Actual independent pair-Haar selected RIGHT CR orthogonal projection
has the exact constant representative equal to the true Haar mean. -/
theorem p4Q2EH_rightSelectedProjection_ae_groupMean (e : Link) :
    (((P (Sum.inr e) (f e) : Lp ℝ 2 muPair) : Joint → ℝ)) =ᵐ[muPair]
      fun _ => p4Q2EH_groupWilsonHaarMean H := by
  have hStrong : StronglyMeasurable (fun z : Joint => F e z) :=
    (F e).continuous.stronglyMeasurable
  have hBound : ∀ z : Joint, ‖F e z‖ ≤ (2 : ℝ) := by
    intro z
    have hz := p4Q2EE_SU2_relativeWilsonEnergyBCF_mem_Icc H e z
    have habs : |F e z| ≤ (2 : ℝ) :=
      abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
    simpa [Real.norm_eq_abs] using habs
  have hRep :
      (fun z : Joint => F e z) =ᵐ[muPair]
        ((f e : Lp ℝ 2 muPair) : Joint → ℝ) :=
    (p4Q2EE_SU2_pairHaarJointL2_ae_eq H e).symm
  have hP := p4Q2DA_actualPairHaarProjection_ae_eq_CUmean
    H 2 (Sum.inr e) (f e)
    (fun z : Joint => F e z) hStrong 2 hBound hRep
  exact hP.trans (Filter.Eventually.of_forall
    (p4Q2EH_rightSelectedMean_eq_groupMean H e))

/-- Actual independent pair-Haar selected LEFT CR orthogonal projection
has the SAME constant representative, with NO Wilson-law equality. -/
theorem p4Q2EH_leftSelectedProjection_ae_groupMean (e : Link) :
    (((P (Sum.inl e) (f e) : Lp ℝ 2 muPair) : Joint → ℝ)) =ᵐ[muPair]
      fun _ => p4Q2EH_groupWilsonHaarMean H := by
  have hStrong : StronglyMeasurable (fun z : Joint => F e z) :=
    (F e).continuous.stronglyMeasurable
  have hBound : ∀ z : Joint, ‖F e z‖ ≤ (2 : ℝ) := by
    intro z
    have hz := p4Q2EE_SU2_relativeWilsonEnergyBCF_mem_Icc H e z
    have habs : |F e z| ≤ (2 : ℝ) :=
      abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
    simpa [Real.norm_eq_abs] using habs
  have hRep :
      (fun z : Joint => F e z) =ᵐ[muPair]
        ((f e : Lp ℝ 2 muPair) : Joint → ℝ) :=
    (p4Q2EE_SU2_pairHaarJointL2_ae_eq H e).symm
  have hP := p4Q2DA_actualPairHaarProjection_ae_eq_CUmean
    H 2 (Sum.inl e) (f e)
    (fun z : Joint => F e z) hStrong 2 hBound hRep
  exact hP.trans (Filter.Eventually.of_forall
    (p4Q2EH_leftSelectedMean_eq_groupMean H e))

end ActualHaar
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EH_rightUpdate
#print axioms MGAP4D.MathlibAnalytic.p4Q2EH_leftUpdate

#print axioms MGAP4D.MathlibAnalytic.p4Q2EH_rightSelectedMean_eq_groupMean
#print axioms MGAP4D.MathlibAnalytic.p4Q2EH_leftSelectedMean_eq_groupMean
#print axioms MGAP4D.MathlibAnalytic.p4Q2EH_rightSelectedProjection_ae_groupMean
#print axioms MGAP4D.MathlibAnalytic.p4Q2EH_leftSelectedProjection_ae_groupMean
