import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwelveColorHilbertResidualLowerBound
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarGlobalMeanPoincare
import Mathlib.Tactic

/-!
# P4-Q2-DQ: from genuine Wilson 12-color Haar averages to all-link L² energy

DP gives the original Wilson twelve-color reference lower bound, with the
literal color cardinalities and factor 1/12, in terms of genuine independent
pair-Haar CR coordinate Hilbert defects. DC gives an unnormalized sum over
ALL coordinates and a pair-Haar global-mean Poincare inequality.

Here the six original color fibers are proved to be an EXACT partition of
the genuine spatial link carrier. Since the number of links of a color does
not exceed the total spatial-link cardinality, the genuine normalized
twelve-color floor bounds an explicit finite-volume positive coefficient
times the UNNORMALIZED actual CR all-coordinate L² squared-defect sum.

No uniform-volume assertion, interacting-Wilson projection commutation,
change of physical measures, or new axiom is used. The next step is to
combine this with DC and DF at the level of physical variance.
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

private def p4Q2DQ_colorSigmaEquiv (H : ℕ) :
    (Σ c : Fin 6, p4Q2BA_ColorLinks H c) ≃
      PeriodicHypercubicEvenSpatialSliceLink H where
  toFun p := p.2.1
  invFun e :=
    ⟨periodicHypercubicEvenGroundStateSpatialColorEquivFin
        (periodicHypercubicEvenSpatialSliceLinkColor H e),
      ⟨e, by simp⟩⟩
  left_inv := by
    intro p
    rcases p with ⟨c, ⟨e, he⟩⟩
    have hc :
        periodicHypercubicEvenGroundStateSpatialColorEquivFin
          (periodicHypercubicEvenSpatialSliceLinkColor H e) = c := by
      rw [he, Equiv.apply_symm_apply]
    cases hc
    rfl
  right_inv := by
    intro e
    rfl

/-- The six *actual* color subtypes cover every link exactly once. -/
theorem p4Q2DQ_sum_colorLinks_eq_allLinks
    (H : ℕ)
    (g : PeriodicHypercubicEvenSpatialSliceLink H → ENNReal) :
    (∑ c : Fin 6, ∑ e : p4Q2BA_ColorLinks H c, g e.1) =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, g e := by
  classical
  calc
    (∑ c : Fin 6, ∑ e : p4Q2BA_ColorLinks H c, g e.1) =
        ∑ p : (Σ c : Fin 6, p4Q2BA_ColorLinks H c), g p.2.1 := by
      rw [Fintype.sum_sigma]
    _ = ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, g e :=
      (p4Q2DQ_colorSigmaEquiv H).sum_comp g

/-- The literal color-normalized average dominates the uniform
1/(total link cardinality) multiple of the full unnormalized link sum.
The inequality also works for arbitrary extended-nonnegative weights. -/
theorem p4Q2DQ_colorAverage_ge_allLinkSum
    (H : ℕ)
    (g : PeriodicHypercubicEvenSpatialSliceLink H → ENNReal) :
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ENNReal)⁻¹ *
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, g e) ≤
      ∑ c : Fin 6,
        (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
          (∑ e : p4Q2BA_ColorLinks H c, g e.1) := by
  classical
  rw [← p4Q2DQ_sum_colorLinks_eq_allLinks H g, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _hc
  have hCard :
      Fintype.card (p4Q2BA_ColorLinks H c) ≤
        Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_le_of_injective
      (fun e : p4Q2BA_ColorLinks H c => e.1)
      (by intro a b hab; exact Subtype.ext hab)
  exact mul_le_mul_right
    (ENNReal.inv_le_inv.mpr (by exact_mod_cast hCard)) _

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "I" => PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "JH" => Lp ℝ 2 muPair
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H N

/-- The explicitly finite-volume coefficient, preserving both the
physical factor 1/12 and original Wilson factor exp(-32 beta). -/
noncomputable def p4Q2DQ_allLinkHilbertFloorCoefficient (m : ℝ) : ENNReal :=
  (12 : ENNReal)⁻¹ *
    (Fintype.card Link : ENNReal)⁻¹ *
      (ENNReal.ofReal m * ENNReal.ofReal (Real.exp (-32 * beta)))

/-- The genuine finite-volume coefficient is strictly positive whenever
the original Perron-vacuum fiber mass floor m is positive. -/
theorem p4Q2DQ_allLinkHilbertFloorCoefficient_pos
    (m : ℝ) (hm : 0 < m) :
    0 < p4Q2DQ_allLinkHilbertFloorCoefficient H beta m := by
  unfold p4Q2DQ_allLinkHilbertFloorCoefficient
  have h12 : 0 < (12 : ENNReal)⁻¹ :=
    ENNReal.inv_pos.mpr (by norm_num)
  have hCard : 0 < (Fintype.card Link : ENNReal)⁻¹ :=
    ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)
  have hm' : 0 < ENNReal.ofReal m := ENNReal.ofReal_pos.mpr hm
  have he : 0 < ENNReal.ofReal (Real.exp (-32 * beta)) :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  exact (ENNReal.mul_pos_iff).2
    ⟨(ENNReal.mul_pos_iff).2 ⟨h12, hCard⟩,
      (ENNReal.mul_pos_iff).2 ⟨hm', he⟩⟩

/-- The ACTUAL normalized six-right/six-left Wilson reference floor
controls every one of the unnormalized CR projection defects. -/
theorem p4Q2DQ_twelveColorHilbertFloor_ge_fullCoordinateResidualSum
    (m : ℝ) (f : JH) :
    (12 : ENNReal)⁻¹ * (Fintype.card Link : ENNReal)⁻¹ *
        (∑ i : I,
          ENNReal.ofReal m *
            (ENNReal.ofReal (Real.exp (-32 * beta)) *
              ENNReal.ofReal (‖f - P i f‖ ^ 2))) ≤
      p4Q2DP_originalTwelveColorPairHaarHilbertFloor H N beta m f := by
  classical
  letI : Fintype I := p4Q2CR_actualJointIndexFintype H
  let q : I → ENNReal := fun i =>
    ENNReal.ofReal m *
      (ENNReal.ofReal (Real.exp (-32 * beta)) *
        ENNReal.ofReal (‖f - P i f‖ ^ 2))
  have hR := p4Q2DQ_colorAverage_ge_allLinkSum H (fun e : Link => q (Sum.inr e))
  have hL := p4Q2DQ_colorAverage_ge_allLinkSum H (fun e : Link => q (Sum.inl e))
  have hsplit :
      (∑ i : I, q i) =
        (∑ e : Link, q (Sum.inl e)) +
          (∑ e : Link, q (Sum.inr e)) := by
    simp only [Fintype.sum_sum_type]
  have hFloor :
      p4Q2DP_originalTwelveColorPairHaarHilbertFloor H N beta m f =
        (12 : ENNReal)⁻¹ *
          ((∑ c : Fin 6,
              (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
                (∑ e : p4Q2BA_ColorLinks H c, q (Sum.inr e.1))) +
            (∑ c : Fin 6,
              (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
                (∑ e : p4Q2BA_ColorLinks H c, q (Sum.inl e.1)))) := by
    simp [p4Q2DP_originalTwelveColorPairHaarHilbertFloor,
      p4Q2DP_originalTwelveColorPairHaarHilbertFloorAverage,
      Fintype.sum_sum_type, q]
  change
    (12 : ENNReal)⁻¹ * (Fintype.card Link : ENNReal)⁻¹ *
      (∑ i : I, q i) ≤
      p4Q2DP_originalTwelveColorPairHaarHilbertFloor H N beta m f
  calc
    (12 : ENNReal)⁻¹ * (Fintype.card Link : ENNReal)⁻¹ *
        (∑ i : I, q i) =
      (12 : ENNReal)⁻¹ *
        ((Fintype.card Link : ENNReal)⁻¹ *
            (∑ e : Link, q (Sum.inr e)) +
         (Fintype.card Link : ENNReal)⁻¹ *
            (∑ e : Link, q (Sum.inl e))) := by
      rw [hsplit]
      ring
    _ ≤ (12 : ENNReal)⁻¹ *
          ((∑ c : Fin 6,
              (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
                (∑ e : p4Q2BA_ColorLinks H c, q (Sum.inr e.1))) +
            (∑ c : Fin 6,
              (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
                (∑ e : p4Q2BA_ColorLinks H c, q (Sum.inl e.1)))) :=
      mul_le_mul_right (add_le_add hR hL) _
    _ = p4Q2DP_originalTwelveColorPairHaarHilbertFloor H N beta m f :=
      hFloor.symm

/-- Exact same bound, now with a single strictly positive finite-volume
coefficient outside DC's literal UNNORMALIZED all-coordinate defect sum. -/
theorem p4Q2DQ_twelveColorHilbertFloor_ge_factoredAllCoordinateResidualSum
    (m : ℝ) (f : JH) :
    p4Q2DQ_allLinkHilbertFloorCoefficient H beta m *
        (∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2)) ≤
      p4Q2DP_originalTwelveColorPairHaarHilbertFloor H N beta m f := by
  letI : Fintype I := p4Q2CR_actualJointIndexFintype H
  have h := p4Q2DQ_twelveColorHilbertFloor_ge_fullCoordinateResidualSum
    H N beta m f
  convert h using 1
  · simp [p4Q2DQ_allLinkHilbertFloorCoefficient, Finset.mul_sum, mul_assoc]
  · rfl

/-- ONE physical original Wilson mass floor, independent of F and f,
controls the genuinely unnormalized pair-Haar all-coordinate residuals
for ALL bounded strongly measurable physical joint observables. -/
theorem p4Q2DQ_originalWilsonTwelveReference_ge_allCoordinateHilbertDefects :
    ∃ m : ℝ, 0 < m ∧
      ∀ (f : JH) (F : Joint → ℝ), StronglyMeasurable F →
        ∀ (M : ℝ), (∀ z, ‖F z‖ ≤ M) →
          F =ᵐ[muPair] (f : Joint → ℝ) →
          p4Q2DQ_allLinkHilbertFloorCoefficient H beta m *
            (∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2)) ≤
              p4Q2BC_originalPhysicalTwelveColorHaarReference
                H N hN beta hbeta F := by
  letI : Fintype I := p4Q2CR_actualJointIndexFintype H
  obtain ⟨m, hm, hReference⟩ :=
    p4Q2DG_originalTwelveColorHaarReference_ge_allLinkMassFloor
      H N hN beta hbeta
  refine ⟨m, hm, ?_⟩
  intro f F hF M hM hEq
  calc
    p4Q2DQ_allLinkHilbertFloorCoefficient H beta m *
        (∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2)) ≤
      p4Q2DP_originalTwelveColorPairHaarHilbertFloor H N beta m f :=
        p4Q2DQ_twelveColorHilbertFloor_ge_factoredAllCoordinateResidualSum
          H N beta m f
    _ = p4Q2DG_originalTwelveColorHaarMassFloor H N beta m F :=
      (p4Q2DP_originalTwelveColorHaarMassFloor_eq_L2_defects
        H N beta m f F hF M hM hEq).symm
    _ ≤ p4Q2BC_originalPhysicalTwelveColorHaarReference
          H N hN beta hbeta F := hReference F hF

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
