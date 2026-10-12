import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalColorAverageSharpnessBarrier
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRieszExactUnnormalizedTwelveFactor
import Mathlib.Tactic

/-!
# P4-Q2-EB: best universal true color-cardinality coefficient for original Wilson Haar reference

EA establishes that for ALL nonnegative link weights on the genuine six-color
spatial carrier the coefficient is at most the reciprocal of the true
largest color link cardinality. DQ instead used the reciprocal of the
WHOLE spatial link cardinality. Here we promote EA's exact genuine
spatial-color sharpness result to the genuine original Wilson Haar
reference normalized 12-color bound, using the existing DP identity
between the original link-fiber mass floor and ACTUAL independent pair-Haar
coordinate L² defects. No new measure or independence assumption is inserted.

We define maxColorCard(H) := max_{c:Fin6} card(actual physical color c),
prove it is positive and ≤ the actual number of physical spatial links,
and prove the exact six-color averaging bound with its reciprocal.
This improves DQ's original finite-volume coefficient
m exp(-32 beta)/(12 * spatialLinkCard(H))
to the new (still finite-volume) coefficient
m exp(-32 beta)/(12 * maxColorCard(H)).

The witness m comes from the unchanged ACTUAL original Wilson link-mass
floor DG/CP. The six-color and left/right defect formula is unchanged.
This is NOT a common mass floor across volume, not a uniform spectral
gap, not a positive-beta commuting Wilson conditional family, and not
a 4D continuum Yang--Mills theorem. Signed fine/frozen Krylov remains open.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section
set_option maxHeartbeats 2000000
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

/-- The maximum size of any of the six ACTUAL spatial color classes. -/
noncomputable def p4Q2EB_maxColorCard (H : ℕ) : ℕ :=
  (Finset.univ : Finset (Fin 6)).sup
    (fun c => Fintype.card (p4Q2BA_ColorLinks H c))

theorem p4Q2EB_colorCard_le_max (H : ℕ) (c : Fin 6) :
    Fintype.card (p4Q2BA_ColorLinks H c) ≤ p4Q2EB_maxColorCard H := by
  unfold p4Q2EB_maxColorCard
  exact Finset.le_sup (Finset.mem_univ c)

theorem p4Q2EB_maxColorCard_pos (H : ℕ) :
    0 < p4Q2EB_maxColorCard H := by
  have hnonempty := p4Q2BA_colorLinks_card_pos H (0 : Fin 6)
  have hle := p4Q2EB_colorCard_le_max H (0 : Fin 6)
  exact lt_of_lt_of_le hnonempty hle

theorem p4Q2EB_maxColorCard_le_allLinks (H : ℕ) :
    p4Q2EB_maxColorCard H ≤
      Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) := by
  unfold p4Q2EB_maxColorCard
  apply Finset.sup_le
  intro c _hc
  exact Fintype.card_le_of_injective
    (fun e : p4Q2BA_ColorLinks H c => e.1)
    (by intro a b hab; exact Subtype.ext hab)

/-- The DQ/EA universal comparison, now with the optimal genuine
six-color maximum cardinality, for arbitrary nonnegative ACTUAL links. -/
theorem p4Q2EB_colorAverage_ge_maxColorAllLinkSum (H : ℕ)
    (g : PeriodicHypercubicEvenSpatialSliceLink H → ENNReal) :
    (p4Q2EB_maxColorCard H : ENNReal)⁻¹ *
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, g e) ≤
        ∑ c : Fin 6,
          (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
            (∑ e : p4Q2BA_ColorLinks H c, g e.1) := by
  apply (p4Q2EA_actualColorAverages_lower_coefficient_iff
      H (p4Q2EB_maxColorCard H : ENNReal)⁻¹).2
  intro c
  have h := p4Q2EB_colorCard_le_max H c
  have hENN :
      (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal) ≤
        (p4Q2EB_maxColorCard H : ENNReal) := by
    exact_mod_cast h
  exact ENNReal.inv_le_inv.mpr hENN

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

/-- The ACTUAL maximum-color improvement over DQ's whole-link coefficient. -/
noncomputable def p4Q2EB_maxColorHilbertFloorCoefficient (m : ℝ) : ENNReal :=
  (12 : ENNReal)⁻¹ * (p4Q2EB_maxColorCard H : ENNReal)⁻¹ *
    (ENNReal.ofReal m * ENNReal.ofReal (Real.exp (-32 * beta)))

theorem p4Q2EB_maxColorHilbertFloorCoefficient_pos
    (m : ℝ) (hm : 0 < m) :
    0 < p4Q2EB_maxColorHilbertFloorCoefficient H beta m := by
  unfold p4Q2EB_maxColorHilbertFloorCoefficient
  have h12 : 0 < (12 : ENNReal)⁻¹ :=
    ENNReal.inv_pos.mpr (by norm_num)
  have hCard : 0 < (p4Q2EB_maxColorCard H : ENNReal)⁻¹ :=
    ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)
  have hm' : 0 < ENNReal.ofReal m := ENNReal.ofReal_pos.mpr hm
  have he : 0 < ENNReal.ofReal (Real.exp (-32 * beta)) :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  exact (ENNReal.mul_pos_iff).2
    ⟨(ENNReal.mul_pos_iff).2 ⟨h12, hCard⟩,
      (ENNReal.mul_pos_iff).2 ⟨hm', he⟩⟩

/-- Compared with DQ, EB's genuine max-color coefficient is NEVER smaller. -/
theorem p4Q2EB_oldFloor_le_maxColorFloor (m : ℝ) :
    p4Q2DQ_allLinkHilbertFloorCoefficient H beta m ≤
      p4Q2EB_maxColorHilbertFloorCoefficient H beta m := by
  have hmax := p4Q2EB_maxColorCard_le_allLinks H
  have hENN :
      (p4Q2EB_maxColorCard H : ENNReal) ≤
        (Fintype.card Link : ENNReal) := by exact_mod_cast hmax
  have hInv := ENNReal.inv_le_inv.mpr hENN
  unfold p4Q2DQ_allLinkHilbertFloorCoefficient
    p4Q2EB_maxColorHilbertFloorCoefficient
  calc
    (12 : ENNReal)⁻¹ * (Fintype.card Link : ENNReal)⁻¹ *
        (ENNReal.ofReal m * ENNReal.ofReal (Real.exp (-32 * beta))) =
      ((ENNReal.ofReal m * ENNReal.ofReal (Real.exp (-32 * beta))) *
        (Fintype.card Link : ENNReal)⁻¹) * (12 : ENNReal)⁻¹ := by ac_rfl
    _ ≤ ((ENNReal.ofReal m * ENNReal.ofReal (Real.exp (-32 * beta))) *
          (p4Q2EB_maxColorCard H : ENNReal)⁻¹) * (12 : ENNReal)⁻¹ := by
      exact mul_le_mul_right (mul_le_mul_right hInv _) _
    _ = (12 : ENNReal)⁻¹ * (p4Q2EB_maxColorCard H : ENNReal)⁻¹ *
        (ENNReal.ofReal m * ENNReal.ofReal (Real.exp (-32 * beta))) := by ac_rfl

/-- Genuine twelve-color physical Wilson Haar fiber mass floor, improved
ONLY by the exact six-color maximum-cardinality geometry. -/
theorem p4Q2EB_twelveColorHilbertFloor_ge_fullCoordinateResidualSum
    (m : ℝ) (f : JH) :
    (12 : ENNReal)⁻¹ * (p4Q2EB_maxColorCard H : ENNReal)⁻¹ *
        (∑ i : I,
          ENNReal.ofReal m *
            (ENNReal.ofReal (Real.exp (-32 * beta)) *
              ENNReal.ofReal (‖f - P i f‖ ^ 2))) ≤
      p4Q2DP_originalTwelveColorPairHaarHilbertFloor H N beta m f := by
  classical
  let q : I → ENNReal := fun i =>
    ENNReal.ofReal m *
      (ENNReal.ofReal (Real.exp (-32 * beta)) *
        ENNReal.ofReal (‖f - P i f‖ ^ 2))
  have hR := p4Q2EB_colorAverage_ge_maxColorAllLinkSum H (fun e : Link => q (Sum.inr e))
  have hL := p4Q2EB_colorAverage_ge_maxColorAllLinkSum H (fun e : Link => q (Sum.inl e))
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
    (12 : ENNReal)⁻¹ * (p4Q2EB_maxColorCard H : ENNReal)⁻¹ *
      (∑ i : I, q i) ≤
      p4Q2DP_originalTwelveColorPairHaarHilbertFloor H N beta m f
  calc
    (12 : ENNReal)⁻¹ * (p4Q2EB_maxColorCard H : ENNReal)⁻¹ *
        (∑ i : I, q i) =
      (12 : ENNReal)⁻¹ *
        ((p4Q2EB_maxColorCard H : ENNReal)⁻¹ *
            (∑ e : Link, q (Sum.inr e)) +
         (p4Q2EB_maxColorCard H : ENNReal)⁻¹ *
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

/-- Same genuine improvement, now factored outside actual pair-Haar defects. -/
theorem p4Q2EB_twelveColorHilbertFloor_ge_factoredAllCoordinateResidualSum
    (m : ℝ) (f : JH) :
    p4Q2EB_maxColorHilbertFloorCoefficient H beta m *
        (∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2)) ≤
      p4Q2DP_originalTwelveColorPairHaarHilbertFloor H N beta m f := by
  have h := p4Q2EB_twelveColorHilbertFloor_ge_fullCoordinateResidualSum
    H N beta m f
  convert h using 1
  simp [p4Q2EB_maxColorHilbertFloorCoefficient, Fintype.sum_sum_type,
    Finset.mul_sum, mul_add, mul_assoc]

/-- One and the SAME original physical Wilson m>0 controls every
bounded strongly measurable original Wilson concrete joint observable. -/
theorem p4Q2EB_originalWilsonTwelveReference_ge_maxColorHilbertDefects :
    ∃ m : ℝ, 0 < m ∧
      ∀ (f : JH) (F : Joint → ℝ), StronglyMeasurable F →
        ∀ (M : ℝ), (∀ z, ‖F z‖ ≤ M) →
          F =ᵐ[muPair] (f : Joint → ℝ) →
          p4Q2EB_maxColorHilbertFloorCoefficient H beta m *
            (∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2)) ≤
              p4Q2BC_originalPhysicalTwelveColorHaarReference
                H N hN beta hbeta F := by
  obtain ⟨m, hm, hReference⟩ :=
    p4Q2DG_originalTwelveColorHaarReference_ge_allLinkMassFloor
      H N hN beta hbeta
  refine ⟨m, hm, ?_⟩
  intro f F hF M hM hEq
  calc
    p4Q2EB_maxColorHilbertFloorCoefficient H beta m *
        (∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2)) ≤
      p4Q2DP_originalTwelveColorPairHaarHilbertFloor H N beta m f :=
        p4Q2EB_twelveColorHilbertFloor_ge_factoredAllCoordinateResidualSum
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

#print axioms MGAP4D.MathlibAnalytic.p4Q2EB_colorAverage_ge_maxColorAllLinkSum
#print axioms MGAP4D.MathlibAnalytic.p4Q2EB_oldFloor_le_maxColorFloor
#print axioms MGAP4D.MathlibAnalytic.p4Q2EB_originalWilsonTwelveReference_ge_maxColorHilbertDefects
