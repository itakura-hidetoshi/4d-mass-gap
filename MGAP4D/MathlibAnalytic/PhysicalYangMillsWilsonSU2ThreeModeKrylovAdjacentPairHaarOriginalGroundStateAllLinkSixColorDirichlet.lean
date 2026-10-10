import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFiberSixSpatialBoundedCoreDirichlet
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSameColorOneLinkSweepEqualsColorBlock
import Mathlib.Tactic

/-!
# P4-Q2-BA: ALL original physical Wilson right links, grouped into six colors

AZ proves the original actual Wilson mass-weighted Haar Dirichlet reference
for each selected target right spatial link of a bounded strongly measurable
joint observable F is dominated by the genuine joint-L2 CondExp projection
residual. Its local Wilson comparison factor exp(-32 beta) has NO spatial
volume dependence; its weight remains the ACTUAL ground-state fiber mass.

BA takes finite sums over EVERY spatial right link in each six-color class,
without replacing physical fibers or assuming positive-beta same-color
commutation, conditional independence, or an unproved global spectral gap.

For each color c, the sum of original mass-weighted link reference energies
is below the sum of genuine one-link physical residuals and then below the
NUMBER OF LINKS of color c times the true color-block residual. Dividing
by that finite nonzero cardinality gives a normalized average bound free of
a volume coefficient on the right. Averaging over six colors preserves this.

These are local-to-color UPPER comparisons. They do NOT give a reverse frame
inequality or a volume-/spacing-uniform physical Yang-Mills mass gap.

BA also discharges AZ's six-color representative existence directly from the
already formalized geometric nonemptiness of every color.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 2600000
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

/-- Literal finite carrier of ALL spatial right links in color c. -/
abbrev p4Q2BA_ColorLinks (H : ℕ) (c : Fin 6) : Type :=
  PeriodicHypercubicEvenFixedSpatialColorLink H
    (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)

local instance p4Q2BAColorLinksFintype (H : ℕ) (c : Fin 6) :
    Fintype (p4Q2BA_ColorLinks H c) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
    periodicHypercubicEvenSpatialSliceLinkColor H e =
      periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)

/-- An ACTUAL spatial target exists in every one of the six classes,
so the all-link color average is never an empty or formal family. -/
theorem p4Q2BA_colorLinks_nonempty (H : ℕ) (c : Fin 6) :
    Nonempty (p4Q2BA_ColorLinks H c) :=
  periodicHypercubicEvenFixedSpatialColorLink_nonempty H
    (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)

/-- Canonical (choice-based) representatives discharge the AZ color constraint.
This is an actual spatial link for every c, not a synthetic link carrier. -/
noncomputable def p4Q2BA_sixColorRepresentatives (H : ℕ) :
    Fin 6 → PeriodicHypercubicEvenSpatialSliceLink H :=
  fun c => (Classical.choice (p4Q2BA_colorLinks_nonempty H c)).1

theorem p4Q2BA_sixColorRepresentatives_correct
    (H : ℕ) (c : Fin 6) :
    periodicHypercubicEvenSpatialSliceLinkColor H
        (p4Q2BA_sixColorRepresentatives H c) =
      periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c :=
  (Classical.choice (p4Q2BA_colorLinks_nonempty H c)).property

/-- Every color's ACTUAL physical right-link Haar reference energy, summed
over ALL links of that color (with their own genuine ground-state fiber mass).
The local Wilson coefficient stays exactly exp(-32 beta). -/
noncomputable def p4Q2BA_colorAllLinkHaarReferenceSum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (c : Fin 6)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) : ENNReal :=
  ∑ e : p4Q2BA_ColorLinks H c,
    p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta e.1 F

/-- Sum of genuine one-link physical Hilbert projection residual norms
over the SAME actual color class, without any independence assumption. -/
noncomputable def p4Q2BA_colorAllLinkPhysicalResidualSum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (c : Fin 6)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) : ENNReal :=
  let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
  ∑ e : p4Q2BA_ColorLinks H c,
    ENNReal.ofReal
      (‖f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta e.1 f‖ ^ 2)

/-- The actual physical joint six-spatial-color projection residual.
It is NOT a decoupled, pair-Haar or beta-zero projection. -/
noncomputable def p4Q2BA_colorPhysicalBlockResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (c : Fin 6)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) : ENNReal :=
  let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
  ENNReal.ofReal
    (‖f -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
        H N hN beta hbeta c f‖ ^ 2)

/-- The original mass-weighted reference energy, summed over ALL actual
right links of a color, is dominated by the sum of the real physical
joint-L2 one-link conditional-expectation residuals. -/
theorem p4Q2BA_colorAllLinkHaarReferenceSum_le_physicalResidualSum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (c : Fin 6)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c F ≤
      p4Q2BA_colorAllLinkPhysicalResidualSum
        H N hN beta hbeta c F hF bound hbound := by
  classical
  let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
  change (∑ e : p4Q2BA_ColorLinks H c,
      p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta e.1 F) ≤
    (∑ e : p4Q2BA_ColorLinks H c,
      ENNReal.ofReal
        (‖f -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta e.1 f‖ ^ 2))
  apply Finset.sum_le_sum
  intro e _he
  exact p4Q2AZ_originalJointHaarReferenceEnergy_le_physicalCondExpResidual
    H N hN beta hbeta e.1 F hF bound hbound

/-- Every genuine right-link residual is at most its own genuine physical
color-block residual. This is sigma-algebra inclusion, not commutation. -/
theorem p4Q2BA_colorAllLinkPhysicalResidualSum_le_card_blockResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (c : Fin 6)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BA_colorAllLinkPhysicalResidualSum
        H N hN beta hbeta c F hF bound hbound ≤
      (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal) *
        p4Q2BA_colorPhysicalBlockResidual
          H N hN beta hbeta c F hF bound hbound := by
  classical
  let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
  let block := p4Q2BA_colorPhysicalBlockResidual
    H N hN beta hbeta c F hF bound hbound
  change
    (∑ e : p4Q2BA_ColorLinks H c,
      ENNReal.ofReal
        (‖f -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta e.1 f‖ ^ 2)) ≤
    (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal) * block
  calc
    (∑ e : p4Q2BA_ColorLinks H c,
      ENNReal.ofReal
        (‖f -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta e.1 f‖ ^ 2)) ≤
      (∑ _e : p4Q2BA_ColorLinks H c, block) := by
        apply Finset.sum_le_sum
        intro e _he
        have hColor :=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_residual_sq_le_color
            H N hN beta hbeta e.1 f
        rw [e.property] at hColor
        change ENNReal.ofReal
          (‖f -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta e.1 f‖ ^ 2) ≤
          ENNReal.ofReal
            (‖f -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
                H N hN beta hbeta c f‖ ^ 2)
        exact ENNReal.ofReal_le_ofReal (by
          simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2]
            using hColor)
    _ = (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal) * block := by
      simp [nsmul_eq_mul]

/-- Unnormalized all-link mass-weighted reference sum carries only the
EXACT explicit finite color multiplicity: there is no hidden
volume-dependent LOCAL Wilson coefficient. -/
theorem p4Q2BA_colorAllLinkHaarReferenceSum_le_card_blockResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (c : Fin 6)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c F ≤
      (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal) *
        p4Q2BA_colorPhysicalBlockResidual
          H N hN beta hbeta c F hF bound hbound := by
  exact
    (p4Q2BA_colorAllLinkHaarReferenceSum_le_physicalResidualSum
      H N hN beta hbeta c F hF bound hbound).trans
    (p4Q2BA_colorAllLinkPhysicalResidualSum_le_card_blockResidual
      H N hN beta hbeta c F hF bound hbound)

/-- Cardinality is strictly positive for EVERY actual spatial color;
therefore normalizing the all-link sum does not divide by zero. -/
theorem p4Q2BA_colorLinks_card_pos (H : ℕ) (c : Fin 6) :
    0 < Fintype.card (p4Q2BA_ColorLinks H c) := by
  exact Fintype.card_pos_iff.mpr (p4Q2BA_colorLinks_nonempty H c)

/-- BA main color theorem: the color-AVERAGE of original physical
mass-weighted link Dirichlet reference energies is bounded by the actual
physical joint Hilbert color residual, with coefficient one on the RHS.

The physical Wilson local factor remains exp(-32 beta) inside each
reference energy; no dependence or frame condition is inserted. -/
theorem p4Q2BA_colorAllLinkHaarReferenceAverage_le_blockResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (c : Fin 6)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
      p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c F ≤
    p4Q2BA_colorPhysicalBlockResidual
      H N hN beta hbeta c F hF bound hbound := by
  have hcardNonzero :
      (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (p4Q2BA_colorLinks_card_pos H c))
  have hcardFinite :
      (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  calc
    (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
        p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c F ≤
      (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
        ((Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal) *
          p4Q2BA_colorPhysicalBlockResidual
            H N hN beta hbeta c F hF bound hbound) := by
      exact mul_le_mul_right
        (p4Q2BA_colorAllLinkHaarReferenceSum_le_card_blockResidual
          H N hN beta hbeta c F hF bound hbound)
        (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹
    _ = p4Q2BA_colorPhysicalBlockResidual
          H N hN beta hbeta c F hF bound hbound := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hcardNonzero hcardFinite, one_mul]

/-- Every original physical right spatial link (not only one link per color)
satisfies the actual all-link finite Dirichlet comparison. -/
theorem p4Q2BA_allRightLinksOriginalHaarReferenceSum_le_physicalResidualSum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta e F) ≤
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ENNReal.ofReal
          (‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta e
              (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)‖ ^ 2)) := by
  classical
  apply Finset.sum_le_sum
  intro e _he
  exact p4Q2AZ_originalJointHaarReferenceEnergy_le_physicalCondExpResidual
    H N hN beta hbeta e F hF bound hbound

/-- Six ACTUAL color averages of ALL genuine physical right links are
bounded by the six genuine physical color-block projection residuals.
The two normalizations (per finite color cardinality, and 1/6) are explicit.
This is a one-sided comparison, NOT global Poincare coercivity. -/
theorem p4Q2BA_allRightLinksSixSpatialNormalizedReference_le_colorResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (6 : ENNReal)⁻¹ *
      (∑ c : Fin 6,
        (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
          p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c F) ≤
      (6 : ENNReal)⁻¹ *
      (∑ c : Fin 6,
        p4Q2BA_colorPhysicalBlockResidual H N hN beta hbeta c F hF bound hbound) := by
  exact mul_le_mul_right
    (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 6))) (by
      intro c _hc
      exact p4Q2BA_colorAllLinkHaarReferenceAverage_le_blockResidual
        H N hN beta hbeta c F hF bound hbound))
    (6 : ENNReal)⁻¹

/-- BA eliminates AZ's arbitrary representative-choices premise by
constructing one literal target link in each real color class. -/
theorem p4Q2BA_existingAZ_selectedSixColor_reference_le_residual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∑ c : Fin 6,
      p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta
        (p4Q2BA_sixColorRepresentatives H c) F) ≤
      (∑ c : Fin 6,
        p4Q2BA_colorPhysicalBlockResidual H N hN beta hbeta c F hF bound hbound) := by
  simpa only [p4Q2BA_colorPhysicalBlockResidual] using
    (p4Q2AZ_sixSelectedOriginalWilsonHaarEnergies_le_sixSpatialColorResiduals
      H N hN beta hbeta (p4Q2BA_sixColorRepresentatives H)
      (p4Q2BA_sixColorRepresentatives_correct H)
      F hF bound hbound)

end
end MathlibAnalytic
end MGAP4D
