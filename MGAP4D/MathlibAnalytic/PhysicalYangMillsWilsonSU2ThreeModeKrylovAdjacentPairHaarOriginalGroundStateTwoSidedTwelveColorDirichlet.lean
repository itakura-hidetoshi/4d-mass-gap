import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGroundStateAllLinkSixColorDirichlet
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSwapOneLinkConjugacy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwoSidedTwelveSpatialConditionalExpectation
import Mathlib.Tactic

/-!
# P4-Q2-BB: original Wilson all-link Dirichlet estimates on both boundaries

BA controls all right spatial target links of the ORIGINAL Wilson ground-state
joint measure, grouped into six actual colors. This file uses the ALREADY
PROVED invariance of that same original physical joint measure under exchange
of its left and right boundaries. No second physical law is introduced.

Endpoint exchange transports a bounded concrete joint observable F to its
swapped observable and its genuine joint L² representative by the existing
physical swap isometry. The exact right one-link CondExpL2 projection
conjugates to the left one-link projection. Consequently BA's mass-weighted
right-fiber energy applied to swapped F is an actual original-measure left
boundary Dirichlet reference energy, with the SAME factor exp(-32 beta).

All left spatial links are then summed by their six genuine colors, using
only the retained-sigma-algebra projection residual inequality. Finally the
right six and left six are assembled into the PREEXISTING twelve-spatial-color
projection family on the SAME genuine physical ground-state joint L² carrier.

The exact per-color cardinalities are normalized separately, then the twelve
colors are averaged with coefficient 1/12. This is a ONE-SIDED local-reference
to physical projection-defect estimate. It does NOT supply a reverse frame
inequality, arbitrary-L² domain extension, or volume- and spacing-uniform
physical mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter Set
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
  p4Q2BAColorLinksFintype

section
variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "JointL2" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta

/-- The original joint observable viewed from the other physical boundary. -/
def p4Q2BB_swapConcrete (F : Joint → ℝ) : Joint → ℝ :=
  fun z => F z.swap

theorem p4Q2BB_swapConcrete_stronglyMeasurable
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    StronglyMeasurable (p4Q2BB_swapConcrete H N F) :=
  hF.comp_measurable measurable_swap

theorem p4Q2BB_swapConcrete_norm_le
    (F : Joint → ℝ) (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    ∀ z, ‖p4Q2BB_swapConcrete H N F z‖ ≤ bound :=
  fun z => hbound z.swap

/-- The concrete swapped observable represented in the SAME physical joint L².
Neither the probability measure nor the coupling parameter is modified. -/
noncomputable def p4Q2BB_swappedJointL2
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) : JointL2 :=
  p4Q2AZ_originalJointL2 H N hN beta hbeta
    (p4Q2BB_swapConcrete H N F)
    (p4Q2BB_swapConcrete_stronglyMeasurable H N F hF)
    bound (p4Q2BB_swapConcrete_norm_le H N F bound hbound)

/-- The original physical endpoint-swap L² equivalence maps the bounded
concrete swapped L² vector EXACTLY back to the original bounded joint vector.
The equality is at the L² quotient level, not at selected exceptional fibers. -/
theorem p4Q2BB_swapL2_swappedConcrete_eq_original
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        (p4Q2BB_swappedJointL2 H N hN beta hbeta F hF bound hbound) =
      p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound := by
  let mu := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
  let mp := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
    H N hN beta hbeta
  let fs : Lp ℝ 2 mu := p4Q2BB_swappedJointL2
    H N hN beta hbeta F hF bound hbound
  let f : Lp ℝ 2 mu := p4Q2AZ_originalJointL2
    H N hN beta hbeta F hF bound hbound
  have hfs : (fun z : Joint => fs z) =ᵐ[mu] p4Q2BB_swapConcrete H N F :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
      H N hN beta hbeta
      (p4Q2BB_swapConcrete H N F)
      (p4Q2BB_swapConcrete_stronglyMeasurable H N F hF)
      bound (p4Q2BB_swapConcrete_norm_le H N F bound hbound)
  have hf : (fun z : Joint => f z) =ᵐ[mu] F :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
      H N hN beta hbeta F hF bound hbound
  have hfsSwap :
      (fun z : Joint => fs z.swap) =ᵐ[mu]
        (fun z => p4Q2BB_swapConcrete H N F z.swap) := by
    simpa only [Function.comp_def] using
      (mp.quasiMeasurePreserving.ae_eq hfs)
  change MeasureTheory.Lp.compMeasurePreserving Prod.swap mp fs = f
  rw [Lp.ext_iff]
  filter_upwards [MeasureTheory.Lp.coeFn_compMeasurePreserving fs mp,
    hfsSwap, hf] with z hcomp hs hz
  calc
    (MeasureTheory.Lp.compMeasurePreserving Prod.swap mp fs) z =
        fs z.swap := hcomp
    _ = p4Q2BB_swapConcrete H N F z.swap := hs
    _ = F z := by cases z; rfl
    _ = f z := hz.symm

/-- The left-link Haar reference is the exact BA original-right-link fiber
reference of swapped F. Physical joint swap invariance and L² conjugacy make
this a reflected ORIGINAL Wilson conditional law, not a new measure. -/
noncomputable def p4Q2BB_originalLeftLinkHaarReferenceEnergy
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) : ENNReal :=
  p4Q2AZ_originalJointHaarReferenceEnergy
    H N hN beta hbeta target (p4Q2BB_swapConcrete H N F)

/-- The original physical left one-link reference controls the genuine
left one-link conditional-expectation residual for any bounded joint core F. -/
theorem p4Q2BB_originalLeftLinkHaarReferenceEnergy_le_leftResidual
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BB_originalLeftLinkHaarReferenceEnergy
        H N hN beta hbeta target F ≤
      ENNReal.ofReal
        (‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
            H N hN beta hbeta target
            (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  let fs := p4Q2BB_swappedJointL2
    H N hN beta hbeta F hF bound hbound
  have hright :=
    p4Q2AZ_originalJointHaarReferenceEnergy_le_physicalCondExpResidual
      H N hN beta hbeta target (p4Q2BB_swapConcrete H N F)
      (p4Q2BB_swapConcrete_stronglyMeasurable H N F hF)
      bound (p4Q2BB_swapConcrete_norm_le H N F bound hbound)
  have hnorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightResidual_norm_eq_left
      H N hN beta hbeta target fs
  rw [p4Q2BB_swapL2_swappedConcrete_eq_original
    H N hN beta hbeta F hF bound hbound] at hnorm
  exact hright.trans_eq
    (congrArg (fun x : ℝ => ENNReal.ofReal (x ^ 2)) hnorm.symm)

/-- Every left spatial link has its original mass-weighted local comparison;
summing over all left links requires no independence hypothesis. -/
theorem p4Q2BB_allLeftLinksHaarReferenceSum_le_leftResidualSum
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      p4Q2BB_originalLeftLinkHaarReferenceEnergy H N hN beta hbeta e F) ≤
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ENNReal.ofReal
          (‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
              H N hN beta hbeta e
              (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)‖ ^ 2)) := by
  classical
  apply Finset.sum_le_sum
  intro e _he
  exact p4Q2BB_originalLeftLinkHaarReferenceEnergy_le_leftResidual
    H N hN beta hbeta e F hF bound hbound

/-- Color summation of the TRUE reflected left-link physical reference. -/
noncomputable def p4Q2BB_leftColorAllLinkHaarReferenceSum
    (c : Fin 6) (F : Joint → ℝ) : ENNReal :=
  p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c
    (p4Q2BB_swapConcrete H N F)

/-- The LEFT color-block residual on the same original joint Hilbert space. -/
noncomputable def p4Q2BB_leftColorPhysicalBlockResidual
    (c : Fin 6) (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) : ENNReal :=
  let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
  ENNReal.ofReal
    (‖f -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2
        H N hN beta hbeta c f‖ ^ 2)

/-- All actual left links in one color are bounded by that color's original
physical Hilbert residual, times the exact finite number of such links.
We do NOT commute the positive-beta link projections. -/
theorem p4Q2BB_leftColorAllLinkReference_le_card_blockResidual
    (c : Fin 6)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BB_leftColorAllLinkHaarReferenceSum
        H N hN beta hbeta c F ≤
      (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal) *
        p4Q2BB_leftColorPhysicalBlockResidual
          H N hN beta hbeta c F hF bound hbound := by
  classical
  let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
  let block := p4Q2BB_leftColorPhysicalBlockResidual
    H N hN beta hbeta c F hF bound hbound
  calc
    p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta c F =
      ∑ e : p4Q2BA_ColorLinks H c,
        p4Q2BB_originalLeftLinkHaarReferenceEnergy H N hN beta hbeta e.1 F := by
          rfl
    _ ≤ ∑ e : p4Q2BA_ColorLinks H c,
        ENNReal.ofReal
          (‖f -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
              H N hN beta hbeta e.1 f‖ ^ 2) := by
          apply Finset.sum_le_sum
          intro e _he
          exact p4Q2BB_originalLeftLinkHaarReferenceEnergy_le_leftResidual
            H N hN beta hbeta e.1 F hF bound hbound
    _ ≤ ∑ _e : p4Q2BA_ColorLinks H c, block := by
          apply Finset.sum_le_sum
          intro e _he
          have hColor :=
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_residual_sq_le_color
              H N hN beta hbeta e.1 f
          rw [e.property] at hColor
          change ENNReal.ofReal
              (‖f -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
                  H N hN beta hbeta e.1 f‖ ^ 2) ≤
            ENNReal.ofReal
              (‖f -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2
                  H N hN beta hbeta c f‖ ^ 2)
          exact ENNReal.ofReal_le_ofReal (by
            simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2]
              using hColor)
    _ = (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal) * block := by
          simp [nsmul_eq_mul]

/-- Normalize the finite real left-link class by its nonzero cardinality.
The coefficient 1 on the color-block RHS is independent of spatial volume. -/
theorem p4Q2BB_leftColorAllLinkReferenceAverage_le_blockResidual
    (c : Fin 6) (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
      p4Q2BB_leftColorAllLinkHaarReferenceSum
        H N hN beta hbeta c F ≤
      p4Q2BB_leftColorPhysicalBlockResidual
        H N hN beta hbeta c F hF bound hbound := by
  have hcard0 :
      (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (p4Q2BA_colorLinks_card_pos H c))
  have hcardTop :
      (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  calc
    (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
        p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta c F ≤
      (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
        ((Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal) *
          p4Q2BB_leftColorPhysicalBlockResidual
            H N hN beta hbeta c F hF bound hbound) := by
            exact mul_le_mul_right
              (p4Q2BB_leftColorAllLinkReference_le_card_blockResidual
                H N hN beta hbeta c F hF bound hbound)
              (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹
    _ = p4Q2BB_leftColorPhysicalBlockResidual
          H N hN beta hbeta c F hF bound hbound := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hcard0 hcardTop, one_mul]

/-- A single one of the twelve genuine spatial colors, retaining its
physical right/left orientation. Every side uses its actual color cardinality. -/
noncomputable def p4Q2BB_twelveColorOriginalHaarReferenceAverage
    (c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor)
    (F : Joint → ℝ) : ENNReal :=
  match c with
  | Sum.inl k =>
      (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
        p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta k F
  | Sum.inr k =>
      (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
        p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta k F

/-- The same twelve-color index, now evaluated on the ACTUAL preexisting
two-sided physical joint-L² conditional expectation family. -/
noncomputable def p4Q2BB_twelveColorPhysicalBlockResidual
    (c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) : ENNReal :=
  let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
  ENNReal.ofReal
    (‖f -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
        H N hN beta hbeta c f‖ ^ 2)

/-- Exact oriented 12-color physical Dirichlet comparison, independently
for each genuine left or right spatial color of the original joint law. -/
theorem p4Q2BB_twelveColorOriginalHaarReferenceAverage_le_physicalBlock
    (c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta c F ≤
      p4Q2BB_twelveColorPhysicalBlockResidual
        H N hN beta hbeta c F hF bound hbound := by
  cases c with
  | inl c =>
      change (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
          p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c F ≤
        p4Q2BA_colorPhysicalBlockResidual H N hN beta hbeta c F hF bound hbound
      exact p4Q2BA_colorAllLinkHaarReferenceAverage_le_blockResidual
        H N hN beta hbeta c F hF bound hbound
  | inr c =>
      change (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
          p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta c F ≤
        p4Q2BB_leftColorPhysicalBlockResidual H N hN beta hbeta c F hF bound hbound
      exact p4Q2BB_leftColorAllLinkReferenceAverage_le_blockResidual
        H N hN beta hbeta c F hF bound hbound

/-- BB main theorem: ALL original physical Wilson right and left spatial
link reference energies are controlled, color by color, by the PREEXISTING
twelve genuine physical joint-L² projections. The local coefficient e^(-32β)
is unchanged and the twelve spatial colors are averaged by 1/12.

This gives neither a reverse physical Poincare inequality nor a uniform
continuum Hamiltonian mass gap. -/
theorem p4Q2BB_originalTwoSidedAllLinkTwelveColorDirichlet_le_physicalResidual
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (12 : ENNReal)⁻¹ *
      (∑ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
        p4Q2BB_twelveColorOriginalHaarReferenceAverage
          H N hN beta hbeta c F) ≤
    (12 : ENNReal)⁻¹ *
      (∑ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
        p4Q2BB_twelveColorPhysicalBlockResidual
          H N hN beta hbeta c F hF bound hbound) := by
  exact mul_le_mul_right
    (Finset.sum_le_sum (s :=
      (Finset.univ : Finset PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor)) (by
        intro c _hc
        exact p4Q2BB_twelveColorOriginalHaarReferenceAverage_le_physicalBlock
          H N hN beta hbeta c F hF bound hbound))
    (12 : ENNReal)⁻¹

/-- Expand the 12-color energy into its exact six right and six reflected-left
physical reference averages. The finite partition changes no link measure. -/
theorem p4Q2BB_originalTwelveColorHaarReferenceSum_eq_rightSix_add_leftSix
    (F : Joint → ℝ) :
    (∑ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
      p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta c F) =
    (∑ c : Fin 6,
      (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
        p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c F) +
    (∑ c : Fin 6,
      (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
        p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta c F) := by
  simp [PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
    p4Q2BB_twelveColorOriginalHaarReferenceAverage, Fintype.sum_sum_type]

end
end
end MathlibAnalytic
end MGAP4D
