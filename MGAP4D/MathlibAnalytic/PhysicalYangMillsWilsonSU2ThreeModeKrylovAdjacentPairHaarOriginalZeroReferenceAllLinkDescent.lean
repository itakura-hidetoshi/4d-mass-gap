import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalJointAENullEquivalence
import Mathlib.Tactic

/-!
# P4-Q2-CF: literal Wilson Haar zero reference descends to EACH physical link

The ORIGINAL physical Wilson Haar reference (BD) is the real part of an
ENNReal sum over exactly twelve right/left physical spatial colors, each of
which is a positive cardinal-normalized sum of the actual local, strictly
mass-weighted, exp(-32*beta) Haar-fiber variances (AZ, BA, BB).

At the bounded strongly measurable ORIGINAL Wilson core the full reference
is known finite (BD). We now prove its zero energy is equivalent to ZERO
reference for EVERY right and left link in EVERY true six-color class.
This is literal, quantitative-free linkwise descent, not a new reference
or a fake finite spatial system. It also applies to genuine BR core L²
images annihilated by the BY Wilson Riesz operator.

The next open step is to turn each vanishing original mass-weighted integral
into outer-a.e. vanishing link Haar variance and paste the coordinate fibers.
No unproved reverse Poincare inequality, global kernel identity or continuum
mass-gap assertion is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

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

/-- A finite sum of ENNReal nonnegative terms can vanish only if each
term vanishes. This fact is used only on the LITERAL Wilson physical
color/link sums, without changing either the law or the weighting. -/
private theorem p4Q2CF_fintype_sum_zero_each
    {ι : Type*} [Fintype ι] (a : ι → ENNReal)
    (h : (∑ i, a i) = 0) (i : ι) : a i = 0 := by
  have hle : a i ≤ ∑ j, a j :=
    Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)
  rw [h] at hle
  exact le_antisymm hle bot_le

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Core" =>
  p4Q2BP_originalBoundedStronglyMeasurableCore H N
local notation "C12" =>
  PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor
local notation "Joint" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "T" =>
  p4Q2BR_originalCoreToPhysicalL2Linear H N hN beta hbeta
local notation "Img" => LinearMap.range T
local notation "W" =>
  p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta

/-- Vanishing of the LITERAL original mass-weighted twelve-color reference
forces zero energy separately in EVERY actual right and left color. -/
theorem p4Q2CF_originalCoreZero_implies_each_color
    (F : Core)
    (hzero : p4Q2BP_originalCoreReference H N hN beta hbeta F = 0)
    (c : C12) :
    p4Q2BB_twelveColorOriginalHaarReferenceAverage
      H N hN beta hbeta c F.1 = 0 := by
  obtain ⟨hF, ⟨bound, hbound⟩⟩ := F.property
  have htop :=
    p4Q2BD_originalWilsonTwelveColorHaarReference_ne_top
      H N hN beta hbeta F.1 hF bound hbound
  have hsum :
      (∑ d : C12,
        p4Q2BB_twelveColorOriginalHaarReferenceAverage
          H N hN beta hbeta d F.1) = 0 := by
    change (∑ d : C12,
      p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta d F.1).toReal = 0 at hzero
    exact (ENNReal.toReal_eq_zero_iff.mp hzero).resolve_right htop
  exact p4Q2CF_fintype_sum_zero_each
    (fun d : C12 =>
      p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta d F.1) hsum c

/-- Vanishing of one genuine RIGHT color Haar reference implies every
physical right-link mass-weighted original Haar fiber reference inside
that color is zero, not merely that their mean is small. -/
theorem p4Q2CF_originalCoreZero_implies_right_link
    (F : Core)
    (hzero : p4Q2BP_originalCoreReference H N hN beta hbeta F = 0)
    (color : Fin 6) (e : p4Q2BA_ColorLinks H color) :
    p4Q2AZ_originalJointHaarReferenceEnergy
      H N hN beta hbeta e.1 F.1 = 0 := by
  have hc := p4Q2CF_originalCoreZero_implies_each_color
    H N hN beta hbeta F hzero (Sum.inl color)
  change (Fintype.card (p4Q2BA_ColorLinks H color) : ENNReal)⁻¹ *
      p4Q2BA_colorAllLinkHaarReferenceSum
        H N hN beta hbeta color F.1 = 0 at hc
  have hcoeff :
      (Fintype.card (p4Q2BA_ColorLinks H color) : ENNReal)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (by finiteness)
  have hsum :
      p4Q2BA_colorAllLinkHaarReferenceSum
        H N hN beta hbeta color F.1 = 0 :=
    (mul_eq_zero.mp hc).resolve_left hcoeff
  change (∑ e' : p4Q2BA_ColorLinks H color,
    p4Q2AZ_originalJointHaarReferenceEnergy
      H N hN beta hbeta e'.1 F.1) = 0 at hsum
  exact p4Q2CF_fintype_sum_zero_each
    (fun e' : p4Q2BA_ColorLinks H color =>
      p4Q2AZ_originalJointHaarReferenceEnergy
        H N hN beta hbeta e'.1 F.1) hsum e

/-- Vanishing of one genuine LEFT color Haar reference implies zero
original Haar fiber reference for every actual left link in the color.
The left reference is the actual endpoint-swapped physical Wilson law. -/
theorem p4Q2CF_originalCoreZero_implies_left_link
    (F : Core)
    (hzero : p4Q2BP_originalCoreReference H N hN beta hbeta F = 0)
    (color : Fin 6) (e : p4Q2BA_ColorLinks H color) :
    p4Q2BB_originalLeftLinkHaarReferenceEnergy
      H N hN beta hbeta e.1 F.1 = 0 := by
  have hc := p4Q2CF_originalCoreZero_implies_each_color
    H N hN beta hbeta F hzero (Sum.inr color)
  change (Fintype.card (p4Q2BA_ColorLinks H color) : ENNReal)⁻¹ *
      p4Q2BB_leftColorAllLinkHaarReferenceSum
        H N hN beta hbeta color F.1 = 0 at hc
  have hcoeff :
      (Fintype.card (p4Q2BA_ColorLinks H color) : ENNReal)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (by finiteness)
  have hsum :
      p4Q2BB_leftColorAllLinkHaarReferenceSum
        H N hN beta hbeta color F.1 = 0 :=
    (mul_eq_zero.mp hc).resolve_left hcoeff
  change (∑ e' : p4Q2BA_ColorLinks H color,
    p4Q2BB_originalLeftLinkHaarReferenceEnergy
      H N hN beta hbeta e'.1 F.1) = 0 at hsum
  exact p4Q2CF_fintype_sum_zero_each
    (fun e' : p4Q2BA_ColorLinks H color =>
      p4Q2BB_originalLeftLinkHaarReferenceEnergy
        H N hN beta hbeta e'.1 F.1) hsum e

/-- Exact core characterization: original Wilson Haar total reference
vanishes iff EACH right and left actual mass-weighted Haar link reference
vanishes. The reverse is pure finite nonnegative sum reconstruction. -/
theorem p4Q2CF_originalCoreZero_iff_all_links
    (F : Core) :
    p4Q2BP_originalCoreReference H N hN beta hbeta F = 0 ↔
      (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
        p4Q2AZ_originalJointHaarReferenceEnergy
          H N hN beta hbeta e.1 F.1 = 0) ∧
      (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
        p4Q2BB_originalLeftLinkHaarReferenceEnergy
          H N hN beta hbeta e.1 F.1 = 0) := by
  constructor
  · intro h
    exact ⟨p4Q2CF_originalCoreZero_implies_right_link H N hN beta hbeta F h,
      p4Q2CF_originalCoreZero_implies_left_link H N hN beta hbeta F h⟩
  · rintro ⟨hr, hl⟩
    have hcol (c : C12) :
        p4Q2BB_twelveColorOriginalHaarReferenceAverage
          H N hN beta hbeta c F.1 = 0 := by
      cases c with
      | inl color =>
          change (Fintype.card (p4Q2BA_ColorLinks H color) : ENNReal)⁻¹ *
            (∑ e : p4Q2BA_ColorLinks H color,
              p4Q2AZ_originalJointHaarReferenceEnergy
                H N hN beta hbeta e.1 F.1) = 0
          rw [Finset.sum_eq_zero (fun e _ => hr color e), mul_zero]
      | inr color =>
          change (Fintype.card (p4Q2BA_ColorLinks H color) : ENNReal)⁻¹ *
            (∑ e : p4Q2BA_ColorLinks H color,
              p4Q2BB_originalLeftLinkHaarReferenceEnergy
                H N hN beta hbeta e.1 F.1) = 0
          rw [Finset.sum_eq_zero (fun e _ => hl color e), mul_zero]
    change (∑ c : C12,
      p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta c F.1).toReal = 0
    simp [hcol]

/-- If a REAL Wilson ground-state L² bounded-core image is in the
ACTUAL original Wilson Riesz kernel, then EVERY original right/left
mass-weighted Haar fiber reference at its chosen bounded representative
vanishes. This is a statement on the true range, NOT on arbitrary raw L²
representatives (which remain an explicit future step). -/
theorem p4Q2CF_originalRieszCoreKernel_implies_all_link_zero
    (x : Img) (hx : W (x : J) = 0) :
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      p4Q2AZ_originalJointHaarReferenceEnergy
        H N hN beta hbeta e.1
          (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1 = 0) ∧
    (∀ (color : Fin 6) (e : p4Q2BA_ColorLinks H color),
      p4Q2BB_originalLeftLinkHaarReferenceEnergy
        H N hN beta hbeta e.1
          (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x).1 = 0) := by
  have hQ : p4Q2BX_originalFullJointQuadratic H N hN beta hbeta (x : J) = 0 :=
    (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
      H N hN beta hbeta (x : J)).2 hx
  rw [p4Q2BX_originalFullJointQuadratic_on_range] at hQ
  exact (p4Q2CF_originalCoreZero_iff_all_links H N hN beta hbeta
    (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x)).1 hQ

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
