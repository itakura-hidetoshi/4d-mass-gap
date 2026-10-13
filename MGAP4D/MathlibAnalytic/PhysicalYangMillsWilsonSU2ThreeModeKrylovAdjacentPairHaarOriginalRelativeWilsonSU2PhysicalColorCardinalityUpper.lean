import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2SelectedHaarPhysicalColorRatio
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic

/-!
# P4-Q2-EQ: sharp selected-color cardinality upper comparison

EP proved EACH genuine original Wilson mass-weighted selected right/left Haar
one-link reference energy is bounded by the corresponding actual interacting
physical Wilson six-color conditional squared residual. EL identifies the
original full-joint-L² Haar Riesz quadratic with exactly those TWO original
references, weighted by the inverse ACTUAL selected physical color link count.

Consequently, on the SAME gauge-invariant SU(2) relative-link physical Wilson
joint-L² class, the old upper bound QW <= 12*E12 improves quantitatively to

QW <= (12 / L_(selected color)(H))*E12.

This is a finite-volume witness-specific upper bound for distinct original AW
and interacting D12, not a new infinite-volume or continuum Yang–Mills mass gap.
Crucially it gives a proved necessary upper bound for ANY proposed relative
AW/D12 lower comparison coefficient, directly on a genuine gauge-invariant
Wilson observable, without an arbitrary nonnegative link-weight spike.
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

section ActualSelectedColorCardinality

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "col" => periodicHypercubicEvenSpatialSliceLinkColor H
local notation "kappa" => periodicHypercubicEvenGroundStateSpatialColorEquivFin
local notation "F" => p4Q2EE_SU2_relativeWilsonEnergyBCF H
local notation "W" => p4Q2EE_SU2_physicalWilsonJointL2 H
local notation "Q" => p4Q2BX_originalFullJointQuadratic H 2 (Nat.zero_lt_succ 1)
local notation "E" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H 2 (Nat.zero_lt_succ 1)
local notation "P12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
    H 2 (Nat.zero_lt_succ 1)

/-- The exact positive physical count of original spatial links of the
selected six-color of a genuine physical SU(2) relative link e. -/
noncomputable def p4Q2EQ_SU2_selectedPhysicalColorLinkCard (e : Link) : ℕ :=
  Fintype.card (p4Q2BA_ColorLinks H (kappa (col e)))

theorem p4Q2EQ_SU2_selectedPhysicalColorLinkCard_pos (e : Link) :
    0 < p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e := by
  unfold p4Q2EQ_SU2_selectedPhysicalColorLinkCard
  letI : Nonempty (p4Q2BA_ColorLinks H (kappa (col e))) :=
    p4Q2BA_colorLinks_nonempty H (kappa (col e))
  exact Fintype.card_pos

/-- The true original Wilson selected reference has a STRICTER physical
upper comparison carrying 1 / card(selected color), not just EP's 1.
Both selected ORIGINAL Haar refs are finite because EP supplies genuine
bounds by finite REAL Wilson conditional squared residuals. -/
theorem p4Q2EQ_SU2_selectedHaarReal_le_invColorCard_mul_physicalTwoColor
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e ≤
      (p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e : ℝ)⁻¹ *
        p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e := by
  let n : ℕ := p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e
  let r : ENNReal :=
    p4Q2AZ_originalJointHaarReferenceEnergy
      H 2 (Nat.zero_lt_succ 1) beta hbeta e
      (fun z : Joint => F e z)
  let l : ENNReal :=
    p4Q2BB_originalLeftLinkHaarReferenceEnergy
      H 2 (Nat.zero_lt_succ 1) beta hbeta e
      (fun z : Joint => F e z)
  let rSq : ℝ :=
    ‖W beta hbeta e -
      P12 beta hbeta (Sum.inl (kappa (col e))) (W beta hbeta e)‖ ^ 2
  let lSq : ℝ :=
    ‖W beta hbeta e -
      P12 beta hbeta (Sum.inr (kappa (col e))) (W beta hbeta e)‖ ^ 2
  obtain ⟨hR, hL⟩ :=
    p4Q2EP_SU2_bothSelectedOriginalHaarRefs_le_physicalColorDefects
      H beta hbeta e
  change r ≤ ENNReal.ofReal rSq at hR
  change l ≤ ENNReal.ofReal lSq at hL
  have hrNN : 0 ≤ rSq := by dsimp [rSq]; positivity
  have hlNN : 0 ≤ lSq := by dsimp [lSq]; positivity
  have hrFin : r ≠ ∞ := ne_top_of_le_ne_top (by simp) hR
  have hlFin : l ≠ ∞ := ne_top_of_le_ne_top (by simp) hL
  have hn : 0 < n :=
    p4Q2EQ_SU2_selectedPhysicalColorLinkCard_pos H e
  have hnENN : (0 : ENNReal) < (n : ENNReal) := by
    exact_mod_cast hn
  have hnInvFin : (n : ENNReal)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (ne_of_gt hnENN)
  have hrProductFin : (n : ENNReal)⁻¹ * r ≠ ∞ :=
    (ENNReal.mul_lt_top hnInvFin.lt_top hrFin.lt_top).ne
  have hlProductFin : (n : ENNReal)⁻¹ * l ≠ ∞ :=
    (ENNReal.mul_lt_top hnInvFin.lt_top hlFin.lt_top).ne
  have hrReal : r.toReal ≤ rSq := by
    calc
      r.toReal ≤ (ENNReal.ofReal rSq).toReal :=
        ENNReal.toReal_mono (by simp) hR
      _ = rSq := ENNReal.toReal_ofReal hrNN
  have hlReal : l.toReal ≤ lSq := by
    calc
      l.toReal ≤ (ENNReal.ofReal lSq).toReal :=
        ENNReal.toReal_mono (by simp) hL
      _ = lSq := ENNReal.toReal_ofReal hlNN
  have hExact :
      p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e =
        (n : ℝ)⁻¹ * (r.toReal + l.toReal) := by
    change ((n : ENNReal)⁻¹ * r + (n : ENNReal)⁻¹ * l).toReal = _
    rw [ENNReal.toReal_add hrProductFin hlProductFin]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    ring
  have hInvNN : 0 ≤ (n : ℝ)⁻¹ := by positivity
  calc
    p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e =
        (n : ℝ)⁻¹ * (r.toReal + l.toReal) := hExact
    _ ≤ (n : ℝ)⁻¹ * (rSq + lSq) :=
      mul_le_mul_of_nonneg_left (add_le_add hrReal hlReal) hInvNN
    _ = (p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e : ℝ)⁻¹ *
        p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e := by
      rfl

/-- The original physical-Wilson Haar Riesz quadratic on this SAME
gauge-invariant SU(2) witness is at most 12/L_c(H) times the
SEPARATELY DEFINED genuine interacting D12 physical conditional energy.
This strengthens the generic finite-volume BZ operator upper bound
ON THIS WITNESS; it does not identify AW with D12. -/
theorem p4Q2EQ_SU2_originalRiesz_le_twelve_div_selectedColorCard_mul_physicalD12
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    Q beta hbeta (W beta hbeta e) ≤
      ((12 : ℝ) / (p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e : ℝ)) *
        E beta hbeta (W beta hbeta e) := by
  obtain ⟨hQ, hE⟩ :=
    p4Q2EP_SU2_exactSelectedHaarAndPhysicalColorIdentities
      H beta hbeta e
  have hUpper :=
    p4Q2EQ_SU2_selectedHaarReal_le_invColorCard_mul_physicalTwoColor
      H beta hbeta e
  calc
    Q beta hbeta (W beta hbeta e) =
        p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e := hQ
    _ ≤ (p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e : ℝ)⁻¹ *
          p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e :=
        hUpper
    _ = ((12 : ℝ) / (p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e : ℝ)) *
          E beta hbeta (W beta hbeta e) := by
        rw [hE]
        simp only [div_eq_mul_inv]
        ring

/-- Any proposed relative Wilson AW >= κ*D12 inequality tested on this
ACTUAL physical SU(2) gauge-invariant witness necessarily has
κ <= 12/L_(selected color)(H). This imposes a concrete finite-H
cardinality constraint, not a claim about the physical D12 spectral gap
or continuum Yang–Mills. No sign assumption on κ is required. -/
theorem p4Q2EQ_SU2_anyRelativeCoefficient_le_twelve_div_selectedColorCard
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link)
    (κ : ℝ)
    (hLower :
      κ * E beta hbeta (W beta hbeta e) ≤
        Q beta hbeta (W beta hbeta e)) :
    κ ≤ (12 : ℝ) /
      (p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e : ℝ) := by
  have hUpper :=
    p4Q2EQ_SU2_originalRiesz_le_twelve_div_selectedColorCard_mul_physicalD12
      H beta hbeta e
  have hPos :=
    p4Q2EN_SU2_originalPhysicalD12_pos H beta hbeta e
  by_contra hNot
  have hGt :
      (12 : ℝ) /
          (p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e : ℝ) < κ :=
    lt_of_not_ge hNot
  exact (not_lt_of_ge (hLower.trans hUpper))
    (mul_lt_mul_of_pos_right hGt hPos)

/-- In particular, the GENUINE original Wilson mass/variance certificate
κ_EC(H,beta,m,M) from EC is necessarily bounded above by the explicit
12 / cardinality of this physical SU(2) selected color. It remains positive
at every fixed H; no H-uniform conclusion is assumed. -/
theorem p4Q2EQ_SU2_originalEC_coefficient_le_twelve_div_selectedColorCard
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      0 < p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M ∧
      p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M ≤
        (12 : ℝ) /
          (p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e : ℝ) := by
  obtain ⟨m, M, hm, hM, hκ, hLower⟩ :=
    p4Q2EO_SU2_physicalD12_le_originalRiesz_explicitWilsonMass
      H beta hbeta e
  exact ⟨m, M, hm, hM, hκ,
    p4Q2EQ_SU2_anyRelativeCoefficient_le_twelve_div_selectedColorCard
      H beta hbeta e
      (p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M) hLower⟩

/-- Dimensionless true Wilson witness ratio: now the UPPER bound is the
inverse genuine selected-color cardinality, not merely EP's bound 1.
The LOWER bound retains the actual EC Wilson finite-H coefficient /12.
Both residual laws and the two exact energy normalizations remain separate. -/
theorem p4Q2EQ_SU2_selectedHaar_physicalTwoColor_sharperRatio
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      0 < p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M ∧
      0 < p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e ∧
      p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M / 12 ≤
        p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e /
          p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e ∧
      p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e /
          p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e ≤
        (p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e : ℝ)⁻¹ := by
  obtain ⟨m, M, hm, hM, hκ, hPos, hLower, _⟩ :=
    p4Q2EP_SU2_selectedHaar_over_physicalTwoColor_ratio_bounds H beta hbeta e
  have hUpper :=
    p4Q2EQ_SU2_selectedHaarReal_le_invColorCard_mul_physicalTwoColor
      H beta hbeta e
  refine ⟨m, M, hm, hM, hκ, hPos, hLower, ?_⟩
  apply (div_le_iff₀ hPos).2
  exact hUpper

end ActualSelectedColorCardinality
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EQ_SU2_selectedPhysicalColorLinkCard_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2EQ_SU2_selectedHaarReal_le_invColorCard_mul_physicalTwoColor
#print axioms MGAP4D.MathlibAnalytic.p4Q2EQ_SU2_originalRiesz_le_twelve_div_selectedColorCard_mul_physicalD12
#print axioms MGAP4D.MathlibAnalytic.p4Q2EQ_SU2_anyRelativeCoefficient_le_twelve_div_selectedColorCard
#print axioms MGAP4D.MathlibAnalytic.p4Q2EQ_SU2_originalEC_coefficient_le_twelve_div_selectedColorCard
#print axioms MGAP4D.MathlibAnalytic.p4Q2EQ_SU2_selectedHaar_physicalTwoColor_sharperRatio
