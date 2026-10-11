import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalContinuousDensityFiniteVolumeSandwich
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic

/-!
# P4-Q2-CE: exact original-Wilson/physical Haar zero and finiteness transport

CD proved the actual finite-volume ORIGINAL physical Wilson ground-state
joint law has a strictly positive, finite, continuous-Perron-vacuum
density with respect to the genuine pair-Haar law. For arbitrary
nonnegative measurable observables, a two-sided integral inequality with
strictly positive finite (but volume- and beta-dependent) constants follows.

The present theorems extract the exact null and finite-moment consequences
on the SAME physical configuration space, requiring no extra integrability
assumption and no new auxiliary probability law:

* an arbitrary measurable ENNReal observable has zero literal Wilson
  joint integral iff it has zero pair-Haar integral;
* either integral is finite iff the other is finite;
* the equivalence specializes to the actual real squared-observable
  second moments, providing the precise next finite-volume L²
  admissibility bridge for fiber-nullset and Dirichlet analysis.

NO uniform-in-volume coefficients, equality of original Haar-reference
and physical E12 kernels or continuum Yang--Mills mass gap are claimed.
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

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Joint" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "μH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "μW" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta

/-- The ORIGINAL finite-volume Wilson physical ground-state joint measure
and genuine spatial pair Haar have EXACTLY THE SAME zero integrals for
arbitrary nonnegative measurable observables. -/
theorem p4Q2CE_originalWilsonJoint_lintegral_eq_zero_iff_pairHaar
    (F : Joint → ENNReal) (hF : Measurable F) :
    (∫⁻ z, F z ∂μW) = 0 ↔ (∫⁻ z, F z ∂μH) = 0 := by
  obtain ⟨m, M, hm, hLower, hUpper⟩ :=
    p4Q2CD_originalWilsonJoint_lintegral_twoSided_bound
      H N hN beta hbeta F hF
  constructor
  · intro hzero
    have hmul : ENNReal.ofReal m * (∫⁻ z, F z ∂μH) = 0 := by
      calc
        ENNReal.ofReal m * (∫⁻ z, F z ∂μH) ≤
            ∫⁻ z, F z ∂μW := hLower
        _ = 0 := hzero
      -- goal is equality, not inequality; use bottom antisymmetry below.
    exact (mul_eq_zero.mp hmul).resolve_left
      (ne_of_gt (ENNReal.ofReal_pos.mpr hm))
  · intro hzero
    have h := hUpper
    rw [hzero, mul_zero] at h
    exact le_antisymm h bot_le

/-- Neither the Wilson physical joint measure nor pair Haar gains or loses
finite nonnegative moments at fixed finite volume: strict positivity of
the lower weight prevents an infinite Haar moment from becoming finite. -/
theorem p4Q2CE_originalWilsonJoint_lintegral_lt_top_iff_pairHaar
    (F : Joint → ENNReal) (hF : Measurable F) :
    (∫⁻ z, F z ∂μW) < ∞ ↔ (∫⁻ z, F z ∂μH) < ∞ := by
  obtain ⟨m, M, hm, hLower, hUpper⟩ :=
    p4Q2CD_originalWilsonJoint_lintegral_twoSided_bound
      H N hN beta hbeta F hF
  constructor
  · intro hfinite
    by_contra hnot
    have htop : (∫⁻ z, F z ∂μH) = ∞ :=
      le_antisymm le_top (not_lt.mp hnot)
    have hmne : ENNReal.ofReal m ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hm)
    have htopW : (∫⁻ z, F z ∂μW) = ∞ := by
      apply le_antisymm le_top
      simpa only [htop, ENNReal.mul_top hmne] using hLower
    rw [htopW] at hfinite
    exact (lt_irrefl ∞) hfinite
  · intro hfinite
    exact lt_of_le_of_lt hUpper
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite)

/-- Exact finite-volume ORIGINAL Wilson vs pair-Haar equality of the
vanishing real squared-observable moments; this is an L²-geometry
statement on THE ORIGINAL joint configuration space, not an E12 claim. -/
theorem p4Q2CE_originalWilsonJoint_realSquareLIntegral_eq_zero_iff_pairHaar
    (f : Joint → ℝ) (hf : Measurable f) :
    (∫⁻ z, ENNReal.ofReal ((f z) ^ 2) ∂μW) = 0 ↔
      (∫⁻ z, ENNReal.ofReal ((f z) ^ 2) ∂μH) = 0 := by
  exact p4Q2CE_originalWilsonJoint_lintegral_eq_zero_iff_pairHaar
    H N hN beta hbeta
      (fun z => ENNReal.ofReal ((f z) ^ 2))
      ((hf.pow_const 2).ennreal_ofReal)

/-- Exact finite-volume equivalence of finite real second moments, without
assuming an a priori bounded cylinder representative on either measure. -/
theorem p4Q2CE_originalWilsonJoint_realSquareLIntegral_lt_top_iff_pairHaar
    (f : Joint → ℝ) (hf : Measurable f) :
    (∫⁻ z, ENNReal.ofReal ((f z) ^ 2) ∂μW) < ∞ ↔
      (∫⁻ z, ENNReal.ofReal ((f z) ^ 2) ∂μH) < ∞ := by
  exact p4Q2CE_originalWilsonJoint_lintegral_lt_top_iff_pairHaar
    H N hN beta hbeta
      (fun z => ENNReal.ofReal ((f z) ^ 2))
      ((hf.pow_const 2).ennreal_ofReal)

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
