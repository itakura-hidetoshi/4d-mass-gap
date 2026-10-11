import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRadicalConstantSectorCriterion
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarContinuousJointMeasureIdentification
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# P4-Q2-CD: genuine ORIGINAL physical Wilson joint density has nonzero compact bounds

The exact original one-slab physical Wilson ground-state joint measure was
already identified in AU with its STRICTLY POSITIVE CONTINUOUS physical
Perron-vacuum density relative to pair Haar. On the finite-volume compact
space of full left/right spatial configurations, this density necessarily
has a strictly positive global minimum and finite global maximum.

This module establishes those constants constructively as witnesses in Lean,
for every finite H,N>0 and every beta≥0, preserving the literal original
ground-state measure and the actual compact SU(N) Haar carrier.

We lift the pointwise bounds to a true two-sided comparison of **arbitrary
nonnegative measurable observable integrals** against the same pair Haar and
original physical joint measure. Thus exceptional null sets and finite-
volume L² densities may be safely transported in BOTH directions with
explicit (nonuniform) coefficients.

IMPORTANT: m and M are allowed to depend on H,N,beta. This is NOT a
rank/volume-uniform ratio, a reverse Haar-reference Dirichlet inequality,
a proof of ker A_original=constants or a continuum Yang--Mills mass gap.
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

/-- Compactness gives uniform *positive* lower and finite upper bounds
for any continuous real density which is strictly positive everywhere. -/
private theorem p4Q2CD_compactPositiveContinuous_exists_twoBounds
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (w : X → ℝ) (hw : Continuous w) (hwpos : ∀ x, 0 < w x) :
    ∃ m M : ℝ, 0 < m ∧ ∀ x : X, m ≤ w x ∧ w x ≤ M := by
  obtain ⟨m, hm, hmin⟩ :=
    isCompact_univ.exists_forall_le' hw.continuousOn
      (by intro x _hx; exact hwpos x)
  obtain ⟨z, _hz, hmax⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hw.continuousOn
  exact ⟨m, w z, hm, fun x =>
    ⟨hmin x (Set.mem_univ x), hmax (Set.mem_univ x)⟩⟩

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
local notation "w" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
    H N hN beta hbeta

/-- An ACTUAL finite-volume positive lower and upper bound for the original
continuous Wilson--Perron physical joint density on the entire
left × right spatial configuration space. Not uniform in lattice volume. -/
theorem p4Q2CD_originalWilsonContinuousJointDensity_exists_pos_uniform_bounds :
    ∃ m M : ℝ, 0 < m ∧ ∀ z : Joint, m ≤ w z ∧ w z ≤ M := by
  have hcont : Continuous (w : Joint → ℝ) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_continuous
      H N hN beta hbeta
  have hpos : ∀ z : Joint, 0 < w z :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H N hN beta hbeta
  exact p4Q2CD_compactPositiveContinuous_exists_twoBounds w hcont hpos

/-- The ORIGINAL physical joint law is exactly pair Haar tilted by the
strictly positive continuous physical Wilson--Perron density, not by an
auxiliary Gibbs law. -/
theorem p4Q2CD_originalWilsonJointMeasure_eq_continuousPairHaar :
    μW = (μH).withDensity (fun z : Joint => ENNReal.ofReal (w z)) := by
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_eq_continuous
    H N hN beta hbeta

/-- Any nonnegative MEASURABLE observable on the finite Wilson joint
configuration space has original-joint integral uniformly sandwiched between
positive finite multiples of its pair-Haar integral. The constants are
actual positive compact witnesses, never new hypotheses. -/
theorem p4Q2CD_originalWilsonJoint_lintegral_twoSided_bound
    (F : Joint → ENNReal) (hF : Measurable F) :
    ∃ m M : ℝ, 0 < m ∧
      ENNReal.ofReal m * (∫⁻ z, F z ∂μH) ≤ (∫⁻ z, F z ∂μW) ∧
      (∫⁻ z, F z ∂μW) ≤ ENNReal.ofReal M * (∫⁻ z, F z ∂μH) := by
  obtain ⟨m, M, hm, hbounds⟩ :=
    p4Q2CD_originalWilsonContinuousJointDensity_exists_pos_uniform_bounds
      H N hN beta hbeta
  have hw : Measurable (fun z : Joint => ENNReal.ofReal (w z)) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_continuous
      H N hN beta hbeta).measurable.ennreal_ofReal
  have hrewrite :
      (∫⁻ z, F z ∂μW) =
        ∫⁻ z, ENNReal.ofReal (w z) * F z ∂μH := by
    rw [p4Q2CD_originalWilsonJointMeasure_eq_continuousPairHaar]
    exact lintegral_withDensity_eq_lintegral_mul μH hw hF
  refine ⟨m, M, hm, ?_, ?_⟩
  · rw [hrewrite]
    calc
      ENNReal.ofReal m * (∫⁻ z, F z ∂μH) =
          ∫⁻ z, ENNReal.ofReal m * F z ∂μH :=
        (lintegral_const_mul _ hF).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (w z) * F z ∂μH := by
        apply lintegral_mono
        intro z
        calc
          ENNReal.ofReal m * F z = F z * ENNReal.ofReal m := mul_comm _ _
          _ ≤ F z * ENNReal.ofReal (w z) :=
            mul_le_mul_right (ENNReal.ofReal_le_ofReal (hbounds z).1) _
          _ = ENNReal.ofReal (w z) * F z := mul_comm _ _
  · rw [hrewrite]
    calc
      (∫⁻ z, ENNReal.ofReal (w z) * F z ∂μH) ≤
          ∫⁻ z, ENNReal.ofReal M * F z ∂μH := by
        apply lintegral_mono
        intro z
        calc
          ENNReal.ofReal (w z) * F z = F z * ENNReal.ofReal (w z) := mul_comm _ _
          _ ≤ F z * ENNReal.ofReal M :=
            mul_le_mul_right (ENNReal.ofReal_le_ofReal (hbounds z).2) _
          _ = ENNReal.ofReal M * F z := mul_comm _ _
      _ = ENNReal.ofReal M * (∫⁻ z, F z ∂μH) :=
        lintegral_const_mul _ hF

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
