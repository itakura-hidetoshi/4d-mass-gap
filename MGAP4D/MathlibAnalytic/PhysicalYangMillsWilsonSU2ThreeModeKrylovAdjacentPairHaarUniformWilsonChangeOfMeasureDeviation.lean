import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarGlobalMeanPoincare
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFiniteVolumeLinkMassLowerBound
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# P4-Q2-DE: simultaneous finite-volume Wilson / pair-Haar change-of-measure bounds

DC proved the genuine independent pair-Haar all-link global-mean Poincare
inequality with reference coefficient one. CP proved that each genuine
original Wilson link Haar reference has a positive finite-volume fiber-mass
floor. These are not yet a direct reverse bound on the ORIGINAL Wilson
joint-L² quadratic energy.

CD had proved finite-volume density bounds m <= rho <= M, as well as
an existential two-sided lintegral inequality where the witnesses were
chosen AFTER fixing a measurable observable. Here we explicitly choose
ONE pair (m,M) from the ACTUAL continuous Perron-vacuum Wilson density,
and prove that this SAME pair works SIMULTANEOUSLY for EVERY nonnegative
measurable test observable. This quantifier strengthening is necessary
when the observable varies with the centering constant or a link.

Specialize the uniform comparison to the true squared centered
real observables, for ALL real centers at once, and in particular
the ACTUAL independent pair-Haar global mean used by DC.

All measures refer to the original physical left/right joint carrier;
no synthetic Gibbs density or replacement Wilson law is introduced.
The constants are positive/finite-volume but may depend on H,N,beta.
The reverse Wilson Haar-reference comparison, a volume-uniform gap
and the continuum Yang--Mills mass gap remain separate obligations.
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

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "muWilson" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
local notation "rho" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
    H N hN beta hbeta

/-- The actual normalized physical Wilson joint law admits ONE positive
finite-volume Haar density floor and ONE finite ceiling, simultaneously
for ALL nonnegative measurable functions. No observable-dependent choice
of bounds is needed. -/
theorem p4Q2DE_originalWilsonJoint_allLintegrals_uniform_density_sandwich :
    ∃ m M : ℝ, 0 < m ∧
      ∀ (F : Joint → ENNReal), Measurable F →
        ENNReal.ofReal m * (∫⁻ z, F z ∂muPair) ≤
          (∫⁻ z, F z ∂muWilson) ∧
        (∫⁻ z, F z ∂muWilson) ≤
          ENNReal.ofReal M * (∫⁻ z, F z ∂muPair) := by
  obtain ⟨m, M, hm, hbounds⟩ :=
    p4Q2CD_originalWilsonContinuousJointDensity_exists_pos_uniform_bounds
      H N hN beta hbeta
  have hrho : Measurable (fun z : Joint => ENNReal.ofReal (rho z)) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_continuous
      H N hN beta hbeta).measurable.ennreal_ofReal
  refine ⟨m, M, hm, ?_⟩
  intro F hF
  have hrewrite :
      (∫⁻ z, F z ∂muWilson) =
        ∫⁻ z, ENNReal.ofReal (rho z) * F z ∂muPair := by
    rw [p4Q2CD_originalWilsonJointMeasure_eq_continuousPairHaar]
    exact lintegral_withDensity_eq_lintegral_mul muPair hrho hF
  constructor
  · rw [hrewrite]
    calc
      ENNReal.ofReal m * (∫⁻ z, F z ∂muPair) =
          ∫⁻ z, ENNReal.ofReal m * F z ∂muPair :=
        (lintegral_const_mul _ hF).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (rho z) * F z ∂muPair := by
        apply lintegral_mono
        intro z
        calc
          ENNReal.ofReal m * F z = F z * ENNReal.ofReal m := mul_comm _ _
          _ ≤ F z * ENNReal.ofReal (rho z) :=
            mul_le_mul_right (ENNReal.ofReal_le_ofReal (hbounds z).1) _
          _ = ENNReal.ofReal (rho z) * F z := mul_comm _ _
  · rw [hrewrite]
    calc
      (∫⁻ z, ENNReal.ofReal (rho z) * F z ∂muPair) ≤
          ∫⁻ z, ENNReal.ofReal M * F z ∂muPair := by
        apply lintegral_mono
        intro z
        calc
          ENNReal.ofReal (rho z) * F z = F z * ENNReal.ofReal (rho z) :=
            mul_comm _ _
          _ ≤ F z * ENNReal.ofReal M :=
            mul_le_mul_right (ENNReal.ofReal_le_ofReal (hbounds z).2) _
          _ = ENNReal.ofReal M * F z := mul_comm _ _
      _ = ENNReal.ofReal M * (∫⁻ z, F z ∂muPair) :=
        lintegral_const_mul _ hF

/-- With the SAME finite-volume density constants, compare the squared
deviations of every strongly measurable physical observable about EVERY
real center, on the TRUE original Wilson and pair-Haar probability laws.
Both quantifiers F and c occur AFTER the choice of m and M. -/
theorem p4Q2DE_originalWilsonJoint_allSquaredDeviations_uniform_sandwich :
    ∃ m M : ℝ, 0 < m ∧
      ∀ (F : Joint → ℝ), StronglyMeasurable F → ∀ c : ℝ,
        ENNReal.ofReal m *
          (∫⁻ z, ENNReal.ofReal ((F z - c) ^ 2) ∂muPair) ≤
          (∫⁻ z, ENNReal.ofReal ((F z - c) ^ 2) ∂muWilson) ∧
        (∫⁻ z, ENNReal.ofReal ((F z - c) ^ 2) ∂muWilson) ≤
          ENNReal.ofReal M *
            (∫⁻ z, ENNReal.ofReal ((F z - c) ^ 2) ∂muPair) := by
  obtain ⟨m, M, hm, hglobal⟩ :=
    p4Q2DE_originalWilsonJoint_allLintegrals_uniform_density_sandwich
      H N hN beta hbeta
  refine ⟨m, M, hm, ?_⟩
  intro F hF c
  have hmeas : Measurable
      (fun z : Joint => ENNReal.ofReal ((F z - c) ^ 2)) :=
    ((hF.measurable.sub measurable_const).pow_const 2).ennreal_ofReal
  exact hglobal (fun z : Joint => ENNReal.ofReal ((F z - c) ^ 2)) hmeas

/-- The SAME measure comparison is valid when the center is the actual
GLOBAL INDEPENDENT pair-Haar expectation appearing in DC. The original
physical Wilson density, not a surrogate fiber probability, is used. -/
theorem p4Q2DE_originalWilsonJoint_pairHaarGlobalMean_squaredDeviation_sandwich
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    ∃ m M : ℝ, 0 < m ∧
      ENNReal.ofReal m *
        (∫⁻ z, ENNReal.ofReal
          ((F z - (∫ t : Joint, F t ∂muPair)) ^ 2) ∂muPair) ≤
        (∫⁻ z, ENNReal.ofReal
          ((F z - (∫ t : Joint, F t ∂muPair)) ^ 2) ∂muWilson) ∧
      (∫⁻ z, ENNReal.ofReal
        ((F z - (∫ t : Joint, F t ∂muPair)) ^ 2) ∂muWilson) ≤
        ENNReal.ofReal M *
          (∫⁻ z, ENNReal.ofReal
            ((F z - (∫ t : Joint, F t ∂muPair)) ^ 2) ∂muPair) := by
  obtain ⟨m, M, hm, hall⟩ :=
    p4Q2DE_originalWilsonJoint_allSquaredDeviations_uniform_sandwich
      H N hN beta hbeta
  exact ⟨m, M, hm, hall F hF (∫ t : Joint, F t ∂muPair)⟩

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
