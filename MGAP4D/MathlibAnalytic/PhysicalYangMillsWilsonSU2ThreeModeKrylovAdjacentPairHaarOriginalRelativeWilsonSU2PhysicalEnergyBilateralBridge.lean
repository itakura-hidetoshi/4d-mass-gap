import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2PhysicalOffColorD12Support
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRieszOrthogonalSpectrum
import Mathlib.Tactic

/-!
# P4-Q2-EO: same SU(2) physical Wilson witness, distinct AW and D12 energies

This file compares the actual original Wilson full-joint L² Haar-reference
Riesz quadratic and the distinct normalized interacting Wilson conditional
twelve-color physical Dirichlet energy on ONE concrete gauge-invariant
SU(2) relative-link observable.

EL and EN give genuinely separate selected-link/selected-color equalities.
BZ supplies the original Wilson one-direction inequality; DV plus BF supply
the genuine finite-volume positive reverse coefficient. None of these
identify the operators or replace the Wilson law with independent pair-Haar.

No estimate uniform in spatial volume, coupling, or lattice spacing is claimed.
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

section SamePhysicalWitness

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

/-- Genuine finite-H upper energy comparison, now evaluated on the
actual selected TWO interacting Wilson physical color defects.
The factor twelve from BZ exactly cancels the native EN normalization. -/
theorem p4Q2EO_SU2_originalRiesz_le_twoSelectedPhysicalDefects
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    Q beta hbeta (W beta hbeta e) ≤
      ‖W beta hbeta e -
        P12 beta hbeta (Sum.inl (kappa (col e))) (W beta hbeta e)‖ ^ 2 +
      ‖W beta hbeta e -
        P12 beta hbeta (Sum.inr (kappa (col e))) (W beta hbeta e)‖ ^ 2 := by
  have hBound :=
    p4Q2BZ_originalQuadratic_le_twelve_physicalEnergy
      H 2 (Nat.zero_lt_succ 1) beta hbeta (W beta hbeta e)
  calc
    Q beta hbeta (W beta hbeta e) ≤
        (12 : ℝ) * E beta hbeta (W beta hbeta e) := hBound
    _ = _ := by
      rw [p4Q2EN_SU2_originalPhysicalD12_eq_selectedTwo]
      norm_num

/-- The independent DV/BF finite-volume Wilson coercivity input gives a
positive reverse coefficient on exactly this physical SU(2) witness.
The coefficient may depend on H and beta. -/
theorem p4Q2EO_SU2_physicalD12_le_originalRiesz_positiveCoefficient
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    ∃ κ : ℝ, 0 < κ ∧
      κ * E beta hbeta (W beta hbeta e) ≤
        Q beta hbeta (W beta hbeta e) := by
  obtain ⟨κ, hκ, hDV⟩ :=
    p4Q2DV_originalWilsonFullJointRieszQuadratic_coercive
      H 2 (Nat.zero_lt_succ 1) beta hbeta
  refine ⟨κ, hκ, ?_⟩
  have hEnergy :=
    p4Q2BF_physicalTwelveResidualEnergy_le_centeredJointNormSq
      H 2 (Nat.zero_lt_succ 1) beta hbeta (W beta hbeta e)
  exact (mul_le_mul_of_nonneg_left hEnergy hκ.le).trans
    (hDV (W beta hbeta e))

/-- A genuine, finite-volume bilateral comparison on the same observable;
the right side is explicitly the sum of the TWO selected physical defects.
No pair-Haar or AW = D12 substitution. -/
theorem p4Q2EO_SU2_originalRiesz_physicalD12_selectedBilateral
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    ∃ κ : ℝ, 0 < κ ∧
      κ * E beta hbeta (W beta hbeta e) ≤
        Q beta hbeta (W beta hbeta e) ∧
      Q beta hbeta (W beta hbeta e) ≤
        ‖W beta hbeta e -
          P12 beta hbeta (Sum.inl (kappa (col e))) (W beta hbeta e)‖ ^ 2 +
        ‖W beta hbeta e -
          P12 beta hbeta (Sum.inr (kappa (col e))) (W beta hbeta e)‖ ^ 2 := by
  obtain ⟨κ, hκ, hLower⟩ :=
    p4Q2EO_SU2_physicalD12_le_originalRiesz_positiveCoefficient H beta hbeta e
  exact ⟨κ, hκ, hLower,
    p4Q2EO_SU2_originalRiesz_le_twoSelectedPhysicalDefects H beta hbeta e⟩

/-- Both exact original-law identities are retained simultaneously:
EL's original Haar reference has the inverse ACTUAL selected color link
cardinality, while EN's genuinely interacting D12 has the inverse twelve.
These are equalities for DIFFERENT energy functionals, not AW = D12. -/
theorem p4Q2EO_SU2_exactOriginalHaarAndInteractingD12_twoSupport
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    Q beta hbeta (W beta hbeta e) =
      ((Fintype.card (p4Q2BA_ColorLinks H
          (kappa (col e))) : ENNReal)⁻¹ *
          p4Q2AZ_originalJointHaarReferenceEnergy
            H 2 (Nat.zero_lt_succ 1) beta hbeta e
            (fun z : Joint => F e z) +
       (Fintype.card (p4Q2BA_ColorLinks H
          (kappa (col e))) : ENNReal)⁻¹ *
          p4Q2BB_originalLeftLinkHaarReferenceEnergy
            H 2 (Nat.zero_lt_succ 1) beta hbeta e
            (fun z : Joint => F e z)).toReal ∧
    E beta hbeta (W beta hbeta e) =
      (12 : ℝ)⁻¹ *
        (‖W beta hbeta e -
          P12 beta hbeta (Sum.inl (kappa (col e))) (W beta hbeta e)‖ ^ 2 +
         ‖W beta hbeta e -
          P12 beta hbeta (Sum.inr (kappa (col e))) (W beta hbeta e)‖ ^ 2) := by
  constructor
  · exact p4Q2EL_SU2_originalWilsonPhysicalRieszQuadratic_eq_twoSelected
      H beta hbeta e
  · exact p4Q2EN_SU2_originalPhysicalD12_eq_selectedTwo H beta hbeta e

end SamePhysicalWitness
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EO_SU2_originalRiesz_le_twoSelectedPhysicalDefects
#print axioms MGAP4D.MathlibAnalytic.p4Q2EO_SU2_physicalD12_le_originalRiesz_positiveCoefficient
#print axioms MGAP4D.MathlibAnalytic.p4Q2EO_SU2_originalRiesz_physicalD12_selectedBilateral
#print axioms MGAP4D.MathlibAnalytic.p4Q2EO_SU2_exactOriginalHaarAndInteractingD12_twoSupport
