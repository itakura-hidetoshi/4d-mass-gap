import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicLocalActionReindexBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectorySpecialUnitaryTwoStapleOscillationSeparationBCF
import MGAP4D.MathlibAnalytic.PeriodicHypercubicIncidentOtherEdgeClassification
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

local instance periodicSixStapleSpecialUnitaryTwoIsTopologicalGroup :
    IsTopologicalGroup (SpecialUnitaryMatrixGroup 2) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance periodicSixStapleSpecialUnitaryTwoCompactSpace :
    CompactSpace (SpecialUnitaryMatrixGroup 2) :=
  specialUnitaryGroupCompactSpace 2

/-- The concrete target used for the first actual periodic endpoint realization:
the positive axis-zero link based at the origin of the side-three four-torus. -/
def periodicHypercubicThreeOriginAxisZeroTarget :
    PeriodicHypercubicEdge 3 :=
  (0, 0)

/-- The identity `SU(2)` configuration on the side-three periodic box. -/
def periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration :
    PeriodicHypercubicEdge 3 → SpecialUnitaryMatrixGroup 2 :=
  fun _ => 1

/-- A central `Z₂` configuration selecting axis-zero links whose source-coordinate
sum is `-1` in `ZMod 3`.  On the six plaquettes incident to the origin axis-zero
target, this selects exactly the three far-side opposite axis-zero links. -/
def periodicHypercubicThreeSpecialUnitaryTwoFarSideCenterConfiguration :
    PeriodicHypercubicEdge 3 → SpecialUnitaryMatrixGroup 2 :=
  fun e =>
    if e.2 = 0 ∧ (∑ i : Fin 4, e.1 i) = (-1 : ZMod 3) then
      specialUnitaryTwoNegativeIdentity
    else
      1

@[simp]
theorem specialUnitaryTwoNegativeIdentity_inv :
    specialUnitaryTwoNegativeIdentity⁻¹ =
      specialUnitaryTwoNegativeIdentity := by
  apply Subtype.ext
  change star (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) =
    -(1 : Matrix (Fin 2) (Fin 2) ℂ)
  simp

private theorem specialUnitaryTwo_identityComplementProduct_eq_one :
    (1 : SpecialUnitaryMatrixGroup 2) * 1⁻¹ * 1⁻¹ = 1 := by
  apply Subtype.ext
  change
    (1 : Matrix (Fin 2) (Fin 2) ℂ) *
          star (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        star (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ)
  simp

private theorem specialUnitaryTwo_farCenterComplementProduct_eq_negativeIdentity :
    ((1 : SpecialUnitaryMatrixGroup 2)⁻¹ *
        specialUnitaryTwoNegativeIdentity * 1)⁻¹ =
      specialUnitaryTwoNegativeIdentity := by
  apply Subtype.ext
  change
    star
        (star (1 : Matrix (Fin 2) (Fin 2) ℂ) *
            (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      -(1 : Matrix (Fin 2) (Fin 2) ℂ)
  simp

/-- The rank-two central negative identity is distinct from the identity. -/
theorem specialUnitaryTwoNegativeIdentity_ne_one :
    specialUnitaryTwoNegativeIdentity ≠
      (1 : SpecialUnitaryMatrixGroup 2) := by
  intro h
  have h00 := congrArg
    (fun U : SpecialUnitaryMatrixGroup 2 =>
      ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0)) h
  norm_num [specialUnitaryTwoNegativeIdentity] at h00

local instance periodicSixStapleSpecialUnitaryTwoNontrivial :
    Nontrivial (SpecialUnitaryMatrixGroup 2) :=
  ⟨⟨specialUnitaryTwoNegativeIdentity, 1,
    specialUnitaryTwoNegativeIdentity_ne_one⟩⟩

private theorem zmodThree_one_ne_neg_one :
    (1 : ZMod 3) ≠ -1 := by
  native_decide

/-- Every oriented three-link complement is the identity on the identity
configuration. -/
theorem continuous_compact_oriented_isolatedTargetPlaquetteIncidence_stapleValue_identityConfiguration
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (inc : C.IsolatedTargetPlaquetteIncidence target) :
    inc.stapleValue (fun _ => 1) = 1 := by
  have hStep
      (step : FiniteOrientedBoundaryStep C.base.geometry.Edge) :
      C.base.stepValue (fun _ => 1) step = 1 := by
    cases step with
    | mk edge orientation =>
        cases orientation <;>
          simp [CompactOrientedGaugeWilsonSystem.stepValue,
            FiniteOrientedFourDimensionalPlaquetteGeometry.stepValue]
  cases inc <;>
    simp [ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.stapleValue,
      ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.targetOrientation,
      ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.rawComplement,
      hStep] <;>
    split <;> simp

/-- The concrete center configuration takes the expected value on every one of
the three explicitly enumerated non-target links of an incident plaquette. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoFarSideCenterConfiguration_incidentOtherEdge
    (nu : PeriodicHypercubicOtherAxis
      periodicHypercubicThreeOriginAxisZeroTarget.2)
    (otherSide : Bool)
    (slot : Fin 3) :
    periodicHypercubicThreeSpecialUnitaryTwoFarSideCenterConfiguration
        (periodicHypercubicIncidentOtherEdge 3
          periodicHypercubicThreeOriginAxisZeroTarget nu otherSide slot) =
      if otherSide = true ∧ slot = 2 then
        specialUnitaryTwoNegativeIdentity
      else
        1 := by
  rcases nu with ⟨nu, hnu⟩
  change nu ≠ (0 : Fin 4) at hnu
  fin_cases nu <;> simp at hnu
  all_goals
    fin_cases slot <;> cases otherSide <;>
      simp [periodicHypercubicThreeSpecialUnitaryTwoFarSideCenterConfiguration,
        periodicHypercubicThreeOriginAxisZeroTarget,
        periodicHypercubicIncidentOtherEdge,
        periodicHypercubicShift,
        periodicHypercubicUnshift,
        periodicHypercubicUnit,
        Fin.sum_univ_four,
        zmodThree_one_ne_neg_one]

/-- The actual six-slot staple family at the fixed side-three target. -/
def periodicHypercubicThreeSpecialUnitaryTwoCanonicalStapleFamily
    (A : PeriodicHypercubicEdge 3 → SpecialUnitaryMatrixGroup 2) :
    PeriodicHypercubicOtherAxis
        periodicHypercubicThreeOriginAxisZeroTarget.2 × Bool →
      SpecialUnitaryMatrixGroup 2 :=
  fun data =>
    (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
      3 2 (by norm_num) (by norm_num) 0 (by norm_num)
      periodicHypercubicThreeOriginAxisZeroTarget data).stapleValue A

/-- The identity configuration realizes six coincident identity staples. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCanonicalStapleFamily_identityConfiguration :
    periodicHypercubicThreeSpecialUnitaryTwoCanonicalStapleFamily
        periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration =
      fun _ => 1 := by
  funext data
  exact
    continuous_compact_oriented_isolatedTargetPlaquetteIncidence_stapleValue_identityConfiguration
      (periodicHypercubicSpecialUnitaryWilsonSystem
        3 2 (by norm_num) 0 (by norm_num))
      periodicHypercubicThreeOriginAxisZeroTarget
      (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
        3 2 (by norm_num) (by norm_num) 0 (by norm_num)
        periodicHypercubicThreeOriginAxisZeroTarget data)

/-- On the center configuration, the actual canonical staple is `I` on the near
side and `-I` on the far side, independently for each transverse axis. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCanonicalStapleFamily_farSideCenterConfiguration :
    periodicHypercubicThreeSpecialUnitaryTwoCanonicalStapleFamily
        periodicHypercubicThreeSpecialUnitaryTwoFarSideCenterConfiguration =
      fun data =>
        if data.2 = true then specialUnitaryTwoNegativeIdentity else 1 := by
  funext data
  rcases data with ⟨⟨nu, hnu⟩, otherSide⟩
  change nu ≠ (0 : Fin 4) at hnu
  fin_cases nu <;> simp at hnu
  all_goals
    cases otherSide <;>
      simp [periodicHypercubicThreeSpecialUnitaryTwoCanonicalStapleFamily,
        periodicHypercubicThreeOriginAxisZeroTarget,
        periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence,
        ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.stapleValue,
        ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.targetOrientation,
        ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.rawComplement,
        CompactOrientedGaugeWilsonSystem.stepValue,
        FiniteOrientedFourDimensionalPlaquetteGeometry.stepValue,
        periodicHypercubicSpecialUnitaryWilsonSystem,
        specialUnitaryContinuousCompactOrientedGaugeWilsonSystem,
        specialUnitaryCompactOrientedGaugeWilsonSystem,
        periodicHypercubicFiniteOrientedGeometry,
        periodicHypercubicIncidentPlaquette,
        periodicHypercubicAxisPairOfNe,
        periodicHypercubicPlaquetteFirstAxis,
        periodicHypercubicPlaquetteSecondAxis,
        periodicHypercubicBoundaryStep,
        periodicBoundaryStepToFinite,
        periodicOrientationToFinite,
        periodicHypercubicThreeSpecialUnitaryTwoFarSideCenterConfiguration,
        periodicHypercubicShift,
        periodicHypercubicUnshift,
        periodicHypercubicUnit,
        Fin.sum_univ_four,
        zmodThree_one_ne_neg_one] <;>
      first
      | exact specialUnitaryTwo_identityComplementProduct_eq_one
      | exact specialUnitaryTwo_farCenterComplementProduct_eq_negativeIdentity

/-- Six coincident identity staples on the actual canonical index. -/
def specialUnitaryTwoPeriodicSixSameStapleFamily :
    PeriodicHypercubicOtherAxis
        periodicHypercubicThreeOriginAxisZeroTarget.2 × Bool →
      SpecialUnitaryMatrixGroup 2 :=
  fun _ => 1

/-- Three identity/negative-identity pairs, one for each transverse axis. -/
def specialUnitaryTwoPeriodicSixSplitStapleFamily :
    PeriodicHypercubicOtherAxis
        periodicHypercubicThreeOriginAxisZeroTarget.2 × Bool →
      SpecialUnitaryMatrixGroup 2 :=
  fun data =>
    if data.2 = true then specialUnitaryTwoNegativeIdentity else 1

/-- The six coincident-staple section is six times the `SU(2)` Wilson energy. -/
theorem specialUnitaryTwoPeriodicSixSameStaple_section_apply
    (g : SpecialUnitaryMatrixGroup 2) :
    multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
        specialUnitaryTwoPeriodicSixSameStapleFamily g =
      6 * specialUnitaryWilsonPlaquetteEnergy 2 g := by
  rw [multiRightTranslateSumBCF_apply]
  simp only [specialUnitaryTwoPeriodicSixSameStapleFamily, mul_one]
  rw [Finset.sum_const, Finset.card_univ,
    periodicHypercubicCanonicalTargetPlaquetteIndex_card
      3 periodicHypercubicThreeOriginAxisZeroTarget]
  norm_num

/-- Each transverse plane contributes one complementary pair, so the split
six-staple section is the constant function six. -/
theorem specialUnitaryTwoPeriodicSixSplitStaple_section_apply
    (g : SpecialUnitaryMatrixGroup 2) :
    multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
        specialUnitaryTwoPeriodicSixSplitStapleFamily g = 6 := by
  rw [multiRightTranslateSumBCF_apply, Fintype.sum_prod_type]
  simp [specialUnitaryTwoPeriodicSixSplitStapleFamily,
    specialUnitaryWilsonPlaquetteEnergy_two_mul_negativeIdentity]
  norm_num

/-- The same-staple six-slot section is nonnegative. -/
theorem specialUnitaryTwoPeriodicSixSameStaple_section_nonneg
    (g : SpecialUnitaryMatrixGroup 2) :
    0 ≤ multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
      specialUnitaryTwoPeriodicSixSameStapleFamily g := by
  rw [specialUnitaryTwoPeriodicSixSameStaple_section_apply]
  nlinarith [specialUnitaryWilsonPlaquetteEnergy_nonneg
    (N := 2) (by norm_num) g]

/-- The same-staple six-slot section is bounded above by twelve. -/
theorem specialUnitaryTwoPeriodicSixSameStaple_section_le_twelve
    (g : SpecialUnitaryMatrixGroup 2) :
    multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
      specialUnitaryTwoPeriodicSixSameStapleFamily g ≤ 12 := by
  rw [specialUnitaryTwoPeriodicSixSameStaple_section_apply]
  nlinarith [specialUnitaryWilsonPlaquetteEnergy_le_two
    (N := 2) (by norm_num) g]

@[simp]
theorem specialUnitaryTwoPeriodicSixSameStaple_section_one :
    multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
      specialUnitaryTwoPeriodicSixSameStapleFamily
      (1 : SpecialUnitaryMatrixGroup 2) = 0 := by
  rw [specialUnitaryTwoPeriodicSixSameStaple_section_apply]
  simp

@[simp]
theorem specialUnitaryTwoPeriodicSixSameStaple_section_negativeIdentity :
    multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
      specialUnitaryTwoPeriodicSixSameStapleFamily
      specialUnitaryTwoNegativeIdentity = 12 := by
  rw [specialUnitaryTwoPeriodicSixSameStaple_section_apply]
  norm_num

/-- The six coincident identity staples have exact oscillation twelve. -/
theorem specialUnitaryTwoPeriodicSixSameStaple_oscillation_eq_twelve :
    multiRightTranslateSumOscillationBCF specialUnitaryTwoWilsonEnergyBCF
      specialUnitaryTwoPeriodicSixSameStapleFamily = 12 := by
  let F := multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
    specialUnitaryTwoPeriodicSixSameStapleFamily
  have hGreatest : IsGreatest (Set.range F) 12 := by
    constructor
    · exact ⟨specialUnitaryTwoNegativeIdentity,
        specialUnitaryTwoPeriodicSixSameStaple_section_negativeIdentity⟩
    · intro y hy
      rcases hy with ⟨g, rfl⟩
      exact specialUnitaryTwoPeriodicSixSameStaple_section_le_twelve g
  have hLeast : IsLeast (Set.range F) 0 := by
    constructor
    · exact ⟨(1 : SpecialUnitaryMatrixGroup 2),
        specialUnitaryTwoPeriodicSixSameStaple_section_one⟩
    · intro y hy
      rcases hy with ⟨g, rfl⟩
      exact specialUnitaryTwoPeriodicSixSameStaple_section_nonneg g
  unfold multiRightTranslateSumOscillationBCF
  change sSup (Set.range F) - sInf (Set.range F) = 12
  rw [hGreatest.csSup_eq, hLeast.csInf_eq]
  norm_num

/-- The three complementary center pairs have zero oscillation. -/
theorem specialUnitaryTwoPeriodicSixSplitStaple_oscillation_eq_zero :
    multiRightTranslateSumOscillationBCF specialUnitaryTwoWilsonEnergyBCF
      specialUnitaryTwoPeriodicSixSplitStapleFamily = 0 := by
  let F := multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
    specialUnitaryTwoPeriodicSixSplitStapleFamily
  have hValue : ∀ g : SpecialUnitaryMatrixGroup 2, F g = 6 := by
    intro g
    exact specialUnitaryTwoPeriodicSixSplitStaple_section_apply g
  have hGreatest : IsGreatest (Set.range F) 6 := by
    constructor
    · exact ⟨(1 : SpecialUnitaryMatrixGroup 2), hValue 1⟩
    · intro y hy
      rcases hy with ⟨g, rfl⟩
      rw [hValue g]
  have hLeast : IsLeast (Set.range F) 6 := by
    constructor
    · exact ⟨(1 : SpecialUnitaryMatrixGroup 2), hValue 1⟩
    · intro y hy
      rcases hy with ⟨g, rfl⟩
      rw [hValue g]
  unfold multiRightTranslateSumOscillationBCF
  change sSup (Set.range F) - sInf (Set.range F) = 0
  rw [hGreatest.csSup_eq, hLeast.csInf_eq]
  norm_num

/-- Exact oscillation inequality for two actual side-three periodic
configurations at the fixed physical target link. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCanonicalStapleFamily_oscillations_ne :
    multiRightTranslateSumOscillationBCF specialUnitaryTwoWilsonEnergyBCF
        (periodicHypercubicThreeSpecialUnitaryTwoCanonicalStapleFamily
          periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration) ≠
      multiRightTranslateSumOscillationBCF specialUnitaryTwoWilsonEnergyBCF
        (periodicHypercubicThreeSpecialUnitaryTwoCanonicalStapleFamily
          periodicHypercubicThreeSpecialUnitaryTwoFarSideCenterConfiguration) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoCanonicalStapleFamily_identityConfiguration,
    periodicHypercubicThreeSpecialUnitaryTwoCanonicalStapleFamily_farSideCenterConfiguration]
  change
    multiRightTranslateSumOscillationBCF specialUnitaryTwoWilsonEnergyBCF
        specialUnitaryTwoPeriodicSixSameStapleFamily ≠
      multiRightTranslateSumOscillationBCF specialUnitaryTwoWilsonEnergyBCF
        specialUnitaryTwoPeriodicSixSplitStapleFamily
  rw [specialUnitaryTwoPeriodicSixSameStaple_oscillation_eq_twelve,
    specialUnitaryTwoPeriodicSixSplitStaple_oscillation_eq_zero]
  norm_num

end

end MathlibAnalytic
end MGAP4D
