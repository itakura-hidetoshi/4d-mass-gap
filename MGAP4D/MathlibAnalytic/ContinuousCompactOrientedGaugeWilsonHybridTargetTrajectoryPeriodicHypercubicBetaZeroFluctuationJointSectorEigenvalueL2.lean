import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroPointSpectrumIntegerGridL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The joint sector selected by a finite subset `s` of a finite family of
continuous linear endomorphisms.  A vector in this submodule is fixed by every
coordinate in `s` and killed by every coordinate outside `s`. -/
def continuousLinearMapJointSectorSubmoduleL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι) :
    Submodule ℝ V where
  carrier :=
    {f | (∀ i ∈ s, Q i f = f) ∧
      (∀ i, i ∉ s → Q i f = 0)}
  zero_mem' := by
    constructor
    · intro i hi
      simp
    · intro i hi
      simp
  add_mem' := by
    intro f g hf hg
    rcases hf with ⟨hfFixed, hfZero⟩
    rcases hg with ⟨hgFixed, hgZero⟩
    constructor
    · intro i hi
      simp [hfFixed i hi, hgFixed i hi]
    · intro i hi
      simp [hfZero i hi, hgZero i hi]
  smul_mem' := by
    intro c f hf
    rcases hf with ⟨hfFixed, hfZero⟩
    constructor
    · intro i hi
      simp [hfFixed i hi]
    · intro i hi
      simp [hfZero i hi]

@[simp]
theorem continuousLinearMapJointSectorSubmoduleL2_mem_iff
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (f : V) :
    f ∈ continuousLinearMapJointSectorSubmoduleL2 Q s ↔
      (∀ i ∈ s, Q i f = f) ∧
        (∀ i, i ∉ s → Q i f = 0) := by
  rfl

/-- On the joint sector indexed by `s`, the sum of all coordinate operators is
scalar multiplication by the sector weight `card s`.  This statement uses only
the defining coordinate eigenconditions; commutation and idempotence are needed
later to construct the sector projectors themselves. -/
theorem continuousLinearMap_univ_sum_apply_eq_card_smul_of_mem_jointSectorSubmoduleL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    {f : V}
    (hf : f ∈ continuousLinearMapJointSectorSubmoduleL2 Q s) :
    (∑ i : ι, Q i) f = (s.card : ℝ) • f := by
  classical
  rw [continuousLinearMapJointSectorSubmoduleL2_mem_iff] at hf
  rcases hf with ⟨hFixed, hZero⟩
  calc
    (∑ i : ι, Q i) f = ∑ i : ι, Q i f := by
      simp only [ContinuousLinearMap.sum_apply]
    _ = ∑ i : ι, if i ∈ s then f else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases his : i ∈ s
      · simp [his, hFixed i his]
      · simp [his, hZero i his]
    _ = (s.card : ℝ) • f := by
      rw [Nat.cast_smul_eq_nsmul]
      simp

/-- Every finite joint-sector label has cardinality bounded by the size of the
ambient finite coordinate family. -/
theorem continuousLinearMapJointSectorSubmoduleL2_card_le_fintype_card
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (s : Finset ι) :
    s.card ≤ Fintype.card ι := by
  simpa using Finset.card_le_univ s

/-- The actual one-link fluctuation joint sector selected by a finite set of
physical edges. -/
noncomputable def ContinuousCompactOrientedGaugeWilsonSystem.fluctuationJointSectorSubmoduleL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (s : Finset C.base.geometry.Edge) :
    Submodule ℝ (Lp ℝ 2 C.gibbsMeasure) := by
  classical
  exact
    continuousLinearMapJointSectorSubmoduleL2
      (fun edge : C.base.geometry.Edge =>
        C.singleLinkHeatBathFluctuationL2 edge)
      s

@[simp]
theorem continuous_compact_oriented_fluctuationJointSectorSubmoduleL2_mem_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (s : Finset C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    f ∈ C.fluctuationJointSectorSubmoduleL2 s ↔
      (∀ edge ∈ s,
        C.singleLinkHeatBathFluctuationL2 edge f = f) ∧
      (∀ edge, edge ∉ s →
        C.singleLinkHeatBathFluctuationL2 edge f = 0) := by
  classical
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.fluctuationJointSectorSubmoduleL2]
    using
      (continuousLinearMapJointSectorSubmoduleL2_mem_iff
        (fun edge : C.base.geometry.Edge =>
          C.singleLinkHeatBathFluctuationL2 edge)
        s f)

/-- Every vector in the actual beta-zero fluctuation joint sector indexed by
`s` is an exact heat-bath Hamiltonian eigenvector of eigenvalue `card s`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_apply_eq_card_smul_of_mem_fluctuationJointSector
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    {f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure}
    (hf : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        s) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f =
      (s.card : ℝ) • f := by
  classical
  have hf' :
      f ∈ continuousLinearMapJointSectorSubmoduleL2
        (fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        s := by
    simpa [ContinuousCompactOrientedGaugeWilsonSystem.fluctuationJointSectorSubmoduleL2]
      using hf
  calc
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f =
        ∑ edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
            edge f :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_heatBathHamiltonianL2_eq_sum_commuting_fluctuation_family
        f
    _ = (s.card : ℝ) • f := by
      have hSum :=
        continuousLinearMap_univ_sum_apply_eq_card_smul_of_mem_jointSectorSubmoduleL2
          (Q := fun edge :
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
                edge)
          s hf'
      simpa only [ContinuousLinearMap.sum_apply] using hSum

/-- Every actual joint-sector label has weight at most `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationJointSector_card_le_324
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    s.card ≤ 324 := by
  classical
  have hCard :=
    continuousLinearMapJointSectorSubmoduleL2_card_le_fintype_card s
  simpa [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]
    using hCard

/-- A nonzero vector in an actual beta-zero joint sector realizes the sector
weight as a genuine heat-bath point-spectrum value. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_card_mem_heatBathPointSpectrumL2_of_nonzero_mem_fluctuationJointSector
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    {f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure}
    (hfZero : f ≠ 0)
    (hfSector : f ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        s) :
    (s.card : ℝ) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 := by
  change ∃ g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    g ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 g =
        (s.card : ℝ) • g
  exact ⟨f, hfZero,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_apply_eq_card_smul_of_mem_fluctuationJointSector
      s hfSector⟩

/-- The cardinality of every actual joint-sector label belongs to the finite
allowed heat-bath integer grid `{0, ..., 324}`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_card_mem_allowedHeatBathPointSpectrumL2
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    (s.card : ℝ) ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2 := by
  change ∃ j : Fin 325, (j.1 : ℝ) = (s.card : ℝ)
  refine ⟨⟨s.card, ?_⟩, rfl⟩
  have hBound :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationJointSector_card_le_324
      s
  omega

/-- Compact receipt for the actual beta-zero joint-sector eigenspace layer. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorEigenvalueL2Receipt :
    Prop :=
  ∀ (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure),
    f ∈
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
          s →
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f =
        (s.card : ℝ) • f ∧
      (f ≠ 0 →
        (s.card : ℝ) ∈
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2)

/-- The actual beta-zero fluctuation joint-sector eigenvalue receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorEigenvalueL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorEigenvalueL2Receipt := by
  intro s f hfSector
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_apply_eq_card_smul_of_mem_fluctuationJointSector
      s hfSector,
    fun hfZero =>
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_card_mem_heatBathPointSpectrumL2_of_nonzero_mem_fluctuationJointSector
        s hfZero hfSector⟩

end

end MathlibAnalytic
end MGAP4D
