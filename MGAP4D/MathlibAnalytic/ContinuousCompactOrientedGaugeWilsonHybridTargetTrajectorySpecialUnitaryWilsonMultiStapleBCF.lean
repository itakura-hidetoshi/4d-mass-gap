import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectorySpecialUnitaryWilsonTwoLinkNoGoBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- A finite sum of right-translated copies of one bounded continuous function on
an arbitrary compact topological group.  For Wilson theory, the entries of `s`
are the frozen staples incident to the updated target link. -/
def multiRightTranslateSumBCF
    {G ι : Type*}
    [Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [Fintype ι]
    (f : BoundedContinuousFunction G ℝ)
    (s : ι → G) :
    BoundedContinuousFunction G ℝ := by
  classical
  let F : G → ℝ := fun g => ∑ i, f (g * s i)
  have hF : Continuous F := by
    apply continuous_finset_sum
    intro i _hi
    exact f.continuous.comp (continuous_id.mul continuous_const)
  exact BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩

@[simp]
theorem multiRightTranslateSumBCF_apply
    {G ι : Type*}
    [Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [Fintype ι]
    (f : BoundedContinuousFunction G ℝ)
    (s : ι → G)
    (g : G) :
    multiRightTranslateSumBCF f s g = ∑ i, f (g * s i) := by
  rfl

/-- Oscillation of a finite multi-staple section. -/
def multiRightTranslateSumOscillationBCF
    {G ι : Type*}
    [Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [Fintype ι]
    (f : BoundedContinuousFunction G ℝ)
    (s : ι → G) : ℝ :=
  sSup (Set.range (multiRightTranslateSumBCF f s)) -
    sInf (Set.range (multiRightTranslateSumBCF f s))

/-- Simultaneous left multiplication of all staples is absorbed by a right
translation of the target variable.  Hence it does not change the section
range. -/
theorem multiRightTranslateSumBCF_range_commonLeftMul_eq
    {G ι : Type*}
    [Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [Fintype ι]
    (f : BoundedContinuousFunction G ℝ)
    (s : ι → G)
    (r : G) :
    Set.range (multiRightTranslateSumBCF f (fun i => r * s i)) =
      Set.range (multiRightTranslateSumBCF f s) := by
  classical
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g * r, ?_⟩
    simp [multiRightTranslateSumBCF, mul_assoc]
  · rintro ⟨g, rfl⟩
    refine ⟨g * r⁻¹, ?_⟩
    simp [multiRightTranslateSumBCF, mul_assoc]

/-- Multi-staple oscillation depends only on the relative staple configuration,
not on a common left factor. -/
theorem multiRightTranslateSumOscillationBCF_commonLeftMul
    {G ι : Type*}
    [Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [Fintype ι]
    (f : BoundedContinuousFunction G ℝ)
    (s : ι → G)
    (r : G) :
    multiRightTranslateSumOscillationBCF f (fun i => r * s i) =
      multiRightTranslateSumOscillationBCF f s := by
  unfold multiRightTranslateSumOscillationBCF
  rw [multiRightTranslateSumBCF_range_commonLeftMul_eq f s r]

/-- Normalize a finite staple family relative to one distinguished anchor. -/
def relativeStapleFamily
    {G ι : Type*}
    [Group G]
    (s : ι → G)
    (anchor : ι) : ι → G :=
  fun i => (s anchor)⁻¹ * s i

@[simp]
theorem relativeStapleFamily_anchor
    {G ι : Type*}
    [Group G]
    (s : ι → G)
    (anchor : ι) :
    relativeStapleFamily s anchor anchor = 1 := by
  simp [relativeStapleFamily]

/-- Anchoring one staple at the identity preserves the complete section
oscillation. -/
theorem multiRightTranslateSumOscillationBCF_relativeStapleFamily
    {G ι : Type*}
    [Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [Fintype ι]
    (f : BoundedContinuousFunction G ℝ)
    (s : ι → G)
    (anchor : ι) :
    multiRightTranslateSumOscillationBCF f
        (relativeStapleFamily s anchor) =
      multiRightTranslateSumOscillationBCF f s := by
  simpa [relativeStapleFamily] using
    (multiRightTranslateSumOscillationBCF_commonLeftMul
      f s (s anchor)⁻¹)

/-- A continuous family of frozen staples is independent of target-link
replacement when none of its values changes after replacing the target. -/
def ContinuousCompactOrientedGaugeWilsonSystem.targetIndependentStapleFamilyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {ι : Type*}
    [Fintype ι]
    (target : C.base.geometry.Edge)
    (staple : ι → C.base.Configuration →C C.base.Gauge) : Prop :=
  ∀ i A g, staple i (C.base.replaceLink A target g) = staple i A

/-- A concrete finite multi-staple cylinder observable. -/
def ContinuousCompactOrientedGaugeWilsonSystem.multiStapleCylinderObservableBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {ι : Type*}
    [Fintype ι]
    (target : C.base.geometry.Edge)
    (f : BoundedContinuousFunction C.base.Gauge ℝ)
    (staple : ι → C.base.Configuration →C C.base.Gauge) :
    BoundedContinuousFunction C.base.Configuration ℝ := by
  classical
  let F : C.base.Configuration → ℝ :=
    fun A => ∑ i, f (A target * staple i A)
  have hF : Continuous F := by
    apply continuous_finset_sum
    intro i _hi
    exact f.continuous.comp
      ((continuous_apply target).mul (staple i).continuous)
  exact BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩

@[simp]
theorem continuous_compact_oriented_multiStapleCylinderObservableBCF_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {ι : Type*}
    [Fintype ι]
    (target : C.base.geometry.Edge)
    (f : BoundedContinuousFunction C.base.Gauge ℝ)
    (staple : ι → C.base.Configuration →C C.base.Gauge)
    (A : C.base.Configuration) :
    C.multiStapleCylinderObservableBCF target f staple A =
      ∑ i, f (A target * staple i A) := by
  rfl

/-- The rank-zero insertion profile of a target-independent multi-staple
observable is its finite right-translate section at the rank-zero background. -/
theorem continuous_compact_oriented_multiStapleCylinderObservableBCF_initialInsertionProfile_eq_section
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {ι : Type*}
    [Fintype ι]
    (target : C.base.geometry.Edge)
    (f : BoundedContinuousFunction C.base.Gauge ℝ)
    (staple : ι → C.base.Configuration →C C.base.Gauge)
    (hStaple : C.targetIndependentStapleFamilyBCF target staple)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
        target (C.multiStapleCylinderObservableBCF target f staple) z =
      multiRightTranslateSumBCF f
        (fun i => staple i
          (C.independentPairHybridConfiguration z.1 z.2 0)) := by
  classical
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.targetIndependentStapleFamilyBCF at hStaple
  funext g
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
  rw [continuous_compact_oriented_multiStapleCylinderObservableBCF_apply]
  rw [multiRightTranslateSumBCF_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [compact_oriented_replaceLink_same]
  rw [hStaple i
    (C.independentPairHybridConfiguration z.1 z.2 0) g]

/-- The full-rank insertion profile is the corresponding multi-staple section at
the full-rank endpoint background. -/
theorem continuous_compact_oriented_multiStapleCylinderObservableBCF_finalInsertionProfile_eq_section
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {ι : Type*}
    [Fintype ι]
    (target : C.base.geometry.Edge)
    (f : BoundedContinuousFunction C.base.Gauge ℝ)
    (staple : ι → C.base.Configuration →C C.base.Gauge)
    (hStaple : C.targetIndependentStapleFamilyBCF target staple)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
        target (C.multiStapleCylinderObservableBCF target f staple) z =
      multiRightTranslateSumBCF f
        (fun i => staple i
          (C.independentPairHybridConfiguration z.1 z.2
            (Fintype.card C.base.geometry.Edge))) := by
  classical
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.targetIndependentStapleFamilyBCF at hStaple
  funext g
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
  rw [continuous_compact_oriented_multiStapleCylinderObservableBCF_apply]
  rw [multiRightTranslateSumBCF_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [compact_oriented_replaceLink_same]
  rw [hStaple i
    (C.independentPairHybridConfiguration z.1 z.2
      (Fintype.card C.base.geometry.Edge)) g]

/-- Exact scalar form of the endpoint oscillation margin for a concrete
multi-staple cylinder observable. -/
theorem continuous_compact_oriented_multiStapleCylinderObservableBCF_oscillationMargin_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {ι : Type*}
    [Fintype ι]
    (target : C.base.geometry.Edge)
    (f : BoundedContinuousFunction C.base.Gauge ℝ)
    (staple : ι → C.base.Configuration →C C.base.Gauge)
    (hStaple : C.targetIndependentStapleFamilyBCF target staple)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
        target (C.multiStapleCylinderObservableBCF target f staple) z =
      abs
        (multiRightTranslateSumOscillationBCF f
            (fun i => staple i
              (C.independentPairHybridConfiguration z.1 z.2 0)) -
          multiRightTranslateSumOscillationBCF f
            (fun i => staple i
              (C.independentPairHybridConfiguration z.1 z.2
                (Fintype.card C.base.geometry.Edge)))) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
    multiRightTranslateSumOscillationBCF
  rw [continuous_compact_oriented_multiStapleCylinderObservableBCF_initialInsertionProfile_eq_section
      C target f staple hStaple z,
    continuous_compact_oriented_multiStapleCylinderObservableBCF_finalInsertionProfile_eq_section
      C target f staple hStaple z]

/-- The original coordinate-update witness for a concrete multi-staple
observable is exactly inequality of its two endpoint relative-staple
oscillations. -/
theorem continuous_compact_oriented_multiStapleCylinderObservableBCF_coordinateUpdateWitness_iff_oscillation_ne
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {ι : Type*}
    [Fintype ι]
    (target : C.base.geometry.Edge)
    (f : BoundedContinuousFunction C.base.Gauge ℝ)
    (staple : ι → C.base.Configuration →C C.base.Gauge)
    (hStaple : C.targetIndependentStapleFamilyBCF target staple)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
        target (C.multiStapleCylinderObservableBCF target f staple) z ↔
      multiRightTranslateSumOscillationBCF f
          (fun i => staple i
            (C.independentPairHybridConfiguration z.1 z.2 0)) ≠
        multiRightTranslateSumOscillationBCF f
          (fun i => staple i
            (C.independentPairHybridConfiguration z.1 z.2
              (Fintype.card C.base.geometry.Edge))) := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_iff_oscillationMargin_pos]
  rw [continuous_compact_oriented_multiStapleCylinderObservableBCF_oscillationMargin_eq
    C target f staple hStaple z]
  rw [abs_pos, sub_ne_zero]

/-- The actual finite `SU(N)` Wilson multi-staple section. -/
def specialUnitaryWilsonMultiStapleSectionBCF
    (N : ℕ)
    {ι : Type*}
    [Fintype ι]
    (s : ι → SpecialUnitaryMatrixGroup N) :
    BoundedContinuousFunction (SpecialUnitaryMatrixGroup N) ℝ := by
  letI : IsTopologicalGroup (SpecialUnitaryMatrixGroup N) :=
    specialUnitaryGroupIsTopologicalGroup N
  letI : CompactSpace (SpecialUnitaryMatrixGroup N) :=
    specialUnitaryGroupCompactSpace N
  exact multiRightTranslateSumBCF
    (specialUnitaryWilsonPlaquetteEnergyBCF N) s

@[simp]
theorem specialUnitaryWilsonMultiStapleSectionBCF_apply
    (N : ℕ)
    {ι : Type*}
    [Fintype ι]
    (s : ι → SpecialUnitaryMatrixGroup N)
    (g : SpecialUnitaryMatrixGroup N) :
    specialUnitaryWilsonMultiStapleSectionBCF N s g =
      ∑ i, specialUnitaryWilsonPlaquetteEnergy N (g * s i) := by
  letI : IsTopologicalGroup (SpecialUnitaryMatrixGroup N) :=
    specialUnitaryGroupIsTopologicalGroup N
  letI : CompactSpace (SpecialUnitaryMatrixGroup N) :=
    specialUnitaryGroupCompactSpace N
  change multiRightTranslateSumBCF
      (specialUnitaryWilsonPlaquetteEnergyBCF N) s g = _
  rw [multiRightTranslateSumBCF_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [specialUnitaryWilsonPlaquetteEnergyBCF_apply]

/-- Oscillation of the actual `SU(N)` Wilson multi-staple section. -/
def specialUnitaryWilsonMultiStapleSectionOscillationBCF
    (N : ℕ)
    {ι : Type*}
    [Fintype ι]
    (s : ι → SpecialUnitaryMatrixGroup N) : ℝ :=
  sSup (Set.range (specialUnitaryWilsonMultiStapleSectionBCF N s)) -
    sInf (Set.range (specialUnitaryWilsonMultiStapleSectionBCF N s))

/-- Common left multiplication of every `SU(N)` Wilson staple leaves the
multi-staple oscillation unchanged. -/
theorem specialUnitaryWilsonMultiStapleSectionOscillationBCF_commonLeftMul
    (N : ℕ)
    {ι : Type*}
    [Fintype ι]
    (s : ι → SpecialUnitaryMatrixGroup N)
    (r : SpecialUnitaryMatrixGroup N) :
    specialUnitaryWilsonMultiStapleSectionOscillationBCF N
        (fun i => r * s i) =
      specialUnitaryWilsonMultiStapleSectionOscillationBCF N s := by
  letI : IsTopologicalGroup (SpecialUnitaryMatrixGroup N) :=
    specialUnitaryGroupIsTopologicalGroup N
  letI : CompactSpace (SpecialUnitaryMatrixGroup N) :=
    specialUnitaryGroupCompactSpace N
  unfold specialUnitaryWilsonMultiStapleSectionOscillationBCF
  change multiRightTranslateSumOscillationBCF
      (specialUnitaryWilsonPlaquetteEnergyBCF N) (fun i => r * s i) =
    multiRightTranslateSumOscillationBCF
      (specialUnitaryWilsonPlaquetteEnergyBCF N) s
  exact multiRightTranslateSumOscillationBCF_commonLeftMul
    (specialUnitaryWilsonPlaquetteEnergyBCF N) s r

/-- The actual `SU(N)` Wilson multi-staple oscillation is completely determined
by the family normalized relative to any chosen anchor staple. -/
theorem specialUnitaryWilsonMultiStapleSectionOscillationBCF_relativeStapleFamily
    (N : ℕ)
    {ι : Type*}
    [Fintype ι]
    (s : ι → SpecialUnitaryMatrixGroup N)
    (anchor : ι) :
    specialUnitaryWilsonMultiStapleSectionOscillationBCF N
        (relativeStapleFamily s anchor) =
      specialUnitaryWilsonMultiStapleSectionOscillationBCF N s := by
  letI : IsTopologicalGroup (SpecialUnitaryMatrixGroup N) :=
    specialUnitaryGroupIsTopologicalGroup N
  letI : CompactSpace (SpecialUnitaryMatrixGroup N) :=
    specialUnitaryGroupCompactSpace N
  unfold specialUnitaryWilsonMultiStapleSectionOscillationBCF
  change multiRightTranslateSumOscillationBCF
      (specialUnitaryWilsonPlaquetteEnergyBCF N)
        (relativeStapleFamily s anchor) =
    multiRightTranslateSumOscillationBCF
      (specialUnitaryWilsonPlaquetteEnergyBCF N) s
  exact multiRightTranslateSumOscillationBCF_relativeStapleFamily
    (specialUnitaryWilsonPlaquetteEnergyBCF N) s anchor

end

end MathlibAnalytic
end MGAP4D
