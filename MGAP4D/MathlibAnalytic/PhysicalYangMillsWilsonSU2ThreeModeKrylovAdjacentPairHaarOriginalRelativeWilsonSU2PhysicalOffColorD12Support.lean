import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2InteractingPhysicalColorStrictEnergy
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGroundStateTwelveColorRealEnergyInterface
import Mathlib.Tactic

/-!
# P4-Q2-EN: genuine interacting Wilson off-selected-color fixedness and exact D12 support

The ED-EM bounded continuous gauge-invariant SU(2) relative-link Wilson-energy
observable depends on precisely the selected left and right physical spatial
links. For another right or left spatial six-color block, BOTH of those
coordinates are contained in the retained information. This file proves
the concrete observable is measurably factored through the corresponding
real retained-color sigma-algebra, and its ORIGINAL interacting Wilson
joint-L² class belongs to the genuine lpMeas retained subspace.
Consequently the TRUE Wilson conditional-expectation orthogonal projection
fixes the observable at every off-selected right/left color.

The physical twelve-color Dirichlet sum, and separately the normalized
physical D12 residual energy, equal exactly the selected RIGHT and LEFT
interacting Wilson squared Hilbert residuals, with coefficient 1/12.
EM proves each selected term strictly positive. These physical conditional
projections are not identified with independent pair-Haar projections or
the different original Haar-reference Riesz operator AW; no H-uniform or
continuum Yang-Mills mass gap is asserted.
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

section ActualWilsonColorFixedness

variable (H : ℕ)

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "col" => periodicHypercubicEvenSpatialSliceLinkColor H
local notation "kappa" => periodicHypercubicEvenGroundStateSpatialColorEquivFin
local notation "F" => p4Q2EE_SU2_relativeWilsonEnergyBCF H
local notation "W" => p4Q2EE_SU2_physicalWilsonJointL2 H
local notation "P12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
    H 2 (Nat.zero_lt_succ 1)
local notation "Mu" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H 2 (Nat.zero_lt_succ 1)

/-- An off-selected spatial color truly retains the selected physical link
in its off-color configuration type. The canonical six-color equivalence
is used in its exact direction without inventing a finite carrier. -/
private theorem p4Q2EN_selectedLink_offColor
    (e : Link) (c : Fin 6) (hc : c ≠ kappa (col e)) :
    col e ≠ periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c := by
  intro hh
  apply hc
  have h := congrArg kappa hh
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- The actual SU(2) relative-link Wilson energy is measurable with respect
to the retained sigma-algebra of any OTHER physical right six-color block.
Both selected coordinates remain represented in that sigma-algebra. -/
private theorem p4Q2EN_rightOffColor_stronglyMeasurable
    (e : Link) (c : Fin 6) (hc : c ≠ kappa (col e)) :
    @StronglyMeasurable Joint ℝ
      inferInstance
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
        H 2 (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)) inferInstance
      (fun z : Joint => F e z) := by
  let cc := periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c
  let eOff : PeriodicHypercubicEvenSpatialSliceOffColorLink H cc :=
    ⟨e, p4Q2EN_selectedLink_offColor H e c hc⟩
  let factor :
      (Cfg × (PeriodicHypercubicEvenSpatialSliceOffColorLink H cc → G)) → ℝ :=
    fun t => specialUnitaryWilsonPlaquetteEnergy 2 ((t.1 e)⁻¹ * t.2 eOff)
  have hFactor : Measurable factor := by
    apply (continuous_specialUnitaryWilsonPlaquetteEnergy 2).measurable.comp
    dsimp [factor]
    fun_prop
  letI : MeasurableSpace Joint :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
      H 2 cc
  have hRet : Measurable (fun z : Joint =>
      (z.1, periodicHypercubicEvenSpatialSliceOffColorRestriction cc z.2)) := by
    exact (Measurable.of_comap_le le_sup_left).prodMk
      (Measurable.of_comap_le le_sup_right)
  have hMeas : Measurable (fun z : Joint => F e z) := by
    have hh := hFactor.comp hRet
    have hfun :
        (fun z : Joint => F e z) =
          fun z : Joint =>
            factor (z.1, periodicHypercubicEvenSpatialSliceOffColorRestriction cc z.2) := by
      funext z
      rw [p4Q2EE_SU2_relativeWilsonEnergyBCF_apply]
      rfl
    rw [hfun]
    exact hh
  exact hMeas.stronglyMeasurable

/-- A genuine off-selected LEFT color retains the entire original right
boundary and the physical selected left link in its off-color coordinates. -/
private theorem p4Q2EN_leftOffColor_stronglyMeasurable
    (e : Link) (c : Fin 6) (hc : c ≠ kappa (col e)) :
    @StronglyMeasurable Joint ℝ
      inferInstance
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
        H 2 (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)) inferInstance
      (fun z : Joint => F e z) := by
  let cc := periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c
  let eOff : PeriodicHypercubicEvenSpatialSliceOffColorLink H cc :=
    ⟨e, p4Q2EN_selectedLink_offColor H e c hc⟩
  let factor :
      (Cfg × (PeriodicHypercubicEvenSpatialSliceOffColorLink H cc → G)) → ℝ :=
    fun t => specialUnitaryWilsonPlaquetteEnergy 2 ((t.2 eOff)⁻¹ * t.1 e)
  have hFactor : Measurable factor := by
    apply (continuous_specialUnitaryWilsonPlaquetteEnergy 2).measurable.comp
    dsimp [factor]
    fun_prop
  letI : MeasurableSpace Joint :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
      H 2 cc
  have hRet : Measurable (fun z : Joint =>
      (z.2, periodicHypercubicEvenSpatialSliceOffColorRestriction cc z.1)) := by
    exact (Measurable.of_comap_le le_sup_left).prodMk
      (Measurable.of_comap_le le_sup_right)
  have hMeas : Measurable (fun z : Joint => F e z) := by
    have hh := hFactor.comp hRet
    have hfun :
        (fun z : Joint => F e z) =
          fun z : Joint =>
            factor (z.2, periodicHypercubicEvenSpatialSliceOffColorRestriction cc z.1) := by
      funext z
      rw [p4Q2EE_SU2_relativeWilsonEnergyBCF_apply]
      rfl
    rw [hfun]
    exact hh
  exact hMeas.stronglyMeasurable

/-- The REAL interacting original Wilson conditional projection fixes this
physical joint-L² witness in every off-selected RIGHT spatial color. -/
theorem p4Q2EN_SU2_offSelectedPhysicalRightColor_fixed
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Link) (c : Fin 6) (hc : c ≠ kappa (col e)) :
    P12 beta hbeta (Sum.inl c) (W beta hbeta e) =
      W beta hbeta e := by
  let cc := periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c
  let sigma : MeasurableSpace Joint :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
      H 2 cc
  let f := W beta hbeta e
  have hMem : f ∈ lpMeas ℝ ℝ sigma 2 (Mu beta hbeta) := by
    rw [mem_lpMeas_iff_aestronglyMeasurable]
    exact (p4Q2EN_rightOffColor_stronglyMeasurable H e c hc).aestronglyMeasurable.congr
      (p4Q2EE_SU2_physicalWilsonJointL2_ae_eq H beta hbeta e).symm
  let q : lpMeas ℝ ℝ sigma 2 (Mu beta hbeta) := ⟨f, hMem⟩
  let hm := periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
    H 2 cc
  letI : Fact (sigma ≤
      (inferInstance : MeasurableSpace Joint)) := ⟨hm⟩
  have hq :
      (condExpL2 ℝ ℝ hm (q :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H 2 (Nat.zero_lt_succ 1) beta hbeta) :
        lpMeas ℝ ℝ sigma 2 (Mu beta hbeta)) = q := by
    unfold condExpL2
    exact Submodule.orthogonalProjection_mem_subspace_eq_self q
  change ((condExpL2 ℝ ℝ hm (q :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H 2 (Nat.zero_lt_succ 1) beta hbeta) :
      lpMeas ℝ ℝ sigma 2 (Mu beta hbeta)) :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H 2 (Nat.zero_lt_succ 1) beta hbeta) = (q :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H 2 (Nat.zero_lt_succ 1) beta hbeta)
  exact congrArg
    (fun y : lpMeas ℝ ℝ sigma 2 (Mu beta hbeta) =>
      (y : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H 2 (Nat.zero_lt_succ 1) beta hbeta)) hq

/-- A genuinely interacting Wilson LEFT conditional color update also
fixes the witness off its selected left spatial six-color class. -/
theorem p4Q2EN_SU2_offSelectedPhysicalLeftColor_fixed
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Link) (c : Fin 6) (hc : c ≠ kappa (col e)) :
    P12 beta hbeta (Sum.inr c) (W beta hbeta e) =
      W beta hbeta e := by
  let cc := periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c
  let sigma : MeasurableSpace Joint :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
      H 2 cc
  let f := W beta hbeta e
  have hMem : f ∈ lpMeas ℝ ℝ sigma 2 (Mu beta hbeta) := by
    rw [mem_lpMeas_iff_aestronglyMeasurable]
    exact (p4Q2EN_leftOffColor_stronglyMeasurable H e c hc).aestronglyMeasurable.congr
      (p4Q2EE_SU2_physicalWilsonJointL2_ae_eq H beta hbeta e).symm
  let q : lpMeas ℝ ℝ sigma 2 (Mu beta hbeta) := ⟨f, hMem⟩
  let hm := periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_le
    H 2 cc
  letI : Fact (sigma ≤
      (inferInstance : MeasurableSpace Joint)) := ⟨hm⟩
  have hq :
      (condExpL2 ℝ ℝ hm (q :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H 2 (Nat.zero_lt_succ 1) beta hbeta) :
        lpMeas ℝ ℝ sigma 2 (Mu beta hbeta)) = q := by
    unfold condExpL2
    exact Submodule.orthogonalProjection_mem_subspace_eq_self q
  change ((condExpL2 ℝ ℝ hm (q :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H 2 (Nat.zero_lt_succ 1) beta hbeta) :
      lpMeas ℝ ℝ sigma 2 (Mu beta hbeta)) :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H 2 (Nat.zero_lt_succ 1) beta hbeta) = (q :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H 2 (Nat.zero_lt_succ 1) beta hbeta)
  exact congrArg
    (fun y : lpMeas ℝ ℝ sigma 2 (Mu beta hbeta) =>
      (y : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H 2 (Nat.zero_lt_succ 1) beta hbeta)) hq

/-- The full true interacting Wilson physical TWELVE-color Hilbert residual
sum is exactly supported on its selected right and left colors. -/
theorem p4Q2EN_SU2_originalPhysicalTwelveColorSum_eq_selectedTwo
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    p4Q2BC_twelvePhysicalResidualSum
        H 2 (Nat.zero_lt_succ 1) beta hbeta (W beta hbeta e) =
      ‖W beta hbeta e -
        P12 beta hbeta (Sum.inl (kappa (col e))) (W beta hbeta e)‖ ^ 2 +
      ‖W beta hbeta e -
        P12 beta hbeta (Sum.inr (kappa (col e))) (W beta hbeta e)‖ ^ 2 := by
  classical
  let f := W beta hbeta e
  let k : Fin 6 := kappa (col e)
  have hR :
      (∑ c : Fin 6, ‖f - P12 beta hbeta (Sum.inl c) f‖ ^ 2) =
        ‖f - P12 beta hbeta (Sum.inl k) f‖ ^ 2 := by
    apply Finset.sum_eq_single k
    · intro c _ hOther
      rw [p4Q2EN_SU2_offSelectedPhysicalRightColor_fixed H beta hbeta e c hOther]
      simp [f]
    · simp
  have hL :
      (∑ c : Fin 6, ‖f - P12 beta hbeta (Sum.inr c) f‖ ^ 2) =
        ‖f - P12 beta hbeta (Sum.inr k) f‖ ^ 2 := by
    apply Finset.sum_eq_single k
    · intro c _ hOther
      rw [p4Q2EN_SU2_offSelectedPhysicalLeftColor_fixed H beta hbeta e c hOther]
      simp [f]
    · simp
  unfold p4Q2BC_twelvePhysicalResidualSum
  rw [Fintype.sum_sum_type]
  rw [hR, hL]

/-- The physically normalized original Wilson D12 Dirichlet energy,
which is NOT the original Haar-reference Riesz quadratic, has the exact
two-color support with its native 1/12 physical normalization. -/
theorem p4Q2EN_SU2_originalPhysicalD12_eq_selectedTwo
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
        H 2 (Nat.zero_lt_succ 1) beta hbeta (W beta hbeta e) =
      (12 : ℝ)⁻¹ *
        (‖W beta hbeta e -
          P12 beta hbeta (Sum.inl (kappa (col e))) (W beta hbeta e)‖ ^ 2 +
         ‖W beta hbeta e -
          P12 beta hbeta (Sum.inr (kappa (col e))) (W beta hbeta e)‖ ^ 2) := by
  have hSum :=
    p4Q2BC_realPhysicalResidualSum_eq_twelve_mul_normalized
      H 2 (Nat.zero_lt_succ 1) beta hbeta (W beta hbeta e)
  rw [p4Q2EN_SU2_originalPhysicalTwelveColorSum_eq_selectedTwo] at hSum
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
        H 2 (Nat.zero_lt_succ 1) beta hbeta (W beta hbeta e) =
      (12 : ℝ)⁻¹ *
        ((12 : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
            H 2 (Nat.zero_lt_succ 1) beta hbeta (W beta hbeta e)) := by ring
    _ = _ := by rw [← hSum]

/-- The same physical SU(2) witness has strictly positive normalized
interacting Wilson D12 residual energy, using EM's two strict terms. -/
theorem p4Q2EN_SU2_originalPhysicalD12_pos
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
        H 2 (Nat.zero_lt_succ 1) beta hbeta (W beta hbeta e) := by
  rw [p4Q2EN_SU2_originalPhysicalD12_eq_selectedTwo]
  obtain ⟨hRight, hLeft⟩ :=
    p4Q2EM_SU2_bothSelectedPhysicalWilsonColorDefects_pos H beta hbeta e
  exact mul_pos (by norm_num : 0 < (12 : ℝ)⁻¹) (add_pos hRight hLeft)

end ActualWilsonColorFixedness
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EN_SU2_offSelectedPhysicalRightColor_fixed
#print axioms MGAP4D.MathlibAnalytic.p4Q2EN_SU2_offSelectedPhysicalLeftColor_fixed
#print axioms MGAP4D.MathlibAnalytic.p4Q2EN_SU2_originalPhysicalTwelveColorSum_eq_selectedTwo
#print axioms MGAP4D.MathlibAnalytic.p4Q2EN_SU2_originalPhysicalD12_eq_selectedTwo
#print axioms MGAP4D.MathlibAnalytic.p4Q2EN_SU2_originalPhysicalD12_pos
