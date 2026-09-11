import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCanonicalJointSectorProjectorL2
import Mathlib.Data.Finset.SDiff
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Every selected/complement factor acts as the identity on the joint sector
with the same label. -/
theorem continuousLinearMapJointSectorFactorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    {f : V}
    (hf : f ∈ continuousLinearMapJointSectorSubmoduleL2 Q s)
    (i : ι) :
    continuousLinearMapJointSectorFactorL2 Q s i f = f := by
  have hf' :=
    (continuousLinearMapJointSectorSubmoduleL2_mem_iff Q s f).1 hf
  by_cases hi : i ∈ s
  · simp [continuousLinearMapJointSectorFactorL2, hi, hf'.1 i hi]
  · simp [continuousLinearMapJointSectorFactorL2, hi, hf'.2 i hi]

/-- The canonical joint-sector projector restricts to the identity on its
specified joint-sector submodule. -/
theorem continuousLinearMap_jointSectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {f : V}
    (hf : f ∈ continuousLinearMapJointSectorSubmoduleL2 Q s) :
    continuousLinearMapJointSectorProjectorL2 Q s hComm f = f := by
  change
    (Finset.univ.noncommProd
      (continuousLinearMapJointSectorFactorL2 Q s)
      (continuousLinearMapJointSectorFactorL2_pairwise_comm Q s hComm)) f = f
  exact
    Finset.noncommProd_induction
      (Finset.univ : Finset ι)
      (continuousLinearMapJointSectorFactorL2 Q s)
      (continuousLinearMapJointSectorFactorL2_pairwise_comm Q s hComm)
      (fun T : V →L[ℝ] V => T f = f)
      (fun A B hA hB => by
        change A (B f) = f
        rw [hB, hA])
      (by simp)
      (fun i hi =>
        continuousLinearMapJointSectorFactorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
          Q s hf i)

/-- The canonical projector of a pairwise commuting idempotent family is
idempotent. -/
theorem continuousLinearMap_jointSectorProjectorL2_mul_self
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    continuousLinearMapJointSectorProjectorL2 Q s hComm *
        continuousLinearMapJointSectorProjectorL2 Q s hComm =
      continuousLinearMapJointSectorProjectorL2 Q s hComm := by
  apply ContinuousLinearMap.ext
  intro f
  change
    continuousLinearMapJointSectorProjectorL2 Q s hComm
        (continuousLinearMapJointSectorProjectorL2 Q s hComm f) =
      continuousLinearMapJointSectorProjectorL2 Q s hComm f
  exact
    continuousLinearMap_jointSectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
      Q s hComm
      (continuousLinearMap_jointSectorProjectorL2_apply_mem_jointSectorSubmoduleL2
        Q s hIdempotent hComm f)

/-- A canonical projector kills every vector in a differently labelled joint
sector.  A coordinate in the symmetric difference supplies either a `Q_i`
factor killing the vector or an `I - Q_i` factor killing it. -/
theorem continuousLinearMap_jointSectorProjectorL2_apply_eq_zero_of_mem_jointSectorSubmoduleL2_of_ne
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s t : Finset ι)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (hst : s ≠ t)
    {f : V}
    (hf : f ∈ continuousLinearMapJointSectorSubmoduleL2 Q t) :
    continuousLinearMapJointSectorProjectorL2 Q s hComm f = 0 := by
  classical
  have hf' :=
    (continuousLinearMapJointSectorSubmoduleL2_mem_iff Q t f).1 hf
  have hCases : ¬s ⊆ t ∨ ¬t ⊆ s := by
    by_contra h
    push_neg at h
    exact hst (le_antisymm h.1 h.2)
  let factor : ι → V →L[ℝ] V :=
    continuousLinearMapJointSectorFactorL2 Q s
  have hFactorComm :
      ((Finset.univ : Finset ι) : Set ι).Pairwise (Commute on factor) := by
    exact continuousLinearMapJointSectorFactorL2_pairwise_comm Q s hComm
  change (Finset.univ.noncommProd factor hFactorComm) f = 0
  rcases hCases with hNotSubset | hNotSuperset
  · rcases Finset.sdiff_nonempty.mpr hNotSubset with ⟨i, hi⟩
    have his : i ∈ s := (Finset.mem_sdiff.mp hi).1
    have hit : i ∉ t := (Finset.mem_sdiff.mp hi).2
    have hFactorZero : factor i f = 0 := by
      dsimp [factor]
      simp [continuousLinearMapJointSectorFactorL2, his, hf'.2 i hit]
    have hExtract :=
      Finset.noncommProd_erase_mul
        (Finset.univ : Finset ι)
        (Finset.mem_univ i)
        factor
        hFactorComm
    have hApply :=
      congrArg (fun T : V →L[ℝ] V => T f) hExtract
    simpa [hFactorZero] using hApply.symm
  · rcases Finset.sdiff_nonempty.mpr hNotSuperset with ⟨i, hi⟩
    have hit : i ∈ t := (Finset.mem_sdiff.mp hi).1
    have his : i ∉ s := (Finset.mem_sdiff.mp hi).2
    have hFactorZero : factor i f = 0 := by
      dsimp [factor]
      simp [continuousLinearMapJointSectorFactorL2, his, hf'.1 i hit]
    have hExtract :=
      Finset.noncommProd_erase_mul
        (Finset.univ : Finset ι)
        (Finset.mem_univ i)
        factor
        hFactorComm
    have hApply :=
      congrArg (fun T : V →L[ℝ] V => T f) hExtract
    simpa [hFactorZero] using hApply.symm

/-- Canonical projectors with distinct labels have zero product. -/
theorem continuousLinearMap_jointSectorProjectorL2_mul_eq_zero_of_ne
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s t : Finset ι)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (hst : s ≠ t) :
    continuousLinearMapJointSectorProjectorL2 Q s hComm *
        continuousLinearMapJointSectorProjectorL2 Q t hComm = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  change
    continuousLinearMapJointSectorProjectorL2 Q s hComm
        (continuousLinearMapJointSectorProjectorL2 Q t hComm f) = 0
  exact
    continuousLinearMap_jointSectorProjectorL2_apply_eq_zero_of_mem_jointSectorSubmoduleL2_of_ne
      Q s t hComm hst
      (continuousLinearMap_jointSectorProjectorL2_apply_mem_jointSectorSubmoduleL2
        Q t hIdempotent hComm f)

/-- The full multiplication law for canonical joint-sector projectors: equal
labels return the projector and distinct labels return zero. -/
theorem continuousLinearMap_jointSectorProjectorL2_mul_eq_ite
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (s t : Finset ι)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    continuousLinearMapJointSectorProjectorL2 Q s hComm *
        continuousLinearMapJointSectorProjectorL2 Q t hComm =
      if s = t then continuousLinearMapJointSectorProjectorL2 Q s hComm else 0 := by
  by_cases hst : s = t
  · subst t
    simpa using
      continuousLinearMap_jointSectorProjectorL2_mul_self
        Q s hIdempotent hComm
  · simpa [hst] using
      continuousLinearMap_jointSectorProjectorL2_mul_eq_zero_of_ne
        Q s t hIdempotent hComm hst

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- The actual beta-zero canonical projector is idempotent. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationJointSectorProjectorL2_mul_self
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2 s *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2 s =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2 s := by
  classical
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2]
    using
      (continuousLinearMap_jointSectorProjectorL2_mul_self
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        s
        (fun edge f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
            edge f)
        (fun target source f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source f))

/-- Distinct actual beta-zero joint-sector projectors have zero product. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationJointSectorProjectorL2_mul_eq_zero_of_ne
    (s t : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hst : s ≠ t) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2 s *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2 t = 0 := by
  classical
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2]
    using
      (continuousLinearMap_jointSectorProjectorL2_mul_eq_zero_of_ne
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        s t
        (fun edge f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
            edge f)
        (fun target source f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source f)
        hst)

/-- The actual canonical projectors satisfy the Kronecker multiplication law. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationJointSectorProjectorL2_mul_eq_ite
    (s t : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2 s *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2 t =
      if s = t then
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2 s
      else 0 := by
  classical
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2]
    using
      (continuousLinearMap_jointSectorProjectorL2_mul_eq_ite
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        s t
        (fun edge f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
            edge f)
        (fun target source f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source f))

/-- Compact receipt for the actual canonical projector idempotence and pairwise
orthogonality layer. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroJointSectorProjectorIdempotentOrthogonalL2Receipt :
    Prop :=
  ∀ (s t : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge),
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2 s *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2 t =
      if s = t then
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2 s
      else 0

/-- The actual canonical projector idempotence and orthogonality receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroJointSectorProjectorIdempotentOrthogonalL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroJointSectorProjectorIdempotentOrthogonalL2Receipt := by
  intro s t
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationJointSectorProjectorL2_mul_eq_ite
      s t

end

end MathlibAnalytic
end MGAP4D
