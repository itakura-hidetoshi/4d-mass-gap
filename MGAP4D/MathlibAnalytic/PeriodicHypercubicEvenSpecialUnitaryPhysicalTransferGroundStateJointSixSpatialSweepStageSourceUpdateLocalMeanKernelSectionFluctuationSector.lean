import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateLocalMeanKernelSectionL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionOneLinkProjectionFluctuationAnnihilation
import Mathlib.Tactic

/-!
# The physical local-mean L2 carrier is a pure one-link fluctuation

PR #4738 realizes the physical diagonal local source mean as the existing
remote kernel-section fluctuation

  Q_link f = f - P_link f

in the actual fixed-right kernel-section L2 carrier.

The older remote kernel-section projection algebra proves pointwise almost
everywhere that

  P_link (Q_link f) = 0.

This file lifts that statement to the concrete L2 carrier used by the current
physical response construction.  It therefore records that the canonical
local-mean vector is genuinely in the one-link fluctuation sector, rather than
merely being an arbitrary L2 representative.

No full ground-state-joint disintegration, norm comparison, or new coefficient
is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance localMeanKernelSectionFluctuationSectorSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance localMeanKernelSectionFluctuationSectorSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- L2 projection of the canonical local-mean fluctuation representative onto
the source off-fiber conditional subspace.

The theorem below proves that this vector is zero.  Naming it explicitly makes
the fluctuation-sector statement consumable without re-opening pointwise
representative choices. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionProjectedL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : link ≠ distinguishedSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H link distinguishedSource)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B distinguishedSource k) link g₂)) :=
  let rightF :=
    fun C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      F (left, C)
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
      H N hN beta hbeta B link distinguishedSource link k g₂ rightF
  let hRight :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointKernelSectionRight_memLp_two_of_bounded
      H N hN beta hbeta B link distinguishedSource k g₂
      F hF bound hbound left
  let hQ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation_memLp_two
      H N hN beta hbeta B
      (target := link) (source := distinguishedSource)
      hRefNe hNoShare link k g₂ rightF hRight
  let hPq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_memLp_two
      H N hN beta hbeta B
      (target := link) (source := distinguishedSource)
      hRefNe hNoShare link k g₂ q hQ
  hPq.toLp
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
      H N hN beta hbeta B link distinguishedSource link k g₂ q)

/-- The local-mean L2 vector from PR #4738 is literally the L2 class of the
existing remote kernel-section fluctuation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionL2_eq_fluctuation_toLp
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : link ≠ distinguishedSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H link distinguishedSource)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionL2
        H N hN beta hbeta B link distinguishedSource hRefNe hNoShare
        k g₂ F hF bound hbound left =
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateKernelSectionFluctuation_memLp_two_of_remote
        H N hN beta hbeta B link distinguishedSource hRefNe hNoShare
        k g₂ F hF bound hbound left).toLp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
          H N hN beta hbeta B link distinguishedSource link k g₂
          (fun C => F (left, C))) := by
  rfl

/-- The concrete projection of the local-mean fluctuation is represented almost
everywhere by zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionProjection_ae_eq_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : link ≠ distinguishedSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H link distinguishedSource)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta B link distinguishedSource link k g₂
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
          H N hN beta hbeta B link distinguishedSource link k g₂
          (fun C => F (left, C))) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B distinguishedSource k) link g₂)]
      (0 : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) := by
  have hRight :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointKernelSectionRight_memLp_two_of_bounded
      H N hN beta hbeta B link distinguishedSource k g₂
      F hF bound hbound left
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_fluctuation_ae_eq_zero_of_memLp_two
      H N hN beta hbeta B
      (target := link) (source := distinguishedSource)
      hRefNe hNoShare link k g₂
      (fun C => F (left, C)) hRight

/-- Main fluctuation-sector theorem: the L2 projection of the canonical
local-mean vector is exactly zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionProjectedL2_eq_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : link ≠ distinguishedSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H link distinguishedSource)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionProjectedL2
        H N hN beta hbeta B link distinguishedSource hRefNe hNoShare
        k g₂ F hF bound hbound left = 0 := by
  let rightF :=
    fun C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      F (left, C)
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
      H N hN beta hbeta B link distinguishedSource link k g₂ rightF
  let hRight :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointKernelSectionRight_memLp_two_of_bounded
      H N hN beta hbeta B link distinguishedSource k g₂
      F hF bound hbound left
  let hQ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation_memLp_two
      H N hN beta hbeta B
      (target := link) (source := distinguishedSource)
      hRefNe hNoShare link k g₂ rightF hRight
  let p :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
      H N hN beta hbeta B link distinguishedSource link k g₂ q
  let hP :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_memLp_two
      H N hN beta hbeta B
      (target := link) (source := distinguishedSource)
      hRefNe hNoShare link k g₂ q hQ
  have hRep :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionProjectedL2
          H N hN beta hbeta B link distinguishedSource hRefNe hNoShare
          k g₂ F hF bound hbound left =ᵐ[
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B distinguishedSource k) link g₂)]
        p := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionProjectedL2,
      rightF, q, p, hRight, hQ, hP] using hP.coeFn_toLp
  have hZero :
      p =ᵐ[
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B distinguishedSource k) link g₂)]
        (0 : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) := by
    simpa [p, q, rightF] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionProjection_ae_eq_zero
        H N hN beta hbeta B link distinguishedSource hRefNe hNoShare
        k g₂ F hF bound hbound left
  apply Lp.ext
  filter_upwards [hRep, hZero] with C hRepC hZeroC
  rw [hRepC, hZeroC]
  simp

end

end MGAP4D.MathlibAnalytic
