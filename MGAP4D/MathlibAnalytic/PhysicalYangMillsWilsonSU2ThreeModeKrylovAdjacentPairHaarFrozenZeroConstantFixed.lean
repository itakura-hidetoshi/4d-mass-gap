import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFrozenZeroGramRayleighRankOne
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateProductHaar
import MGAP4D.MathlibAnalytic.RealL2MeasurePreservingConstant
import Mathlib.Tactic

/-!
# P4: the genuine frozen beta-zero posterior fixes the physical constant receiver

Previous P4 packages retain the exact physical receiver
    v_f = lambda^(-1) ((S_beta f) o snd),
and the original posterior conditional-expectation projection
    Q_e = U.symm ∘ P_e ∘ U.

At beta=0 the original physical transfer fixes its canonical constant
unit vector and lambda=1. The existing measure-preserving right
pullback identifies the full physical pair-Haar receiver with the
actual pair-Haar L2 constant one.

The original beta-zero joint density equals one pair-Haar a.e., so the
half-density transport U sends that same receiver to a joint vector
whose representative is constant one joint-a.e. Any such constant
vector is fixed by the ORIGINAL ground-state joint one-link CondExpL2,
as a direct consequence of its membership in the retained L2
sub-sigma-algebra. Conjugating this fact proves Q_e v_one = v_one.

No new probability kernel, posterior, carrier or normalization is
introduced. No Dobrushin, spatial-support assumption, covariance/L2
identification, or continuum Yang-Mills mass-gap claim is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4ZeroConstTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4ZeroConstCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4ZeroConstSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4ZeroConstMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4ZeroConstBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4ZeroConstSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The ORIGINAL frozen beta-zero pair-Haar receiver of the canonical
physical constant unit is literally the pair-Haar L2 constant one.
The physical inverse-top-transfer normalization is preserved. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_zero_constantUnit_eq_one
    (H N : ℕ) (hN : 0 < N) :
    normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) =
      Lp.const 2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
        (1 : ℝ) := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN 0 (by norm_num)
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN 0 (by norm_num)
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let π := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let hSnd := spatialSlicePairHaar_snd_measurePreserving H N
  have hu : S u = u :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_zero_constantUnit
      H N hN
  have hT : ‖T‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_norm H N hN
  have hPull :
      Lp.compMeasurePreserving Prod.snd hSnd (Lp.const 2 μ (1 : ℝ)) =
        Lp.const 2 π (1 : ℝ) := by
    change (Lp.compMeasurePreservingₗᵢ ℝ Prod.snd hSnd)
      (Lp.const 2 μ (1 : ℝ)) = Lp.const 2 π (1 : ℝ)
    exact realL2_compMeasurePreserving_const_one Prod.snd hSnd
  change ‖T‖⁻¹ • Lp.compMeasurePreserving Prod.snd hSnd
      ((S u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        Lp ℝ 2 μ) = Lp.const 2 π (1 : ℝ)
  rw [hu, hT, inv_one, one_smul]
  change Lp.compMeasurePreserving Prod.snd hSnd (Lp.const 2 μ (1 : ℝ)) =
    Lp.const 2 π (1 : ℝ)
  exact hPull

/-- At frozen beta=0, the genuine half-density equivalence sends the
physical constant receiver to a representative that is one a.e. under
the ORIGINAL ground-state joint law, not just under a surrogate law. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_zero_joint_ae_one
    (H N : ℕ) (hN : 0 < N) :
    (fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
        H N hN 0 (by norm_num)
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)) z) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN 0 (by norm_num)] (fun _ => (1 : ℝ)) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let ν := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN 0 (by norm_num)
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
    H N hN 0 (by norm_num)
  have hνμ : ν = μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_zero_eq_pairHaar
      H N hN
  have hv : (fun z => v z) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    change (fun z => (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)) z) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      (fun _ => (1 : ℝ))
    rw [normalizedPhysicalOneSlabPairHaarReceiver_zero_constantUnit_eq_one H N hN]
    simpa using (Lp.coeFn_const
      (μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
      (p := 2) (c := (1 : ℝ)))
  have hvν : (fun z => v z) =ᵐ[ν] (fun _ => (1 : ℝ)) := by
    rw [hνμ]
    exact hv
  have hw : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN 0 (by norm_num) =ᵐ[ν] (fun _ => (1 : ℝ)) := by
    rw [hνμ]
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_zero_ae_eq_one
      H N hN
  have hU :
      (fun z => U v z) =ᵐ[ν]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
          H N hN 0 (by norm_num) v := by
    simpa only [U, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv_apply] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
        H N hN 0 (by norm_num) v)
  change (fun z => U v z) =ᵐ[ν] (fun _ => (1 : ℝ))
  filter_upwards [hU, hvν, hw] with z huz hvz hwz
  rw [huz]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
  rw [hvz, hwz]
  norm_num

/-- Any joint L2 vector represented by a constant is fixed by the
ORIGINAL one-link conditional expectation on the retained information. -/
theorem groundStateSpatialLinkCondExpL2_fixed_of_ae_const
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (c : ℝ)
    (hc : (fun x => z x) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta] (fun _ => c)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta e z = z := by
  let ν := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
  let hm := periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
    H N e
  have hz : z ∈ lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
        H N e) 2 ν := by
    apply mem_lpMeas_iff_aestronglyMeasurable.mpr
    exact aestronglyMeasurable_const.congr hc.symm
  letI : Fact
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
        H N e ≤
        (Prod.instMeasurableSpace : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) := ⟨hm⟩
  let q : lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
        H N e) 2 ν := ⟨z, hz⟩
  have hq : (condExpL2 ℝ ℝ hm (q :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) : lpMeas ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
            H N e) 2 ν) = q := by
    unfold condExpL2
    exact Submodule.orthogonalProjection_mem_subspace_eq_self q
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_apply]
  exact congrArg Subtype.val hq

/-- Therefore the ORIGINAL genuine transported posterior one-link
projection fixes the true beta-zero constant physical pair-Haar receiver.
No replacement by an independent Haar conditional expectation. -/
theorem pairHaarTransportedGroundStateSpatialLinkProjection_zero_fixed_constantReceiver
    (H N : ℕ) (hN : 0 < N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    pairHaarTransportedGroundStateSpatialLinkProjection
      H N hN 0 (by norm_num) e
      (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)) =
      normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) := by
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
    H N hN 0 (by norm_num)
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
    H N hN 0 (by norm_num) e
  have hconst : (fun z => (U v) z) =ᵐ[
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN 0 (by norm_num)] (fun _ => (1 : ℝ)) :=
    normalizedPhysicalOneSlabPairHaarReceiver_zero_joint_ae_one H N hN
  have hP : P (U v) = U v :=
    groundStateSpatialLinkCondExpL2_fixed_of_ae_const
      H N hN 0 (by norm_num) e (U v) 1 hconst
  change U.symm (P (U v)) = v
  rw [hP]
  exact U.symm_apply_apply v

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
