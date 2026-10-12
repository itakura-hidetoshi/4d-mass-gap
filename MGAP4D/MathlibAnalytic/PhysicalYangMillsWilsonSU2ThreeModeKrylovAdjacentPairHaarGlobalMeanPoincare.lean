import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUnconditionalProjectionCommutation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

/-!
# P4-Q2-DC: genuine original pair-Haar global mean and Efron--Stein Poincare

DB proved genuine original left/right spatial pair-Haar coordinate L²
orthogonal projections commute UNCONDITIONALLY. CQ's finite tensorization
and CS's exact common fixed sector then give a finite all-coordinate
Haar sweep with a.e.-constant output.

Here every single CR projection is shown to preserve the TRUE full
pair-Haar integral using the pinned mathlib integral_condExpL2_eq.
This property iterates over the actual finite physical coordinate
sweep. Because the sweep output is a.e. constant and the original
pair-Haar law is probability, that constant is exactly the ORIGINAL
global Haar expectation, not an unspecified constant.

Substitute this equality in DB's unconditional Efron--Stein bound to
obtain the exact all-coordinate Poincare inequality, coefficient ONE:

  ‖f - (∫ f dμ_pair) const-Lp‖² ≤ ∑_i ‖f - P_i f‖².

This is a quantitative bound only for the independent true pair-Haar
REFERENCE law. No original positive-beta Wilson coercivity, uniform
Wilson spectral gap, continuum strong limit or 4D Yang--Mills mass gap
is claimed or inferred.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 2400000
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

section ActualPairHaar
variable (H N : ℕ)

/-- Use the exact same finite physical joint-coordinate enumeration as
the original CR/CQ operator tensorization, rather than the alternative
inferred sum Fintype, which can have a different list ordering. -/
local instance p4Q2DC_actualJointIndexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H) :=
  p4Q2CR_actualJointIndexFintype H

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "JH" => Lp ℝ 2 muPair
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H N

/-- Every actual CR physical pair-Haar orthogonal projection preserves
the full original pair-Haar integral. The set used in the intrinsic
L² conditional-expectation characterization is precisely Set.univ. -/
theorem p4Q2DC_actualPairHaarCoordinateProjection_integral_eq
    (i : I) (x : JH) :
    ∫ z : Joint, (P i x : JH) z ∂muPair =
      ∫ z : Joint, x z ∂muPair := by
  have hProj : (P i x : JH) =
      (condExpL2 ℝ ℝ
        (p4Q2CR_actualPairHaarOffCoordinateSigma_le H N i) x : JH) := by
    rfl
  rw [hProj]
  simpa only [setIntegral_univ] using
    (integral_condExpL2_eq
      (p4Q2CR_actualPairHaarOffCoordinateSigma_le H N i)
      x (show MeasurableSet[
        p4Q2CR_actualPairHaarOffCoordinateSigma H N i]
        (Set.univ : Set Joint) from MeasurableSet.univ)
      (measure_ne_top _ _))

/-- Every actual finite composition of original physical coordinate
Haar orthogonal projections preserves the true global Haar integral,
even before applying the all-coordinate constancy theorem. -/
theorem p4Q2DC_actualPairHaar_projectionSweep_integral_eq
    (l : List I) (x : JH) :
    ∫ z : Joint, (p4Q2CQ_projectionSweep P l x : JH) z ∂muPair =
      ∫ z : Joint, x z ∂muPair := by
  induction l generalizing x with
  | nil =>
      simp [p4Q2CQ_projectionSweep]
  | cons i rest ih =>
      change ∫ z : Joint,
          (p4Q2CQ_projectionSweep P rest (P i x) : JH) z ∂muPair =
            ∫ z : Joint, x z ∂muPair
      rw [ih (P i x), p4Q2DC_actualPairHaarCoordinateProjection_integral_eq H N i x]

/-- The CR-indexed finite sweep is fixed by every actual Haar
coordinate projection, irrespective of the different alternative
Fintype used by older CS/DB presentation theorems. -/
private theorem p4Q2DC_actualPairHaar_crSweep_fixed
    (x : JH) (i : I) :
    P i (p4Q2CQ_projectionSweep P
        (@p4Q2CQ_finiteCoordinates I (p4Q2CR_actualJointIndexFintype H)) x) =
      p4Q2CQ_projectionSweep P
        (@p4Q2CQ_finiteCoordinates I (p4Q2CR_actualJointIndexFintype H)) x := by
  classical
  let l : List I :=
    @p4Q2CQ_finiteCoordinates I (p4Q2CR_actualJointIndexFintype H)
  have hi : i ∈ l := by
    dsimp [l, p4Q2CQ_finiteCoordinates]
    apply List.mem_ofFn.mpr
    refine ⟨(Fintype.equivFin I) i, ?_⟩
    simp
  have hId : ∀ j : I, ∀ y : JH, P j (P j y) = P j y :=
    p4Q2CR_actualPairHaarCoordinateProjection_idempotent H N
  have hComm : ∀ j k : I, ∀ y : JH, P j (P k y) = P k (P j y) :=
    p4Q2DB_actualPairHaarProjections_commute H N
  have hFixed : ∀ (rest : List I), i ∈ rest →
      ∀ y : JH, P i (p4Q2CQ_projectionSweep P rest y) =
        p4Q2CQ_projectionSweep P rest y := by
    intro rest
    induction rest with
    | nil =>
        intro hnil
        simp at hnil
    | cons j tail ih =>
        intro hmem y
        simp only [List.mem_cons] at hmem
        rcases hmem with hij | hit
        · subst j
          change P i (p4Q2CQ_projectionSweep P tail (P i y)) =
            p4Q2CQ_projectionSweep P tail (P i y)
          rw [p4Q2CQ_projection_commute_sweep P hComm i tail (P i y),
            hId i y]
        · change P i (p4Q2CQ_projectionSweep P tail (P j y)) =
            p4Q2CQ_projectionSweep P tail (P j y)
          exact ih hit (P j y)
  exact hFixed l hi x

/-- The CR-indexed finite sweep has a.e.-constant output. This uses
actual DB commutation and the CS characterization of the common fixed
sector, without identifying two differently enumerated Fintype lists. -/
private theorem p4Q2DC_actualPairHaar_crSweep_aeConst
    (x : JH) :
    ∃ c : ℝ,
      (p4Q2CQ_projectionSweep P
        (@p4Q2CQ_finiteCoordinates I (p4Q2CR_actualJointIndexFintype H)) x :
          Joint → ℝ) =ᵐ[muPair] fun _ => c := by
  apply (p4Q2CS_actualPairHaar_allCoordinateFixed_iff_aeConst H N _).mp
  intro i
  exact p4Q2DC_actualPairHaar_crSweep_fixed H N x i

/-- The actual full finite independent pair-Haar sweep is not merely
a.e.-constant: it is exactly the ORIGINAL physical pair-Haar global
expectation. No synthetic expectation functional enters. -/
theorem p4Q2DC_actualPairHaar_sweep_ae_eq_globalMean
    (x : JH) :
    (p4Q2CQ_projectionSweep P (p4Q2CQ_finiteCoordinates I) x :
      Joint → ℝ) =ᵐ[muPair]
        (fun _ : Joint => ∫ z : Joint, x z ∂muPair) := by
  obtain ⟨c, hc⟩ :=
    p4Q2DC_actualPairHaar_crSweep_aeConst H N x
  have hInt :=
    p4Q2DC_actualPairHaar_projectionSweep_integral_eq H N
      (p4Q2CQ_finiteCoordinates I) x
  have hcVal : c = ∫ z : Joint, x z ∂muPair := by
    calc
      c = ∫ z : Joint, c ∂muPair := by simp
      _ = ∫ z : Joint,
          (p4Q2CQ_projectionSweep P (p4Q2CQ_finiteCoordinates I) x : JH) z
          ∂muPair :=
        (integral_congr_ae hc).symm
      _ = ∫ z : Joint, x z ∂muPair := hInt
  simpa only [hcVal] using hc

/-- In the original physical joint pair-Haar L², the finite sweep is
exactly the Hilbert class of the constant true Haar mean. -/
theorem p4Q2DC_actualPairHaar_sweep_eq_globalMeanLp
    (x : JH) :
    p4Q2CQ_projectionSweep P (p4Q2CQ_finiteCoordinates I) x =
      Lp.const 2 muPair (∫ z : Joint, x z ∂muPair) := by
  apply Lp.ext
  have hConst :
      (Lp.const 2 muPair (∫ z : Joint, x z ∂muPair) : Joint → ℝ) =ᵐ[muPair]
        (fun _ : Joint => ∫ z : Joint, x z ∂muPair) := by
    simpa only [Function.const_apply] using
      (Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := muPair)
        (c := ∫ z : Joint, x z ∂muPair))
  exact (p4Q2DC_actualPairHaar_sweep_ae_eq_globalMean H N x).trans
    hConst.symm

/-- TRUE independent physical joint pair-Haar Hilbert-L² Poincare /
Efron--Stein inequality with exact constant ONE. This constant applies
only to the Haar reference coordinate residual energy; a reverse
positive-beta Wilson comparison is a separate unresolved obligation. -/
theorem p4Q2DC_actualPairHaar_globalMeanPoincare
    (x : JH) :
    ‖x - Lp.const 2 muPair (∫ z : Joint, x z ∂muPair)‖ ^ 2 ≤
      ∑ i ∈ (@Finset.univ I (p4Q2CR_actualJointIndexFintype H)),
        ‖x - P i x‖ ^ 2 := by
  rw [← p4Q2DC_actualPairHaar_sweep_eq_globalMeanLp H N x]
  exact p4Q2DB_actualPairHaar_unconditional_tensorization H N x

end ActualPairHaar
end

end MathlibAnalytic
end MGAP4D
