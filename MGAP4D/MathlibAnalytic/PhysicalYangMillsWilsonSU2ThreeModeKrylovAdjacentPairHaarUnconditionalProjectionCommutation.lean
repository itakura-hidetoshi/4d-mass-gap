import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSplitUpdateMeanIdentification
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSimpleCoreFubiniDensityBridge
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# P4-Q2-DB: TRUE original physical pair-Haar L² coordinate projections commute

CZ identified the actual CR pair-Haar Hilbert-L² orthogonal projection
with the literal CY Haar fiber mean on every bounded strongly measurable
representative. DA established that this CY fiber mean is CU's literal
Function.update Haar average, pointwise on the original physical left/
right spatial configuration. CU already proves those two-link means
commute by Fubini on genuine independent Haar.

Here we discharge the remaining two-step bounded-core identification:
one CU one-link Haar mean of a bounded strongly measurable F is again
bounded and strongly measurable, without treating an arbitrary L²
equivalence class as a pointwise function. Thus the actual two CR
projection composite on EVERY dense Lp.simpleFunc core vector is
identified a.e. with CU's iterated concrete Haar means.

CW's already proven dense-core extension removes the final hypothesis,
establishing UNCONDITIONAL full-L² commutation for the genuine original
pair-Haar projections. CQ and CS then give unconditional finite Haar
tensorization and constancy of the exact all-coordinate sweep.

These operators act on the independent pair-Haar REFERENCE probability,
not the interacting positive-beta Wilson conditional law. There is no
uniform Wilson spectral-gap claim or continuum Yang--Mills mass-gap claim.
No sorry, admit or new axiom.
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

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "muH" => normalizedCompactHaar G
local notation "JH" => Lp ℝ 2 muPair
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H N

/-- The literal true one-coordinate Haar mean preserves strong
measurability on the ACTUAL left/right physical joint configuration,
because CY gives a genuine measurable product split. -/
theorem p4Q2DB_actualPairHaarCoordinateMean_stronglyMeasurable
    (i : I) (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    StronglyMeasurable (p4Q2CU_actualPairHaarCoordinateMean H N i F) := by
  let e := p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i
  have hprod : StronglyMeasurable
      (fun p : ({j : I // j ≠ i} → G) × G => F (e.symm p)) :=
    hF.comp_measurable e.symm.measurable
  have hmean : StronglyMeasurable
      (fun a : {j : I // j ≠ i} → G =>
        ∫ u : G, F (e.symm (a, u)) ∂muH) :=
    hprod.integral_prod_right'
  have hjoint : StronglyMeasurable
      (fun z : Joint => ∫ u : G, F (e.symm ((e z).1, u)) ∂muH) :=
    hmean.comp_measurable (measurable_fst.comp e.measurable)
  have hfun :
      (fun z : Joint => ∫ u : G, F (e.symm ((e z).1, u)) ∂muH) =
        p4Q2CU_actualPairHaarCoordinateMean H N i F := by
    funext z
    exact p4Q2DA_actualPairHaar_splitFiberMean_eq_CU H N i F z
  rw [← hfun]
  exact hjoint

/-- Uniform pointwise norm bounds are preserved by the LITERAL original
one-link Haar mean on a bounded strongly measurable F. The proof is a
genuine probability-Haar integral bound, not a Wilson conditional law. -/
theorem p4Q2DB_actualPairHaarCoordinateMean_norm_le
    (i : I) (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M) (z : Joint) :
    ‖p4Q2CU_actualPairHaarCoordinateMean H N i F z‖ ≤ M := by
  let e := p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i
  have hsecSm : StronglyMeasurable
      (fun u : G => F (e.symm ((e z).1, u))) :=
    hF.comp_measurable
      (e.symm.measurable.comp (measurable_const.prodMk measurable_id))
  have hsecInt : Integrable
      (fun u : G => F (e.symm ((e z).1, u))) muH :=
    Integrable.of_bound hsecSm.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun u => hM _)
  rw [← p4Q2DA_actualPairHaar_splitFiberMean_eq_CU H N i F z]
  calc
    ‖∫ u : G, F (e.symm ((e z).1, u)) ∂muH‖ ≤
        ∫ u : G, ‖F (e.symm ((e z).1, u))‖ ∂muH :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _u : G, M ∂muH :=
      integral_mono_ae hsecInt.norm (integrable_const M)
        (Filter.Eventually.of_forall fun u => hM _)
    _ = M := by simp

/-- Exact ORIGINAL physical two-link Haar integral represents a double
ACTUAL CR Hilbert-L² orthogonal projection a.e. on every core vector.
This discharges CW's visible iterated-mean identification hypothesis:
the inner mean is strongly measurable and uniformly bounded, permitting
a SECOND application of DA's genuine Hilbert projection theorem. -/
theorem p4Q2DB_actualPairHaar_simpleCore_iteratedProjection_eq_HaarMeans
    (i j : I) (f : Lp.simpleFunc ℝ 2 muPair) :
    ((P i (P j (f : JH)) : JH) : Joint → ℝ) =ᵐ[muPair]
      p4Q2CU_actualPairHaarCoordinateMean H N i
        (p4Q2CU_actualPairHaarCoordinateMean H N j
          (Lp.simpleFunc.toSimpleFunc f)) := by
  let F : Joint → ℝ := Lp.simpleFunc.toSimpleFunc f
  obtain ⟨M, hM⟩ := (Lp.simpleFunc.toSimpleFunc f).exists_forall_norm_le
  have hF : StronglyMeasurable F :=
    Lp.simpleFunc.stronglyMeasurable f
  have hEq : F =ᵐ[muPair] (f : JH) :=
    Lp.simpleFunc.toSimpleFunc_eq_toFun f
  have hFirst : ((P j (f : JH) : JH) : Joint → ℝ) =ᵐ[muPair]
      p4Q2CU_actualPairHaarCoordinateMean H N j F :=
    p4Q2DA_actualPairHaarProjection_ae_eq_CUmean
      H N j (f : JH) F hF M hM hEq
  have hSecond :=
    p4Q2DA_actualPairHaarProjection_ae_eq_CUmean
      H N i (P j (f : JH))
        (p4Q2CU_actualPairHaarCoordinateMean H N j F)
        (p4Q2DB_actualPairHaarCoordinateMean_stronglyMeasurable H N j F hF)
        M (fun z =>
          p4Q2DB_actualPairHaarCoordinateMean_norm_le H N j F hF M hM z)
        hFirst.symm
  simpa [F] using hSecond

/-- UNCONDITIONAL commutation, with neither a retained-measurability
premise nor a synthetic Wilson law: these are the actual CR orthogonal
projections on the entire original physical independent pair-Haar L². -/
theorem p4Q2DB_actualPairHaarProjections_commute
    (i j : I) (x : JH) :
    P i (P j x) = P j (P i x) := by
  have hIdentify : ∀ (a b : I) (f : Lp.simpleFunc ℝ 2 muPair),
      ((P a (P b (f : JH)) : JH) : Joint → ℝ) =ᵐ[muPair]
        p4Q2CU_actualPairHaarCoordinateMean H N a
          (p4Q2CU_actualPairHaarCoordinateMean H N b
            (Lp.simpleFunc.toSimpleFunc f)) :=
    fun a b f =>
      p4Q2DB_actualPairHaar_simpleCore_iteratedProjection_eq_HaarMeans
        H N a b f
  exact p4Q2CW_actualPairHaarProjections_commute_of_iteratedMeanIdentification
    H N hIdentify i j x

/-- Full-L² finite-product Efron--Stein tensorization on the GENUINE
original independent physical pair-Haar reference law. No commutation
or stability hypothesis remains: the genuine projection commutation is
the theorem immediately above. -/
theorem p4Q2DB_actualPairHaar_unconditional_tensorization
    (x : JH) :
    ‖x - p4Q2CQ_projectionSweep P
      (@p4Q2CQ_finiteCoordinates I (p4Q2CR_actualJointIndexFintype H)) x‖ ^ 2 ≤
      ∑ i ∈ (@Finset.univ I (p4Q2CR_actualJointIndexFintype H)),
        ‖x - P i x‖ ^ 2 := by
  exact p4Q2CR_actualPairHaarProjectionSweep_tensorization_of_commuting
    H N (p4Q2DB_actualPairHaarProjections_commute H N) x

/-- The actual finite all-link Haar orthogonal-projection sweep is
pair-Haar-a.e. constant for EVERY physical Hilbert-L² vector, without
any commutation premise. This follows from genuine DB commutation and
CS's exact pre-existing common-fixed-sector classification. -/
theorem p4Q2DB_actualPairHaar_unconditional_sweep_aeConst
    (x : JH) :
    ∃ c : ℝ,
      (p4Q2CQ_projectionSweep P
        (p4Q2CQ_finiteCoordinates I) x : Joint → ℝ) =ᵐ[muPair]
          fun _ => c := by
  exact p4Q2CS_actualPairHaarSweep_aeConst_of_commuting
    H N (p4Q2DB_actualPairHaarProjections_commute H N) x

end ActualPairHaar
end

end MathlibAnalytic
end MGAP4D
