import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarProductFiberMeanCondExpIdentification
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Tactic

/-!
# P4-Q2-CW: genuine pair-Haar simple-core Fubini / full-L2 density bridge

CR constructed the actual off-coordinate Haar orthogonal projections in
the original spatial joint L². CS proved that their common fixed sector
is exactly the a.e.-constant sector. CU established the exact pointwise
commutation of independent coordinate Haar means on bounded functions;
CV identified the one-factor fiber mean with the genuine condExpL2.

This file establishes, for the SAME original physical pair-Haar joint L²:
* the SIMPLE-FUNCTION CORE is dense, without modifying the measure;
* every core vector has a strongly measurable, globally bounded
  representative on the actual physical joint configuration space;
* genuine original-coordinate Haar means commute on every such
  representative (unconditionally, for all physical coordinate pairs);
* equality of the two continuous Hilbert-L² coordinate-projection
  composites on just this core forces equality on ALL of L²;
* it suffices to identify the ACTUAL double-projected simple-core
  functions a.e. with the corresponding genuine CU iterated fiber means.

The iterated-mean identification needed to invoke the last theorem is
an EXPLICIT hypothesis, not an imported synthetic Wilson conditional.
A subsequent result must establish it by transporting CV to the physical
finite-product Haar coordinates. We make no unconditional claim about
CR full-L² commutation or a volume-uniform/continuum Yang--Mills gap.

Pinned Lean 4.30.0-rc2, mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
No sorry, admit, or new axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace

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

section ActualPairHaar
variable (H N : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "JH" => Lp ℝ 2 muPair
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H N

/-- The finite-valued/simple-function core of the ACTUAL physical
left/right pair-Haar L² is dense in the full Hilbert space. -/
theorem p4Q2CW_actualPairHaarSimpleCore_dense :
    Dense (Lp.simpleFunc ℝ 2 muPair : Set JH) := by
  exact Lp.simpleFunc.dense (E := ℝ) (μ := muPair)
    (p := (2 : ℝ≥0∞)) (by norm_num)

/-- Every actual pair-Haar L² simple-core vector has a bounded, strongly
measurable representative on the ORIGINAL left/right spatial carrier. -/
theorem p4Q2CW_actualPairHaarSimpleCore_boundedRepresentative
    (f : Lp.simpleFunc ℝ 2 muPair) :
    ∃ (F : Joint → ℝ) (M : ℝ),
      StronglyMeasurable F ∧
      (∀ z, ‖F z‖ ≤ M) ∧
      F =ᵐ[muPair] (f : JH) := by
  obtain ⟨M, hM⟩ :=
    (Lp.simpleFunc.toSimpleFunc f).exists_forall_norm_le
  exact ⟨(Lp.simpleFunc.toSimpleFunc f : Joint → ℝ), M,
    Lp.simpleFunc.stronglyMeasurable f, hM,
    Lp.simpleFunc.toSimpleFunc_eq_toFun f⟩

/-- Literal independent-coordinate Haar means commute on EVERY member of
the true physical pair-Haar dense simple-function core.  The statement
is pointwise on the canonical bounded representative, not a false point
evaluation of an arbitrary L² equivalence class. -/
theorem p4Q2CW_actualPairHaarSimpleCore_literalMeans_commute
    (i j : I) (f : Lp.simpleFunc ℝ 2 muPair) (z : Joint) :
    p4Q2CU_actualPairHaarCoordinateMean H N i
        (p4Q2CU_actualPairHaarCoordinateMean H N j
          (Lp.simpleFunc.toSimpleFunc f)) z =
      p4Q2CU_actualPairHaarCoordinateMean H N j
        (p4Q2CU_actualPairHaarCoordinateMean H N i
          (Lp.simpleFunc.toSimpleFunc f)) z := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  · obtain ⟨M, hM⟩ :=
      (Lp.simpleFunc.toSimpleFunc f).exists_forall_norm_le
    exact p4Q2CU_actualPairHaarCoordinateMean_commute H N i j hij
      (Lp.simpleFunc.toSimpleFunc f)
      (Lp.simpleFunc.stronglyMeasurable f) M hM z

/-- There is NO need to assume retained-coordinate measurability for
arbitrary L² quotient representatives: equality on the genuinely dense
physical bounded simple-function core suffices by continuity. -/
theorem p4Q2CW_actualPairHaarProjections_commute_of_simpleCore
    (i j : I)
    (hCore : ∀ f : Lp.simpleFunc ℝ 2 muPair,
      P i (P j (f : JH)) = P j (P i (f : JH)))
    (x : JH) :
    P i (P j x) = P j (P i x) := by
  let s : Set JH := Lp.simpleFunc ℝ 2 muPair
  have hs : Dense s := by
    simpa [s] using p4Q2CW_actualPairHaarSimpleCore_dense H N
  have hspan : Dense (↑(Submodule.span ℝ s) : Set JH) :=
    hs.mono (Submodule.subset_span)
  have hMaps : (P i).comp (P j) = (P j).comp (P i) := by
    apply ContinuousLinearMap.ext_on hspan
    intro y hy
    change y ∈ (Lp.simpleFunc ℝ 2 muPair : Set JH) at hy
    simpa only [ContinuousLinearMap.comp_apply] using hCore ⟨y, hy⟩
  simpa only [ContinuousLinearMap.comp_apply] using
    congrArg (fun T : JH →L[ℝ] JH => T x) hMaps

/-- The outstanding CV-to-physical transport obligation can be stated on
the bounded simple core, as ONE actual iterated-fiber conditional-expectation
identification; its reverse ordering is the same assumption with i,j swapped.
Under that visible assumption, CU plus density give full-L² commutation. -/
theorem p4Q2CW_actualPairHaarProjections_commute_of_iteratedMeanIdentification
    (hIdentify : ∀ (i j : I) (f : Lp.simpleFunc ℝ 2 muPair),
      ((P i (P j (f : JH)) : JH) : Joint → ℝ) =ᵐ[muPair]
        p4Q2CU_actualPairHaarCoordinateMean H N i
          (p4Q2CU_actualPairHaarCoordinateMean H N j
            (Lp.simpleFunc.toSimpleFunc f)))
    (i j : I) (x : JH) :
    P i (P j x) = P j (P i x) := by
  have hCore : ∀ f : Lp.simpleFunc ℝ 2 muPair,
      P i (P j (f : JH)) = P j (P i (f : JH)) := by
    intro f
    have hleft := hIdentify i j f
    have hright := hIdentify j i f
    have hmeans :
        p4Q2CU_actualPairHaarCoordinateMean H N i
            (p4Q2CU_actualPairHaarCoordinateMean H N j
              (Lp.simpleFunc.toSimpleFunc f)) =ᵐ[muPair]
          p4Q2CU_actualPairHaarCoordinateMean H N j
            (p4Q2CU_actualPairHaarCoordinateMean H N i
              (Lp.simpleFunc.toSimpleFunc f)) :=
      Filter.Eventually.of_forall
        (p4Q2CW_actualPairHaarSimpleCore_literalMeans_commute H N i j f)
    exact Lp.ext (hleft.trans (hmeans.trans hright.symm))
  exact p4Q2CW_actualPairHaarProjections_commute_of_simpleCore H N i j hCore x

/-- The finite genuine pair-Haar Efron--Stein sweep bound now requires
only the bounded simple-core identity, not all-L² Fubini hypotheses. -/
theorem p4Q2CW_actualPairHaar_tensorization_of_simpleCore
    (hCore : ∀ i j : I, ∀ f : Lp.simpleFunc ℝ 2 muPair,
      P i (P j (f : JH)) = P j (P i (f : JH)))
    (x : JH) :
    ‖x - p4Q2CQ_projectionSweep P
      (@p4Q2CQ_finiteCoordinates I (p4Q2CR_actualJointIndexFintype H)) x‖ ^ 2 ≤
      ∑ i ∈ (@Finset.univ I (p4Q2CR_actualJointIndexFintype H)),
        ‖x - P i x‖ ^ 2 := by
  have hc : ∀ i j : I, ∀ y : JH, P i (P j y) = P j (P i y) :=
    fun i j y =>
      p4Q2CW_actualPairHaarProjections_commute_of_simpleCore H N
        i j (hCore i j) y
  exact p4Q2CR_actualPairHaarProjectionSweep_tensorization_of_commuting
    H N hc x

/-- The same simple-core condition forces the actual finite Haar sweep
to be pair-Haar-a.e. constant, using CS's already established true
joint fixed-space characterization. -/
theorem p4Q2CW_actualPairHaar_sweep_aeConst_of_simpleCore
    (hCore : ∀ i j : I, ∀ f : Lp.simpleFunc ℝ 2 muPair,
      P i (P j (f : JH)) = P j (P i (f : JH)))
    (x : JH) :
    ∃ c : ℝ,
      (p4Q2CQ_projectionSweep P
        (p4Q2CQ_finiteCoordinates I) x : Joint → ℝ) =ᵐ[muPair]
          fun _ => c := by
  have hc : ∀ i j : I, ∀ y : JH, P i (P j y) = P j (P i y) :=
    fun i j y =>
      p4Q2CW_actualPairHaarProjections_commute_of_simpleCore H N
        i j (hCore i j) y
  exact p4Q2CS_actualPairHaarSweep_aeConst_of_commuting H N hc x

end ActualPairHaar
end

end MathlibAnalytic
end MGAP4D
