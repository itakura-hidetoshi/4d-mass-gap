import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroFiniteSetProfileL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_finiteSetProductEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- Product of the centered physical-link Wilson-coordinate observables over a
finite selected set. The empty product is the constant observable one. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ :=
  ∏ edge ∈ s,
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge

@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_apply
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s A =
      ∏ edge ∈ s,
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge A := by
  simp [periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF]

@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_empty :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF ∅ = 1 := by
  simp [periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF]

/-- Inserting a fresh coordinate multiplies the existing finite-set product by
one new centered coordinate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_insert
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (edge : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hEdge : edge ∉ s) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF
        (insert edge s) =
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge *
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s := by
  simp [periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF,
    hEdge]

/-- The finite-set product splits into a selected coordinate and the product
on its erase-complement. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_eq_mul_erase
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (edge : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hEdge : edge ∈ s) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s =
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge *
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF
          (s.erase edge) := by
  rw [← Finset.insert_erase hEdge]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_insert
      (s.erase edge) edge (Finset.notMem_erase edge s)

/-- The finite-set product is constant along every unselected physical-link
fiber. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_offLinkFiberConstant_of_not_mem
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (edge : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hEdge : edge ∉ s) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
      edge
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s) := by
  intro A B hAgree
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_apply,
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_apply]
  apply Finset.prod_congr rfl
  intro selected hSelected
  apply
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
  apply hAgree selected
  intro hEq
  subst selected
  exact hEdge hSelected

/-- Haar averaging the finite-set product in any selected coordinate gives
zero. This is the induction step `F_(insert edge s) = centered edge * F_s`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_projection_eq_zero_of_mem
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (edge : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hEdge : edge ∈ s) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s) =
      fun _ => 0 := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_eq_mul_erase
      s edge hEdge]
  funext A
  change
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge *
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF
            (s.erase edge))
        A = 0
  rw [
    continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      edge
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF
        (s.erase edge))
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_offLinkFiberConstant_of_not_mem
        (s.erase edge) edge (Finset.notMem_erase edge s))
      A]
  have hZero := congrFun
    (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_projection_self_eq_zero
      edge) A
  rw [hZero, zero_mul]

/-- Haar averaging the finite-set product in any unselected coordinate fixes
it. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_projection_eq_self_of_not_mem
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (edge : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hEdge : edge ∉ s) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s) =
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s := by
  exact
    continuous_compact_oriented_singleLinkHeatBathProjection_fixes
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem edge
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_offLinkFiberConstant_of_not_mem
        s edge hEdge)

/-- Every finite selected-set product is nonzero, including the empty product.
If the Haar mean is nonzero, evaluate all selected coordinates at the identity;
if the mean is zero, evaluate them at the negative identity. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_ne_zero
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s ≠ 0 := by
  intro hZero
  by_cases hMean : specialUnitaryTwoWilsonEnergyHaarMean = 0
  · let A :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
      fun edge =>
        if edge ∈ s then specialUnitaryTwoNegativeIdentity else 1
    have hAt :
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF
            s A = 0 := by
      simpa using congrArg
        (fun F : BoundedContinuousFunction
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ =>
          F A)
        hZero
    have hEnergyNeg :
        specialUnitaryWilsonPlaquetteEnergy 2 specialUnitaryTwoNegativeIdentity ≠ 0 := by
      norm_num
    have hEach :
        ∀ edge ∈ s,
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
              edge A ≠ 0 := by
      intro edge hEdge
      simp [A,
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_apply,
        hEdge, hMean, hEnergyNeg]
    have hProd :
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF
            s A ≠ 0 := by
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_apply]
      exact Finset.prod_ne_zero_iff.mpr hEach
    exact hProd hAt
  · let A :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
      fun _ => 1
    have hAt :
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF
            s A = 0 := by
      simpa using congrArg
        (fun F : BoundedContinuousFunction
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ =>
          F A)
        hZero
    have hEnergyOne :
        specialUnitaryWilsonPlaquetteEnergy 2
            (1 : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Gauge) = 0 := by
      change specialUnitaryWilsonPlaquetteEnergy 2
        (1 : SpecialUnitaryMatrixGroup 2) = 0
      exact specialUnitaryWilsonPlaquetteEnergy_two_one
    have hEach :
        ∀ edge ∈ s,
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
              edge A ≠ 0 := by
      intro edge _hEdge
      simp [A,
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_apply,
        hEnergyOne, hMean]
    have hProd :
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF
            s A ≠ 0 := by
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_apply]
      exact Finset.prod_ne_zero_iff.mpr hEach
    exact hProd hAt

end

end MathlibAnalytic
end MGAP4D
