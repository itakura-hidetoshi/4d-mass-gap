import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullStrictness
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

universe v

/-- With the two open-half coordinates fixed, boundary-fibered assembly is a
continuous map of the shared boundary configuration.  The proof is entirely
coordinatewise: each full edge is either one of the two fixed open-half values
or one evaluation of the boundary `Pi`-coordinate. -/
theorem FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble_continuous_boundary
    {Edge : Type} [Fintype Edge]
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} [TopologicalSpace Value]
    (x y : P.OpenHalfConfiguration Value) :
    Continuous
      (fun b : P.BoundaryConfiguration Value =>
        P.boundaryFiberedAssemble b x y) := by
  apply continuous_pi
  intro e
  by_cases hpos : P.side e = ReflectionEdgeSide.positive
  · simp [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble, hpos]
    exact continuous_const
  · by_cases hneg : P.side e = ReflectionEdgeSide.negative
    · simp [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble, hpos, hneg]
      exact continuous_const
    · have hfixed : P.side e = ReflectionEdgeSide.fixed := by
        cases hside : P.side e <;> simp_all
      simpa [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble,
        hpos, hneg, hfixed] using
        (continuous_apply (⟨e, hfixed⟩ : P.FixedEdge) :
          Continuous (fun b : P.BoundaryConfiguration Value => b ⟨e, hfixed⟩))

local instance boundarySectionWeightContinuityNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundarySectionWeightContinuityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundarySectionWeightContinuityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundarySectionWeightContinuitySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundarySectionWeightContinuitySU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The purely spatial reflection-plane Wilson action is continuous on the full
finite `SU(N)` configuration space.  This is the restricted finite sum version
of the generic continuous compact Wilson action theorem. -/
theorem periodicHypercubicEvenSpatialCrossingWilsonAction_continuous
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    Continuous
      (periodicHypercubicEvenSpatialCrossingWilsonAction H N) := by
  classical
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN 0 (by positivity)
  unfold periodicHypercubicEvenSpatialCrossingWilsonAction
  apply continuous_finset_sum
  intro p _hp
  by_cases hs : periodicHypercubicEvenSpatialCrossingPlaquette p
  · simp only [propositionIndicator, if_pos hs]
    have hHol : Continuous
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          periodicHypercubicPlaquetteHolonomy A p) := by
      simpa [C] using continuous_compact_oriented_plaquetteHolonomy C p
    exact (continuous_specialUnitaryWilsonPlaquetteEnergy N).comp hHol
  · simp [propositionIndicator, hs]
    exact continuous_const

/-- The fixed-plane spatial Wilson Boltzmann weight is continuous as a function
of the physical shared-boundary configuration. -/
theorem periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight_continuous
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) :
    Continuous
      (periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
        H N beta) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  have hAssemble : Continuous
      (fun b : P.BoundaryConfiguration (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        P.boundaryFiberedAssemble b (fun _ => 1) (fun _ => 1)) :=
    P.boundaryFiberedAssemble_continuous_boundary (fun _ => 1) (fun _ => 1)
  unfold periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
  unfold periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight
  exact Real.continuous_exp.comp
    (continuous_const.mul
      ((periodicHypercubicEvenSpatialCrossingWilsonAction_continuous H N hN).comp
        hAssemble))

/-- The physical scalar boundary Gram coefficient is continuous. -/
theorem periodicHypercubicEvenBoundaryGramCoefficient_continuous
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Continuous
      (periodicHypercubicEvenBoundaryGramCoefficient H 2 (by norm_num) beta hbeta) := by
  unfold periodicHypercubicEvenBoundaryGramCoefficient
  exact
    (periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight_continuous
      H 2 (by norm_num) beta).div_const _

/-- Named wrapper for the exact residual boundary product.  Keeping the large
finite-lattice product behind one definition avoids forcing the elaborator to
normalize its full dependent index expression while matching continuity
combinators.  The definition is literally the original residual interaction. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalResidualBoundaryProductFn
    (H : ℕ)
    (beta : ℝ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 → ℝ :=
  fun b =>
    ∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H,
      specialUnitaryWilsonRelativeKernel 2 beta
        (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p)
        1

/-- Continuity of the named exact residual boundary product. -/
set_option maxHeartbeats 2000000 in
theorem periodicHypercubicEvenPositiveBoundaryTemporalResidualBoundaryProductFn_continuous
    (H : ℕ)
    (beta : ℝ) :
    Continuous
      (periodicHypercubicEvenPositiveBoundaryTemporalResidualBoundaryProductFn
        H beta) := by
  unfold periodicHypercubicEvenPositiveBoundaryTemporalResidualBoundaryProductFn
  apply continuous_finset_prod
  intro p _hp
  exact (continuous_specialUnitaryWilsonRelativeKernel 2 beta).comp
    ((periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg_continuous
      H p).prodMk continuous_const)

/-- The exact residual boundary factor appearing on the canonical four-companion
section is continuous.  This keeps the original public theorem statement while
routing elaboration through the named finite-product wrapper above. -/
set_option maxHeartbeats 2000000 in
theorem periodicHypercubicEvenPositiveBoundaryTemporalResidualBoundaryProduct_continuous
    (H : ℕ)
    (beta : ℝ) :
    Continuous
      (fun b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 =>
        ∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H,
          specialUnitaryWilsonRelativeKernel 2 beta
            (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p)
            1) := by
  simpa only [periodicHypercubicEvenPositiveBoundaryTemporalResidualBoundaryProductFn] using
    periodicHypercubicEvenPositiveBoundaryTemporalResidualBoundaryProductFn_continuous H beta

/-- The complete boundary prefactor in the actual four-companion section
factorization is continuous.  In particular its measurability can now be
obtained without normalizing the giant boundary × open-half dependent type. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor_continuous
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Continuous
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor
        H beta hbeta) := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor
  exact
    (Real.continuous_sqrt.comp
      (periodicHypercubicEvenBoundaryGramCoefficient_continuous H beta hbeta)).mul
    (periodicHypercubicEvenPositiveBoundaryTemporalResidualBoundaryProduct_continuous
      H beta)

end

end MathlibAnalytic
end MGAP4D
