import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeaturePolynomialClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Topology
open scoped BigOperators

noncomputable section

local instance boundaryPositiveGramPlaquetteGeneratorNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryPositiveGramPlaquetteGeneratorTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryPositiveGramPlaquetteGeneratorCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

/-- Membership of the strict-positive action in a concrete continuous
Wilson/cylinder subalgebra reduces to membership of its finitely many actual
plaquette-energy summands.  No density hypothesis is introduced here: the
input is exactly a continuous representative in the same algebra for each
single finite plaquette term. -/
theorem
    periodicHypercubicEvenBoundaryPositiveWilsonActionContinuousMap_mem_of_plaquette_representatives
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (A : Subalgebra ℝ
      C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ))
    (hPlaquette :
      ∀ p : PeriodicHypercubicEvenPlaquette H,
        ∃ f : C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
              (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ),
          f ∈ A ∧
            ∀ x,
              f x =
                propositionIndicator
                  (periodicHypercubicEvenStrictPositivePlaquette p)
                  (specialUnitaryWilsonPlaquetteEnergy N
                    (periodicHypercubicPlaquetteHolonomy
                      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
                        b x (fun _ => 1)) p))) :
    periodicHypercubicEvenBoundaryPositiveWilsonActionContinuousMap H N hN b ∈ A := by
  classical
  let f : PeriodicHypercubicEvenPlaquette H →
      C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ) :=
    fun p => Classical.choose (hPlaquette p)
  have hf_mem : ∀ p, f p ∈ A := by
    intro p
    exact (Classical.choose_spec (hPlaquette p)).1
  have hf_apply : ∀ p x,
      f p x =
        propositionIndicator
          (periodicHypercubicEvenStrictPositivePlaquette p)
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy
              ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
                b x (fun _ => 1)) p)) := by
    intro p x
    exact (Classical.choose_spec (hPlaquette p)).2 x
  have hsum : (∑ p : PeriodicHypercubicEvenPlaquette H, f p) ∈ A := by
    exact A.sum_mem fun p _hp => hf_mem p
  have hsum_eq :
      (∑ p : PeriodicHypercubicEvenPlaquette H, f p) =
        periodicHypercubicEvenBoundaryPositiveWilsonActionContinuousMap H N hN b := by
    ext x
    simp [periodicHypercubicEvenBoundaryPositiveWilsonActionContinuousMap,
      periodicHypercubicEvenPositiveWilsonAction, hf_apply]
  rw [hsum_eq] at hsum
  exact hsum

/-- The boundary-adjacent temporal action has the same finite-generator
reduction.  Boundary dependence is retained in the individual plaquette
representatives, while the ambient subalgebra `A` is fixed.  This is the form
needed later to pass the boundary integral through one common C⁰ closure. -/
theorem
    periodicHypercubicEvenBoundaryPositiveBoundaryTemporalWilsonActionContinuousMap_mem_of_plaquette_representatives
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (A : Subalgebra ℝ
      C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ))
    (hPlaquette :
      ∀ p : PeriodicHypercubicEvenPlaquette H,
        ∃ f : C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
              (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ),
          f ∈ A ∧
            ∀ x,
              f x =
                propositionIndicator
                  (periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p)
                  (specialUnitaryWilsonPlaquetteEnergy N
                    (periodicHypercubicPlaquetteHolonomy
                      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
                        b x (fun _ => 1)) p))) :
    periodicHypercubicEvenBoundaryPositiveBoundaryTemporalWilsonActionContinuousMap
        H N hN b ∈ A := by
  classical
  let f : PeriodicHypercubicEvenPlaquette H →
      C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ) :=
    fun p => Classical.choose (hPlaquette p)
  have hf_mem : ∀ p, f p ∈ A := by
    intro p
    exact (Classical.choose_spec (hPlaquette p)).1
  have hf_apply : ∀ p x,
      f p x =
        propositionIndicator
          (periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p)
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy
              ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
                b x (fun _ => 1)) p)) := by
    intro p x
    exact (Classical.choose_spec (hPlaquette p)).2 x
  have hsum : (∑ p : PeriodicHypercubicEvenPlaquette H, f p) ∈ A := by
    exact A.sum_mem fun p _hp => hf_mem p
  have hsum_eq :
      (∑ p : PeriodicHypercubicEvenPlaquette H, f p) =
        periodicHypercubicEvenBoundaryPositiveBoundaryTemporalWilsonActionContinuousMap
          H N hN b := by
    ext x
    simp [periodicHypercubicEvenBoundaryPositiveBoundaryTemporalWilsonActionContinuousMap,
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction, hf_apply]
  rw [hsum_eq] at hsum
  exact hsum

/-- The fixed-boundary completed-positive Gram feature is in the uniform
closure as soon as the actual single-plaquette terms have representatives in
one common finite Wilson/cylinder subalgebra.  The finite sums build the two
actions, and Mathlib's compact-range polynomial approximation from the previous
layer builds the Gibbs exponentials. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMap_mem_topologicalClosure_of_plaquette_representatives
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (A : Subalgebra ℝ
      C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ))
    (hBulkPlaquette :
      ∀ p : PeriodicHypercubicEvenPlaquette H,
        ∃ f : C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
              (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ),
          f ∈ A ∧
            ∀ x,
              f x =
                propositionIndicator
                  (periodicHypercubicEvenStrictPositivePlaquette p)
                  (specialUnitaryWilsonPlaquetteEnergy N
                    (periodicHypercubicPlaquetteHolonomy
                      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
                        b x (fun _ => 1)) p)))
    (hTemporalPlaquette :
      ∀ p : PeriodicHypercubicEvenPlaquette H,
        ∃ f : C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
              (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ),
          f ∈ A ∧
            ∀ x,
              f x =
                propositionIndicator
                  (periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p)
                  (specialUnitaryWilsonPlaquetteEnergy N
                    (periodicHypercubicPlaquetteHolonomy
                      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
                        b x (fun _ => 1)) p))) :
    (⟨periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b,
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_continuous_openHalf
        H N hN beta hbeta b⟩ :
      C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ)) ∈ A.topologicalClosure := by
  have hBulk :=
    periodicHypercubicEvenBoundaryPositiveWilsonActionContinuousMap_mem_of_plaquette_representatives
      H N hN b A hBulkPlaquette
  have hTemporal :=
    periodicHypercubicEvenBoundaryPositiveBoundaryTemporalWilsonActionContinuousMap_mem_of_plaquette_representatives
      H N hN b A hTemporalPlaquette
  exact
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMap_mem_topologicalClosure_of_actions_mem
      H N hN beta hbeta b A hBulk hTemporal

end

end MathlibAnalytic
end MGAP4D
