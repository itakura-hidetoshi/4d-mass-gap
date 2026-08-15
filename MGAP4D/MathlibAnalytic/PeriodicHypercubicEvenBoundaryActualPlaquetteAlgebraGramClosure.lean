import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeaturePlaquetteGeneratorClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Topology
open scoped BigOperators

noncomputable section

local instance boundaryActualPlaquetteAlgebraNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryActualPlaquetteAlgebraTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryActualPlaquetteAlgebraCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

/-- One actual Wilson plaquette energy on the positive open-half fiber, with
shared boundary data fixed.  This is the elementary continuous generator from
which both positive action sectors are assembled. -/
noncomputable def periodicHypercubicEvenBoundaryPlaquetteEnergyContinuousMap
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (p : PeriodicHypercubicEvenPlaquette H) :
    C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN 0 (by positivity)
  have hAssemble : Continuous
      (fun x : P.OpenHalfConfiguration (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        P.boundaryFiberedAssemble b x (fun _ => 1)) :=
    P.boundaryFiberedAssemble_continuous_positive b (fun _ => 1)
  have hHol : Continuous
      (fun A : PeriodicHypercubicEvenEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicPlaquetteHolonomy A p) := by
    simpa [C] using continuous_compact_oriented_plaquetteHolonomy C p
  exact
    ⟨fun x => specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy
          (P.boundaryFiberedAssemble b x (fun _ => 1)) p),
      ((continuous_specialUnitaryWilsonPlaquetteEnergy N).comp hHol).comp hAssemble⟩

/-- All actual boundary-fibered single-plaquette energies generate one common
real subalgebra on the positive open-half configuration space.  The generator
set ranges over every shared boundary configuration, so the algebra itself is
independent of the boundary later fixed in the Gram feature. -/
noncomputable def periodicHypercubicEvenBoundaryActualPlaquetteAlgebra
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    Subalgebra ℝ
      C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ) :=
  Algebra.adjoin ℝ
    (Set.range fun z :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
        PeriodicHypercubicEvenPlaquette H =>
      periodicHypercubicEvenBoundaryPlaquetteEnergyContinuousMap
        H N hN z.1 z.2)

/-- Every actual boundary-fibered plaquette energy is one of the canonical
`Algebra.adjoin` generators. -/
theorem periodicHypercubicEvenBoundaryPlaquetteEnergyContinuousMap_mem_actualPlaquetteAlgebra
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenBoundaryPlaquetteEnergyContinuousMap H N hN b p ∈
      periodicHypercubicEvenBoundaryActualPlaquetteAlgebra H N hN := by
  apply Algebra.subset_adjoin
  exact ⟨(b, p), rfl⟩

/-- Strict-positive selection of a single actual plaquette generator. -/
noncomputable def periodicHypercubicEvenBoundaryPositivePlaquetteTermContinuousMap
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (p : PeriodicHypercubicEvenPlaquette H) :
    C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ) := by
  classical
  exact if periodicHypercubicEvenStrictPositivePlaquette p then
    periodicHypercubicEvenBoundaryPlaquetteEnergyContinuousMap H N hN b p
  else 0

@[simp] theorem periodicHypercubicEvenBoundaryPositivePlaquetteTermContinuousMap_apply
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (p : PeriodicHypercubicEvenPlaquette H)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryPositivePlaquetteTermContinuousMap
        H N hN b p x =
      propositionIndicator
        (periodicHypercubicEvenStrictPositivePlaquette p)
        (specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
              b x (fun _ => 1)) p)) := by
  classical
  by_cases hp : periodicHypercubicEvenStrictPositivePlaquette p
  · simp [periodicHypercubicEvenBoundaryPositivePlaquetteTermContinuousMap,
      periodicHypercubicEvenBoundaryPlaquetteEnergyContinuousMap,
      propositionIndicator, hp]
  · simp [periodicHypercubicEvenBoundaryPositivePlaquetteTermContinuousMap,
      propositionIndicator, hp]

/-- Positive-boundary-temporal selection of a single actual plaquette
generator. -/
noncomputable def
    periodicHypercubicEvenBoundaryPositiveBoundaryTemporalPlaquetteTermContinuousMap
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (p : PeriodicHypercubicEvenPlaquette H) :
    C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ) := by
  classical
  exact if periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p then
    periodicHypercubicEvenBoundaryPlaquetteEnergyContinuousMap H N hN b p
  else 0

@[simp] theorem
    periodicHypercubicEvenBoundaryPositiveBoundaryTemporalPlaquetteTermContinuousMap_apply
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (p : PeriodicHypercubicEvenPlaquette H)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryPositiveBoundaryTemporalPlaquetteTermContinuousMap
        H N hN b p x =
      propositionIndicator
        (periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p)
        (specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
              b x (fun _ => 1)) p)) := by
  classical
  by_cases hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p
  · simp [periodicHypercubicEvenBoundaryPositiveBoundaryTemporalPlaquetteTermContinuousMap,
      periodicHypercubicEvenBoundaryPlaquetteEnergyContinuousMap,
      propositionIndicator, hp]
  · simp [periodicHypercubicEvenBoundaryPositiveBoundaryTemporalPlaquetteTermContinuousMap,
      propositionIndicator, hp]

/-- Every strict-positive selected plaquette term belongs to the common actual
plaquette algebra: it is either a generator or zero. -/
theorem periodicHypercubicEvenBoundaryPositivePlaquetteTermContinuousMap_mem_actualPlaquetteAlgebra
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenBoundaryPositivePlaquetteTermContinuousMap H N hN b p ∈
      periodicHypercubicEvenBoundaryActualPlaquetteAlgebra H N hN := by
  classical
  by_cases hp : periodicHypercubicEvenStrictPositivePlaquette p
  · simpa [periodicHypercubicEvenBoundaryPositivePlaquetteTermContinuousMap, hp] using
      periodicHypercubicEvenBoundaryPlaquetteEnergyContinuousMap_mem_actualPlaquetteAlgebra
        H N hN b p
  · simp [periodicHypercubicEvenBoundaryPositivePlaquetteTermContinuousMap, hp]

/-- Every positive-boundary-temporal selected plaquette term belongs to the
same common actual plaquette algebra. -/
theorem
    periodicHypercubicEvenBoundaryPositiveBoundaryTemporalPlaquetteTermContinuousMap_mem_actualPlaquetteAlgebra
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenBoundaryPositiveBoundaryTemporalPlaquetteTermContinuousMap
        H N hN b p ∈
      periodicHypercubicEvenBoundaryActualPlaquetteAlgebra H N hN := by
  classical
  by_cases hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p
  · simpa [periodicHypercubicEvenBoundaryPositiveBoundaryTemporalPlaquetteTermContinuousMap,
      hp] using
      periodicHypercubicEvenBoundaryPlaquetteEnergyContinuousMap_mem_actualPlaquetteAlgebra
        H N hN b p
  · simp [periodicHypercubicEvenBoundaryPositiveBoundaryTemporalPlaquetteTermContinuousMap,
      hp]

/-- The actual strict-positive Wilson action belongs to the common plaquette
algebra, with no action-level membership hypothesis. -/
theorem periodicHypercubicEvenBoundaryPositiveWilsonActionContinuousMap_mem_actualPlaquetteAlgebra
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryPositiveWilsonActionContinuousMap H N hN b ∈
      periodicHypercubicEvenBoundaryActualPlaquetteAlgebra H N hN := by
  apply
    periodicHypercubicEvenBoundaryPositiveWilsonActionContinuousMap_mem_of_plaquette_representatives
      H N hN b (periodicHypercubicEvenBoundaryActualPlaquetteAlgebra H N hN)
  intro p
  refine ⟨periodicHypercubicEvenBoundaryPositivePlaquetteTermContinuousMap
    H N hN b p, ?_, ?_⟩
  · exact
      periodicHypercubicEvenBoundaryPositivePlaquetteTermContinuousMap_mem_actualPlaquetteAlgebra
        H N hN b p
  · intro x
    exact periodicHypercubicEvenBoundaryPositivePlaquetteTermContinuousMap_apply
      H N hN b p x

/-- The actual positive-boundary-temporal Wilson action belongs to the same
common plaquette algebra. -/
theorem
    periodicHypercubicEvenBoundaryPositiveBoundaryTemporalWilsonActionContinuousMap_mem_actualPlaquetteAlgebra
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryPositiveBoundaryTemporalWilsonActionContinuousMap
        H N hN b ∈
      periodicHypercubicEvenBoundaryActualPlaquetteAlgebra H N hN := by
  apply
    periodicHypercubicEvenBoundaryPositiveBoundaryTemporalWilsonActionContinuousMap_mem_of_plaquette_representatives
      H N hN b (periodicHypercubicEvenBoundaryActualPlaquetteAlgebra H N hN)
  intro p
  refine ⟨periodicHypercubicEvenBoundaryPositiveBoundaryTemporalPlaquetteTermContinuousMap
    H N hN b p, ?_, ?_⟩
  · exact
      periodicHypercubicEvenBoundaryPositiveBoundaryTemporalPlaquetteTermContinuousMap_mem_actualPlaquetteAlgebra
        H N hN b p
  · intro x
    exact
      periodicHypercubicEvenBoundaryPositiveBoundaryTemporalPlaquetteTermContinuousMap_apply
        H N hN b p x

/-- The completed-positive Wilson amplitude on every fixed boundary fiber lies
in the C⁰ closure of one boundary-independent actual plaquette algebra. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitudeContinuousMap_mem_actualPlaquetteAlgebra_topologicalClosure
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitudeContinuousMap
        H N hN beta b ∈
      (periodicHypercubicEvenBoundaryActualPlaquetteAlgebra H N hN).topologicalClosure := by
  exact
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitudeContinuousMap_mem_topologicalClosure_of_actions_mem
      H N hN beta b
      (periodicHypercubicEvenBoundaryActualPlaquetteAlgebra H N hN)
      (periodicHypercubicEvenBoundaryPositiveWilsonActionContinuousMap_mem_actualPlaquetteAlgebra
        H N hN b)
      (periodicHypercubicEvenBoundaryPositiveBoundaryTemporalWilsonActionContinuousMap_mem_actualPlaquetteAlgebra
        H N hN b)

/-- In particular the actual fixed-boundary Gram kernel feature `K(b,·)` lies
in the C⁰ closure of the same boundary-independent actual plaquette algebra.
This removes both action-membership assumptions from the previous polynomial
closure layer. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMap_mem_actualPlaquetteAlgebra_topologicalClosure
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    (⟨periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b,
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_continuous_openHalf
        H N hN beta hbeta b⟩ :
      C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ)) ∈
      (periodicHypercubicEvenBoundaryActualPlaquetteAlgebra H N hN).topologicalClosure := by
  exact
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMap_mem_topologicalClosure_of_actions_mem
      H N hN beta hbeta b
      (periodicHypercubicEvenBoundaryActualPlaquetteAlgebra H N hN)
      (periodicHypercubicEvenBoundaryPositiveWilsonActionContinuousMap_mem_actualPlaquetteAlgebra
        H N hN b)
      (periodicHypercubicEvenBoundaryPositiveBoundaryTemporalWilsonActionContinuousMap_mem_actualPlaquetteAlgebra
        H N hN b)

end

end MathlibAnalytic
end MGAP4D