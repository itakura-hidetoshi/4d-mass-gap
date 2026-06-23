import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianGraphLimitUnique
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Topology.Sequences

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- In a real Hilbert space, the sequential zero-fibre criterion implies
Mathlib's graph-theoretic `LinearPMap.IsClosable` predicate.

The closure of the graph is a linear subspace.  It is the graph of a partial
linear map precisely when its fibre over zero is trivial.  Since a Hilbert
space is Fréchet–Urysohn, every point of the graph closure is represented by a
convergent sequence from the original graph, so sequential closability proves
that the zero fibre is trivial. -/
private theorem linearPMap_isClosable_of_sequentially_closable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H →ₗ.[ℝ] H)
    (hseq :
      ∀ {psi : ℕ → f.domain} {eta : H},
        Tendsto (fun n => ((psi n : f.domain) : H)) atTop (nhds 0) →
        Tendsto (fun n => f (psi n)) atTop (nhds eta) →
        eta = 0) :
    LinearPMap.IsClosable f := by
  refine ⟨f.graph.topologicalClosure.toLinearPMap, ?_⟩
  symm
  apply Submodule.toLinearPMap_graph_eq
  intro p hp hpzero
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    mem_closure_iff_seq_limit] at hp
  rcases hp with ⟨u, huGraph, hu⟩
  choose psi hpsiBase hpsiValue using fun n =>
    (LinearPMap.mem_graph_iff f).1 (huGraph n)
  have huFst :
      Tendsto (fun n => (u n).1) atTop (nhds p.1) := by
    simpa only [Function.comp_apply] using
      continuous_fst.continuousAt.comp hu
  have hbaseEq :
      (fun n => (u n).1) = fun n => ((psi n : f.domain) : H) :=
    funext fun n => (hpsiBase n).symm
  rw [hbaseEq, hpzero] at huFst
  have huSnd :
      Tendsto (fun n => (u n).2) atTop (nhds p.2) := by
    simpa only [Function.comp_apply] using
      continuous_snd.continuousAt.comp hu
  have hvalueEq :
      (fun n => (u n).2) = fun n => f (psi n) :=
    funext fun n => (hpsiValue n).symm
  rw [hvalueEq] at huSnd
  exact hseq huFst huSnd

/-- The canonical right infinitesimal generator as Mathlib's partially defined
linear operator on the completed physical Hilbert space. -/
def rightGeneratorLinearPMap
    (T : P.StronglyContinuousPhysicalSemigroup) :
    P.PhysicalHilbert →ₗ.[ℝ] P.PhysicalHilbert where
  domain := T.rightGeneratorDomain
  toFun := T.rightGenerator

@[simp] theorem rightGeneratorLinearPMap_domain
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.rightGeneratorLinearPMap.domain = T.rightGeneratorDomain :=
  rfl

@[simp] theorem rightGeneratorLinearPMap_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.rightGeneratorLinearPMap.domain) :
    T.rightGeneratorLinearPMap psi = T.rightGenerator psi :=
  rfl

/-- The right Hamiltonian as Mathlib's partially defined linear operator. -/
def rightHamiltonianLinearPMap
    (T : P.StronglyContinuousPhysicalSemigroup) :
    P.PhysicalHilbert →ₗ.[ℝ] P.PhysicalHilbert where
  domain := T.rightGeneratorDomain
  toFun := T.rightHamiltonian

@[simp] theorem rightHamiltonianLinearPMap_domain
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.rightHamiltonianLinearPMap.domain = T.rightGeneratorDomain :=
  rfl

@[simp] theorem rightHamiltonianLinearPMap_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.rightHamiltonianLinearPMap.domain) :
    T.rightHamiltonianLinearPMap psi = T.rightHamiltonian psi :=
  rfl

/-- The canonical right generator is closable in Mathlib's `LinearPMap` sense. -/
theorem rightGeneratorLinearPMap_isClosable
    (T : P.StronglyContinuousPhysicalSemigroup) :
    LinearPMap.IsClosable T.rightGeneratorLinearPMap := by
  apply linearPMap_isClosable_of_sequentially_closable
  intro psi eta hpsi hvalue
  exact T.rightGenerator_sequentially_closable hpsi hvalue

/-- The canonical right Hamiltonian is closable in Mathlib's `LinearPMap` sense. -/
theorem rightHamiltonianLinearPMap_isClosable
    (T : P.StronglyContinuousPhysicalSemigroup) :
    LinearPMap.IsClosable T.rightHamiltonianLinearPMap := by
  apply linearPMap_isClosable_of_sequentially_closable
  intro psi eta hpsi hvalue
  exact T.rightHamiltonian_sequentially_closable hpsi hvalue

/-- The closed right generator obtained from Mathlib's canonical graph closure. -/
def closedRightGenerator
    (T : P.StronglyContinuousPhysicalSemigroup) :
    P.PhysicalHilbert →ₗ.[ℝ] P.PhysicalHilbert :=
  T.rightGeneratorLinearPMap.closure

/-- The closed right Hamiltonian obtained from Mathlib's canonical graph closure. -/
def closedRightHamiltonian
    (T : P.StronglyContinuousPhysicalSemigroup) :
    P.PhysicalHilbert →ₗ.[ℝ] P.PhysicalHilbert :=
  T.rightHamiltonianLinearPMap.closure

/-- The original right generator is contained in its closed graph extension. -/
theorem rightGeneratorLinearPMap_le_closedRightGenerator
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.rightGeneratorLinearPMap ≤ T.closedRightGenerator := by
  simpa [closedRightGenerator] using T.rightGeneratorLinearPMap.le_closure

/-- The original right Hamiltonian is contained in its closed graph extension. -/
theorem rightHamiltonianLinearPMap_le_closedRightHamiltonian
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.rightHamiltonianLinearPMap ≤ T.closedRightHamiltonian := by
  simpa [closedRightHamiltonian] using T.rightHamiltonianLinearPMap.le_closure

/-- The graph-closure right generator is a closed partially defined operator. -/
theorem closedRightGenerator_isClosed
    (T : P.StronglyContinuousPhysicalSemigroup) :
    LinearPMap.IsClosed T.closedRightGenerator := by
  simpa [closedRightGenerator] using
    T.rightGeneratorLinearPMap_isClosable.closure_isClosed

/-- The graph-closure right Hamiltonian is a closed partially defined operator. -/
theorem closedRightHamiltonian_isClosed
    (T : P.StronglyContinuousPhysicalSemigroup) :
    LinearPMap.IsClosed T.closedRightHamiltonian := by
  simpa [closedRightHamiltonian] using
    T.rightHamiltonianLinearPMap_isClosable.closure_isClosed

/-- The closed right generator remains densely defined because it extends the
canonical dense generator domain. -/
theorem closedRightGenerator_dense_domain
    (T : P.StronglyContinuousPhysicalSemigroup) :
    Dense ((T.closedRightGenerator.domain : Set P.PhysicalHilbert)) := by
  refine T.rightGeneratorDomain_dense.mono ?_
  intro psi hpsi
  exact T.rightGeneratorLinearPMap_le_closedRightGenerator.1 hpsi

/-- The closed right Hamiltonian remains densely defined because it extends the
same canonical dense domain. -/
theorem closedRightHamiltonian_dense_domain
    (T : P.StronglyContinuousPhysicalSemigroup) :
    Dense ((T.closedRightHamiltonian.domain : Set P.PhysicalHilbert)) := by
  refine T.rightHamiltonianDomain_dense.mono ?_
  intro psi hpsi
  exact T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.1 hpsi

/-- Mathlib identifies the graph of the closed right generator with the
closure of the canonical generator graph. -/
theorem closedRightGenerator_graph_eq
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.rightGeneratorLinearPMap.graph.topologicalClosure =
      T.closedRightGenerator.graph := by
  simpa [closedRightGenerator] using
    T.rightGeneratorLinearPMap_isClosable.graph_closure_eq_closure_graph

/-- Mathlib identifies the graph of the closed right Hamiltonian with the
closure of the canonical Hamiltonian graph. -/
theorem closedRightHamiltonian_graph_eq
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.rightHamiltonianLinearPMap.graph.topologicalClosure =
      T.closedRightHamiltonian.graph := by
  simpa [closedRightHamiltonian] using
    T.rightHamiltonianLinearPMap_isClosable.graph_closure_eq_closure_graph

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
