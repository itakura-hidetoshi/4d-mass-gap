import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularHamiltonian
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-!
# Canonical graph closure of the same-root regular OS Hamiltonian

The densely defined symmetric nonnegative Hamiltonian constructed from the factorial OS C₀
semigroup is now packaged as Mathlib's `LinearPMap` and closed by its canonical graph closure.
The closed operator remains densely defined, formally symmetric and nonnegative.  Every positive
shift satisfies the Hille--Yosida lower bound, is injective, and has closed range.

Surjectivity and self-adjointness are deliberately deferred to the finite-Laplace resolvent layer.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

private theorem linearPMap_isClosable_of_sequentially_closable
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (f : K →ₗ.[ℝ] K)
    (hseq :
      ∀ {psi : ℕ → f.domain} {eta : K},
        Tendsto (fun n => ((psi n : f.domain) : K)) atTop (nhds 0) →
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
  have huFst : Tendsto (fun n => (u n).1) atTop (nhds p.1) := by
    simpa only [Function.comp_apply] using
      (continuous_fst.tendsto p).comp hu
  have hbaseEq :
      (fun n => (u n).1) = fun n => ((psi n : f.domain) : K) :=
    funext fun n => (hpsiBase n).symm
  rw [hbaseEq, hpzero] at huFst
  have huSnd : Tendsto (fun n => (u n).2) atTop (nhds p.2) := by
    simpa only [Function.comp_apply] using
      (continuous_snd.tendsto p).comp hu
  have hvalueEq : (fun n => (u n).2) = fun n => f (psi n) :=
    funext fun n => (hpsiValue n).symm
  rw [hvalueEq] at huSnd
  exact hseq huFst huSnd

noncomputable def fixedSlotHilbertDirectLimitRegularRightGeneratorLinearPMap
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularSubspace →ₗ.[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace where
  domain := P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain
  toFun := P.fixedSlotHilbertDirectLimitRegularRightGenerator

noncomputable def fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularSubspace →ₗ.[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace where
  domain := P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain
  toFun := P.fixedSlotHilbertDirectLimitRegularRightHamiltonian

@[simp] theorem fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap.domain) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap x =
      P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x := rfl

@[simp] theorem fixedSlotHilbertDirectLimitRegularRightGeneratorLinearPMap_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorLinearPMap.domain) :
    P.fixedSlotHilbertDirectLimitRegularRightGeneratorLinearPMap x =
      P.fixedSlotHilbertDirectLimitRegularRightGenerator x := rfl

theorem fixedSlotHilbertDirectLimitRegularRightGeneratorLinearPMap_isClosable
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    LinearPMap.IsClosable P.fixedSlotHilbertDirectLimitRegularRightGeneratorLinearPMap := by
  apply linearPMap_isClosable_of_sequentially_closable
  intro psi eta hpsi hvalue
  exact P.fixedSlotHilbertDirectLimitRegularRightGenerator_sequentially_closable hpsi hvalue

theorem fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_isClosable
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    LinearPMap.IsClosable P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap := by
  apply linearPMap_isClosable_of_sequentially_closable
  intro psi eta hpsi hvalue
  exact P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_sequentially_closable hpsi hvalue

noncomputable def fixedSlotHilbertDirectLimitRegularClosedRightGenerator
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularSubspace →ₗ.[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace :=
  P.fixedSlotHilbertDirectLimitRegularRightGeneratorLinearPMap.closure

noncomputable def fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularSubspace →ₗ.[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace :=
  P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap.closure

theorem fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_le_closed
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap ≤
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian := by
  simpa [fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian] using
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap.le_closure

theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isClosed
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    LinearPMap.IsClosed P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian := by
  simpa [fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian] using
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_isClosable.closure_isClosed

theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_dense_domain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    Dense ((P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain :
      Set P.fixedSlotHilbertDirectLimitRegularSubspace)) := by
  refine P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_dense.mono ?_
  intro x hx
  exact P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_le_closed.1 hx

theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_graph_eq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap.graph.topologicalClosure =
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.graph := by
  simpa [fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian] using
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_isClosable.graph_closure_eq_closure_graph

theorem fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_isFormalAdjoint
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap.IsFormalAdjoint
      P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap := by
  intro x y
  exact P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_inner_symmetric x y

private theorem linearPMap_closure_isFormalAdjoint_of_isFormalAdjoint
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (A : K →ₗ.[ℝ] K)
    (hClosable : LinearPMap.IsClosable A)
    (hSymmetric : A.IsFormalAdjoint A) :
    A.closure.IsFormalAdjoint A.closure := by
  intro x y
  have hxGraph : ((x : K), A.closure x) ∈ A.graph.topologicalClosure := by
    rw [hClosable.graph_closure_eq_closure_graph]
    exact A.closure.mem_graph x
  have hyGraph : ((y : K), A.closure y) ∈ A.graph.topologicalClosure := by
    rw [hClosable.graph_closure_eq_closure_graph]
    exact A.closure.mem_graph y
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    mem_closure_iff_seq_limit] at hxGraph hyGraph
  rcases hxGraph with ⟨u, huGraph, hu⟩
  rcases hyGraph with ⟨v, hvGraph, hv⟩
  choose xu hxuBase hxuValue using fun n =>
    (LinearPMap.mem_graph_iff A).1 (huGraph n)
  choose yv hyvBase hyvValue using fun n =>
    (LinearPMap.mem_graph_iff A).1 (hvGraph n)
  have huFst : Tendsto (fun n => (u n).1) atTop (nhds (x : K)) := by
    simpa only [Function.comp_apply] using
      (continuous_fst.tendsto ((x : K), A.closure x)).comp hu
  have huSnd : Tendsto (fun n => (u n).2) atTop (nhds (A.closure x)) := by
    simpa only [Function.comp_apply] using
      (continuous_snd.tendsto ((x : K), A.closure x)).comp hu
  have hvFst : Tendsto (fun n => (v n).1) atTop (nhds (y : K)) := by
    simpa only [Function.comp_apply] using
      (continuous_fst.tendsto ((y : K), A.closure y)).comp hv
  have hvSnd : Tendsto (fun n => (v n).2) atTop (nhds (A.closure y)) := by
    simpa only [Function.comp_apply] using
      (continuous_snd.tendsto ((y : K), A.closure y)).comp hv
  have hxuBaseFunction : (fun n => (u n).1) = fun n => ((xu n : A.domain) : K) :=
    funext fun n => (hxuBase n).symm
  have hxuValueFunction : (fun n => (u n).2) = fun n => A (xu n) :=
    funext fun n => (hxuValue n).symm
  have hyvBaseFunction : (fun n => (v n).1) = fun n => ((yv n : A.domain) : K) :=
    funext fun n => (hyvBase n).symm
  have hyvValueFunction : (fun n => (v n).2) = fun n => A (yv n) :=
    funext fun n => (hyvValue n).symm
  rw [hxuBaseFunction] at huFst
  rw [hxuValueFunction] at huSnd
  rw [hyvBaseFunction] at hvFst
  rw [hyvValueFunction] at hvSnd
  have hleft := huSnd.inner hvFst
  have hright := huFst.inner hvSnd
  have hfunctions :
      (fun n => inner ℝ (A (xu n)) ((yv n : A.domain) : K)) =
        fun n => inner ℝ ((xu n : A.domain) : K) (A (yv n)) := by
    funext n
    exact hSymmetric (xu n) (yv n)
  rw [hfunctions] at hleft
  exact tendsto_nhds_unique hleft hright

theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isFormalAdjoint
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.IsFormalAdjoint
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian := by
  simpa [fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian] using
    linearPMap_closure_isFormalAdjoint_of_isFormalAdjoint
      P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap
      P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_isClosable
      P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_isFormalAdjoint

theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_inner_nonneg
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    0 ≤ inner ℝ (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x)
      (x : P.fixedSlotHilbertDirectLimitRegularSubspace) := by
  have hgraph :
      ((x : P.fixedSlotHilbertDirectLimitRegularSubspace),
        P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x) ∈
        P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap.graph.topologicalClosure := by
    rw [P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_graph_eq]
    exact P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.mem_graph x
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    mem_closure_iff_seq_limit] at hgraph
  rcases hgraph with ⟨u, huGraph, hu⟩
  have huFst : Tendsto (fun n => (u n).1) atTop
      (nhds (x : P.fixedSlotHilbertDirectLimitRegularSubspace)) := by
    simpa only [Function.comp_apply] using
      (continuous_fst.tendsto
        ((x : P.fixedSlotHilbertDirectLimitRegularSubspace),
          P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x)).comp hu
  have huSnd : Tendsto (fun n => (u n).2) atTop
      (nhds (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x)) := by
    simpa only [Function.comp_apply] using
      (continuous_snd.tendsto
        ((x : P.fixedSlotHilbertDirectLimitRegularSubspace),
          P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x)).comp hu
  have hinner := huSnd.inner huFst
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hinner
  exact Filter.Eventually.of_forall fun n => by
    rcases (LinearPMap.mem_graph_iff
      P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap).1
        (huGraph n) with ⟨z, hzBase, hzValue⟩
    change 0 ≤ inner ℝ (u n).2 (u n).1
    rw [← hzBase, ← hzValue]
    exact P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_inner_nonneg z

noncomputable def fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain →ₗ[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace :=
  lambda • P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain.subtype +
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.toFun

@[simp] theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda x =
      lambda • (x : P.fixedSlotHilbertDirectLimitRegularSubspace) +
        P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x := rfl

theorem fixedSlotHilbertDirectLimitRegular_lambda_mul_norm_le_closedShift
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    lambda * ‖(x : P.fixedSlotHilbertDirectLimitRegularSubspace)‖ ≤
      ‖P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda x‖ := by
  have hquad :
      lambda * ‖(x : P.fixedSlotHilbertDirectLimitRegularSubspace)‖ ^ 2 ≤
        inner ℝ (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda x)
          (x : P.fixedSlotHilbertDirectLimitRegularSubspace) := by
    rw [P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_apply,
      inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith [hlambda.le, P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_inner_nonneg x]
  have hcs := real_inner_le_norm
    (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda x)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
  have hmul := hquad.trans hcs
  by_cases hzero : ‖(x : P.fixedSlotHilbertDirectLimitRegularSubspace)‖ = 0
  · simp [hzero]
  · have hpos : 0 < ‖(x : P.fixedSlotHilbertDirectLimitRegularSubspace)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith

theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_injective
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Injective (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda) := by
  intro x y hxy
  have hzero :
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hbound := P.fixedSlotHilbertDirectLimitRegular_lambda_mul_norm_le_closedShift
    hlambda (x - y)
  rw [hzero, norm_zero] at hbound
  have hnorm :
      ‖((x - y : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
        P.fixedSlotHilbertDirectLimitRegularSubspace)‖ = 0 := by
    have hnonneg := norm_nonneg
      ((x - y : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
        P.fixedSlotHilbertDirectLimitRegularSubspace)
    nlinarith
  apply sub_eq_zero.mp
  apply Subtype.ext
  exact norm_eq_zero.mp hnorm

theorem fixedSlotHilbertDirectLimitRegular_lambda_mul_dist_le_closedShift_dist
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (x y : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    lambda * dist (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
        (y : P.fixedSlotHilbertDirectLimitRegularSubspace) ≤
      dist (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda x)
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda y) := by
  rw [dist_eq_norm, dist_eq_norm]
  calc
    lambda * ‖(x : P.fixedSlotHilbertDirectLimitRegularSubspace) - y‖ =
      lambda * ‖((x - y : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
        P.fixedSlotHilbertDirectLimitRegularSubspace)‖ := by simp
    _ ≤ ‖P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda (x - y)‖ :=
      P.fixedSlotHilbertDirectLimitRegular_lambda_mul_norm_le_closedShift hlambda (x - y)
    _ = ‖P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda x -
        P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda y‖ := by
      rw [map_sub]

theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_range_isClosed
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    IsClosed (Set.range (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro yseq y hyseq hy
  choose psi hpsi using hyseq
  have hyCauchy : CauchySeq yseq := hy.cauchySeq
  have hpsiCauchy : CauchySeq (fun n =>
      (psi n : P.fixedSlotHilbertDirectLimitRegularSubspace)) := by
    rw [Metric.cauchySeq_iff] at hyCauchy ⊢
    intro epsilon hepsilon
    rcases hyCauchy (lambda * epsilon) (mul_pos hlambda hepsilon) with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro m hm n hn
    have hlower := P.fixedSlotHilbertDirectLimitRegular_lambda_mul_dist_le_closedShift_dist
      hlambda (psi m) (psi n)
    rw [hpsi m, hpsi n] at hlower
    have hupper := hM m hm n hn
    nlinarith
  rcases cauchySeq_tendsto_of_complete hpsiCauchy with ⟨x, hx⟩
  have hscaled : Tendsto
      (fun n => lambda • (psi n : P.fixedSlotHilbertDirectLimitRegularSubspace)) atTop
      (nhds (lambda • x)) := tendsto_const_nhds.smul hx
  have hHamiltonianEq :
      (fun n => P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian (psi n)) =
        fun n => yseq n - lambda •
          (psi n : P.fixedSlotHilbertDirectLimitRegularSubspace) := by
    funext n
    rw [← hpsi n, P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_apply]
    module
  have hHamiltonian : Tendsto
      (fun n => P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian (psi n)) atTop
      (nhds (y - lambda • x)) := by
    rw [hHamiltonianEq]
    exact hy.sub hscaled
  have hpair : Tendsto
      (fun n => ((psi n : P.fixedSlotHilbertDirectLimitRegularSubspace),
        P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian (psi n))) atTop
      (nhds (x, y - lambda • x)) := by
    rw [nhds_prod_eq]
    exact hx.prodMk hHamiltonian
  have hlimitGraph :
      (x, y - lambda • x) ∈
        P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.graph :=
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isClosed.mem_of_tendsto hpair
      (Filter.Eventually.of_forall fun n =>
        P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.mem_graph (psi n))
  rcases (LinearPMap.mem_graph_iff
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian).1 hlimitGraph with
    ⟨z, hzBase, hzValue⟩
  refine ⟨z, ?_⟩
  rw [P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_apply, hzBase, hzValue]
  module

theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_surjective_iff_denseRange
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Surjective (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda) ↔
      Dense (Set.range (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda)) := by
  constructor
  · intro hsurj
    rw [dense_iff_closure_eq]
    have hrange : Set.range
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda) = Set.univ := by
      ext y
      constructor
      · intro _; exact Set.mem_univ y
      · intro _
        rcases hsurj y with ⟨x, hx⟩
        exact ⟨x, hx⟩
    rw [hrange, closure_univ]
  · intro hdense y
    have hclosed := P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_range_isClosed hlambda
    have hclosure : closure (Set.range
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda)) = Set.univ :=
      dense_iff_closure_eq.mp hdense
    have hrange : Set.range
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda) = Set.univ := by
      rw [← hclosed.closure_eq, hclosure]
    have hy : y ∈ Set.range
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda) := by
      rw [hrange]
      exact Set.mem_univ y
    exact hy

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
