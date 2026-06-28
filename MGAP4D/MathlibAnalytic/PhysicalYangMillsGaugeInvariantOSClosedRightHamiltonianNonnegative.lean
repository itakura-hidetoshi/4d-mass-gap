import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianLinearPMapClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Dissipativity passes from the canonical right generator to its Mathlib graph
closure. -/
theorem closedRightGenerator_inner_nonpos
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.closedRightGenerator.domain) :
    ⟪T.closedRightGenerator psi, (psi : P.PhysicalHilbert)⟫_ℝ ≤ 0 := by
  have hgraph :
      ((psi : P.PhysicalHilbert), T.closedRightGenerator psi) ∈
        T.rightGeneratorLinearPMap.graph.topologicalClosure := by
    rw [T.closedRightGenerator_graph_eq]
    exact T.closedRightGenerator.mem_graph psi
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    mem_closure_iff_seq_limit] at hgraph
  rcases hgraph with ⟨u, huGraph, hu⟩
  have huFst :
      Tendsto (fun n => (u n).1) atTop
        (nhds (psi : P.PhysicalHilbert)) := by
    simpa only [Function.comp_apply] using
      (continuous_fst.tendsto
        ((psi : P.PhysicalHilbert), T.closedRightGenerator psi)).comp hu
  have huSnd :
      Tendsto (fun n => (u n).2) atTop
        (nhds (T.closedRightGenerator psi)) := by
    simpa only [Function.comp_apply] using
      (continuous_snd.tendsto
        ((psi : P.PhysicalHilbert), T.closedRightGenerator psi)).comp hu
  have hinner :
      Tendsto (fun n => ⟪(u n).2, (u n).1⟫_ℝ) atTop
        (nhds
          ⟪T.closedRightGenerator psi,
            (psi : P.PhysicalHilbert)⟫_ℝ) :=
    huSnd.inner huFst
  apply le_of_tendsto_of_tendsto hinner tendsto_const_nhds
  exact Filter.Eventually.of_forall fun n => by
    change ⟪(u n).2, (u n).1⟫_ℝ ≤ 0
    rcases (LinearPMap.mem_graph_iff T.rightGeneratorLinearPMap).1
      (huGraph n) with ⟨z, hzBase, hzValue⟩
    rw [← hzBase, ← hzValue]
    exact T.rightGenerator_inner_nonpos z

/-- Nonnegativity passes from the canonical right Hamiltonian to its Mathlib
graph closure. -/
theorem closedRightHamiltonian_inner_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.closedRightHamiltonian.domain) :
    0 ≤ ⟪T.closedRightHamiltonian psi, (psi : P.PhysicalHilbert)⟫_ℝ := by
  have hgraph :
      ((psi : P.PhysicalHilbert), T.closedRightHamiltonian psi) ∈
        T.rightHamiltonianLinearPMap.graph.topologicalClosure := by
    rw [T.closedRightHamiltonian_graph_eq]
    exact T.closedRightHamiltonian.mem_graph psi
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    mem_closure_iff_seq_limit] at hgraph
  rcases hgraph with ⟨u, huGraph, hu⟩
  have huFst :
      Tendsto (fun n => (u n).1) atTop
        (nhds (psi : P.PhysicalHilbert)) := by
    simpa only [Function.comp_apply] using
      (continuous_fst.tendsto
        ((psi : P.PhysicalHilbert), T.closedRightHamiltonian psi)).comp hu
  have huSnd :
      Tendsto (fun n => (u n).2) atTop
        (nhds (T.closedRightHamiltonian psi)) := by
    simpa only [Function.comp_apply] using
      (continuous_snd.tendsto
        ((psi : P.PhysicalHilbert), T.closedRightHamiltonian psi)).comp hu
  have hinner :
      Tendsto (fun n => ⟪(u n).2, (u n).1⟫_ℝ) atTop
        (nhds
          ⟪T.closedRightHamiltonian psi,
            (psi : P.PhysicalHilbert)⟫_ℝ) :=
    huSnd.inner huFst
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hinner
  exact Filter.Eventually.of_forall fun n => by
    change 0 ≤ ⟪(u n).2, (u n).1⟫_ℝ
    rcases (LinearPMap.mem_graph_iff T.rightHamiltonianLinearPMap).1
      (huGraph n) with ⟨z, hzBase, hzValue⟩
    rw [← hzBase, ← hzValue]
    exact T.rightHamiltonian_inner_nonneg z

/-- The positive shift `lambda I + H̄` of the closed right Hamiltonian. -/
noncomputable def closedRightHamiltonianShift
    (T : P.StronglyContinuousPhysicalSemigroup) (lambda : ℝ) :
    T.closedRightHamiltonian.domain →ₗ[ℝ] P.PhysicalHilbert :=
  lambda • T.closedRightHamiltonian.domain.subtype +
    T.closedRightHamiltonian.toFun

@[simp] theorem closedRightHamiltonianShift_apply
    (T : P.StronglyContinuousPhysicalSemigroup) (lambda : ℝ)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonianShift lambda psi =
      lambda • (psi : P.PhysicalHilbert) +
        T.closedRightHamiltonian psi := by
  rfl

/-- Every positive shift of the closed right Hamiltonian satisfies the same
Hille--Yosida lower bound as the canonical-domain operator. -/
theorem lambda_mul_norm_le_norm_closedRightHamiltonianShift
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (psi : T.closedRightHamiltonian.domain) :
    lambda * ‖(psi : P.PhysicalHilbert)‖ ≤
      ‖T.closedRightHamiltonianShift lambda psi‖ := by
  have hquad :
      lambda * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
        ⟪T.closedRightHamiltonianShift lambda psi,
          (psi : P.PhysicalHilbert)⟫_ℝ := by
    rw [T.closedRightHamiltonianShift_apply, inner_add_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith [hlambda.le, T.closedRightHamiltonian_inner_nonneg psi]
  have hcs :
      ⟪T.closedRightHamiltonianShift lambda psi,
          (psi : P.PhysicalHilbert)⟫_ℝ ≤
        ‖T.closedRightHamiltonianShift lambda psi‖ *
          ‖(psi : P.PhysicalHilbert)‖ :=
    real_inner_le_norm _ _
  have hmul :
      lambda * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
        ‖T.closedRightHamiltonianShift lambda psi‖ *
          ‖(psi : P.PhysicalHilbert)‖ :=
    hquad.trans hcs
  by_cases hzero : ‖(psi : P.PhysicalHilbert)‖ = 0
  · simp [hzero]
  · have hpos : 0 < ‖(psi : P.PhysicalHilbert)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith [hmul]

/-- Every positive shift of the closed right Hamiltonian is injective. -/
theorem closedRightHamiltonianShift_injective
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Injective (T.closedRightHamiltonianShift lambda) := by
  intro psi phi hpsiPhi
  have hzero :
      T.closedRightHamiltonianShift lambda (psi - phi) = 0 := by
    rw [map_sub, hpsiPhi, sub_self]
  have hbound :=
    T.lambda_mul_norm_le_norm_closedRightHamiltonianShift
      hlambda (psi - phi)
  rw [hzero, norm_zero] at hbound
  have hnorm :
      ‖((psi - phi : T.closedRightHamiltonian.domain) :
        P.PhysicalHilbert)‖ = 0 := by
    have hnonneg :
        0 ≤ ‖((psi - phi : T.closedRightHamiltonian.domain) :
          P.PhysicalHilbert)‖ := norm_nonneg _
    nlinarith
  apply sub_eq_zero.mp
  apply Subtype.ext
  exact norm_eq_zero.mp hnorm

/-- The closed right Hamiltonian package now consists of a closed, densely
defined, nonnegative operator whose every positive shift is bounded below and
injective.  Surjectivity, symmetry, and self-adjointness remain separate
frontiers. -/
theorem closedRightHamiltonian_analytic_package
    (T : P.StronglyContinuousPhysicalSemigroup) :
    LinearPMap.IsClosed T.closedRightHamiltonian ∧
      Dense ((T.closedRightHamiltonian.domain : Set P.PhysicalHilbert)) ∧
      (∀ psi : T.closedRightHamiltonian.domain,
        0 ≤ ⟪T.closedRightHamiltonian psi,
          (psi : P.PhysicalHilbert)⟫_ℝ) ∧
      (∀ lambda : ℝ, 0 < lambda →
        Function.Injective (T.closedRightHamiltonianShift lambda)) :=
  ⟨T.closedRightHamiltonian_isClosed,
    T.closedRightHamiltonian_dense_domain,
    T.closedRightHamiltonian_inner_nonneg,
    fun _ hlambda => T.closedRightHamiltonianShift_injective hlambda⟩

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
