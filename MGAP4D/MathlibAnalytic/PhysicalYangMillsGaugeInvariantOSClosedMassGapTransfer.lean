import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFiniteVolumeMassGapTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedRightHamiltonianNonnegative
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

/-- A vacuum-sector Rayleigh lower bound on the canonical right Hamiltonian passes
through Mathlib's graph closure.

The only extra input is normalization of the OS state.  It makes the vacuum a
unit vector, so every graph-approximating core vector can be orthogonalized by
subtracting its vacuum coefficient.  The right Hamiltonian annihilates the
vacuum, hence this correction changes the approximating vector but not its
Hamiltonian value.  Both corrected graph components then converge, and the
finite-volume lower bound passes to the closed operator. -/
theorem VacuumSemigroupGapSlope.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  have hgraph :
      ((psi : P.PhysicalHilbert), T.closedRightHamiltonian psi) ∈
        T.rightHamiltonianLinearPMap.graph.topologicalClosure := by
    rw [T.closedRightHamiltonian_graph_eq]
    exact T.closedRightHamiltonian.mem_graph psi
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    mem_closure_iff_seq_limit] at hgraph
  rcases hgraph with ⟨u, huGraph, hu⟩
  choose z hzBase hzValue using fun n =>
    (LinearPMap.mem_graph_iff T.rightHamiltonianLinearPMap).1 (huGraph n)
  have huFst :
      Tendsto (fun n => (u n).1) atTop
        (nhds (psi : P.PhysicalHilbert)) := by
    simpa only [Function.comp_apply] using
      (continuous_fst.tendsto
        ((psi : P.PhysicalHilbert), T.closedRightHamiltonian psi)).comp hu
  have hbaseEq :
      (fun n => (u n).1) =
        fun n => ((z n : T.rightHamiltonianLinearPMap.domain) :
          P.PhysicalHilbert) :=
    funext fun n => (hzBase n).symm
  rw [hbaseEq] at huFst
  have huSnd :
      Tendsto (fun n => (u n).2) atTop
        (nhds (T.closedRightHamiltonian psi)) := by
    simpa only [Function.comp_apply] using
      (continuous_snd.tendsto
        ((psi : P.PhysicalHilbert), T.closedRightHamiltonian psi)).comp hu
  have hvalueEq :
      (fun n => (u n).2) =
        fun n => T.rightHamiltonianLinearPMap (z n) := by
    funext n
    exact (hzValue n).symm
  rw [hvalueEq] at huSnd

  let zCore : ℕ → T.rightGeneratorDomain := fun n =>
    (show T.rightGeneratorDomain from z n)
  have hzCoreFst :
      Tendsto (fun n => ((zCore n : T.rightGeneratorDomain) :
        P.PhysicalHilbert)) atTop
        (nhds (psi : P.PhysicalHilbert)) := by
    simpa only [zCore] using huFst
  have hzCoreSnd :
      Tendsto (fun n => T.rightHamiltonian (zCore n)) atTop
        (nhds (T.closedRightHamiltonian psi)) := by
    simpa only [zCore, T.rightHamiltonianLinearPMap_apply] using huSnd

  let vacuumDomain : T.rightGeneratorDomain :=
    ⟨P.vacuum, T.vacuum_mem_rightHamiltonianDomain⟩
  let coefficient : ℕ → ℝ := fun n =>
    inner ℝ ((zCore n : T.rightGeneratorDomain) : P.PhysicalHilbert) P.vacuum
  let zOrth : ℕ → T.rightGeneratorDomain := fun n =>
    zCore n - coefficient n • vacuumDomain

  have hvacuumInner : inner ℝ P.vacuum P.vacuum = 1 := by
    rw [real_inner_self_eq_norm_sq, P.norm_vacuum hP]
    norm_num
  have hzOrthogonal (n : ℕ) :
      inner ℝ ((zOrth n : T.rightGeneratorDomain) : P.PhysicalHilbert)
        P.vacuum = 0 := by
    change inner ℝ
        (((zCore n : T.rightGeneratorDomain) : P.PhysicalHilbert) -
          coefficient n • P.vacuum)
        P.vacuum = 0
    rw [inner_sub_left, real_inner_smul_left, hvacuumInner, mul_one]
    rfl
  have hCoefficient : Tendsto coefficient atTop (nhds 0) := by
    have hinner := hzCoreFst.inner tendsto_const_nhds
    simpa only [coefficient, hpsi] using hinner
  have hzOrthFst :
      Tendsto (fun n => ((zOrth n : T.rightGeneratorDomain) :
        P.PhysicalHilbert)) atTop
        (nhds (psi : P.PhysicalHilbert)) := by
    change Tendsto
      (fun n =>
        ((zCore n : T.rightGeneratorDomain) : P.PhysicalHilbert) -
          coefficient n • P.vacuum)
      atTop (nhds (psi : P.PhysicalHilbert))
    simpa using hzCoreFst.sub (hCoefficient.smul_const P.vacuum)
  have hzOrthValue (n : ℕ) :
      T.rightHamiltonian (zOrth n) = T.rightHamiltonian (zCore n) := by
    simp [zOrth, vacuumDomain, T.rightHamiltonian_vacuum]
  have hzOrthSnd :
      Tendsto (fun n => T.rightHamiltonian (zOrth n)) atTop
        (nhds (T.closedRightHamiltonian psi)) := by
    rw [show (fun n => T.rightHamiltonian (zOrth n)) =
        (fun n => T.rightHamiltonian (zCore n)) by
      funext n
      exact hzOrthValue n]
    exact hzCoreSnd

  have hLeft :
      Tendsto
        (fun n => G.mass *
          ‖((zOrth n : T.rightGeneratorDomain) : P.PhysicalHilbert)‖ ^ 2)
        atTop
        (nhds (G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2)) :=
    tendsto_const_nhds.mul ((hzOrthFst.norm).pow 2)
  have hRight :
      Tendsto
        (fun n => inner ℝ (T.rightHamiltonian (zOrth n))
          ((zOrth n : T.rightGeneratorDomain) : P.PhysicalHilbert))
        atTop
        (nhds
          (inner ℝ (T.closedRightHamiltonian psi)
            (psi : P.PhysicalHilbert))) :=
    hzOrthSnd.inner hzOrthFst
  apply le_of_tendsto_of_tendsto hLeft hRight
  exact Filter.Eventually.of_forall fun n =>
    VacuumSemigroupGapSlope.rightHamiltonian_inner_ge_mass_mul_norm_sq
      T G (zOrth n) (hzOrthogonal n)

/-- The finite-volume transfer package therefore gives the same positive
Rayleigh lower bound on the full domain of the closed OS Hamiltonian. -/
theorem FiniteVolumeVacuumGapTransfer.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) :=
  VacuumSemigroupGapSlope.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    T G.toVacuumSemigroupGapSlope hP psi hpsi

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D