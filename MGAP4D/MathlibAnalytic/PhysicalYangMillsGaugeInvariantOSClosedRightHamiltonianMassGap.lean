import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFiniteVolumeMassGapTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedRightHamiltonianNonnegative
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- A finite-volume vacuum-sector gap transfers from the canonical generator
core to the full graph-closed Osterwalder--Schrader Hamiltonian domain.

The only additional input is normalization of the continuum vacuum.  Given a
graph-approximating sequence from the canonical Hamiltonian domain, subtract its
vacuum component at every stage.  Since the right Hamiltonian annihilates the
vacuum, this correction does not change the Hamiltonian values.  The corrected
sequence is exactly vacuum-orthogonal and converges to the original closed-domain
vector.  The core Rayleigh lower bound therefore passes to the graph closure. -/
theorem FiniteVolumeVacuumGapTransfer.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
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
  have huSnd :
      Tendsto (fun n => (u n).2) atTop
        (nhds (T.closedRightHamiltonian psi)) := by
    simpa only [Function.comp_apply] using
      (continuous_snd.tendsto
        ((psi : P.PhysicalHilbert), T.closedRightHamiltonian psi)).comp hu
  have hzBaseTendsto :
      Tendsto
        (fun n => ((z n : T.rightHamiltonianLinearPMap.domain) :
          P.PhysicalHilbert))
        atTop (nhds (psi : P.PhysicalHilbert)) := by
    have hfun :
        (fun n => (u n).1) =
          fun n => ((z n : T.rightHamiltonianLinearPMap.domain) :
            P.PhysicalHilbert) :=
      funext fun n => (hzBase n).symm
    rw [hfun] at huFst
    exact huFst
  have hzValueTendsto :
      Tendsto
        (fun n => T.rightHamiltonianLinearPMap z n)
        atTop (nhds (T.closedRightHamiltonian psi)) := by
    have hfun :
        (fun n => (u n).2) =
          fun n => T.rightHamiltonianLinearPMap z n :=
      funext fun n => (hzValue n).symm
    rw [hfun] at huSnd
    exact huSnd
  have hVacuumInner : inner ℝ P.vacuum P.vacuum = 1 := by
    rw [real_inner_self_eq_norm_sq, P.norm_vacuum hP]
    norm_num
  let vacuumDomain : T.rightGeneratorDomain :=
    ⟨P.vacuum, T.vacuum_mem_rightHamiltonianDomain⟩
  let coefficient : ℕ → ℝ := fun n =>
    inner ℝ
      ((z n : T.rightHamiltonianLinearPMap.domain) : P.PhysicalHilbert)
      P.vacuum
  let zOrth : ℕ → T.rightGeneratorDomain := fun n =>
    z n - coefficient n • vacuumDomain
  have hCoefficient : Tendsto coefficient atTop (nhds 0) := by
    have hinner := hzBaseTendsto.inner tendsto_const_nhds
    simpa [coefficient, hpsi] using hinner
  have hCorrection :
      Tendsto (fun n => coefficient n • P.vacuum) atTop (nhds 0) := by
    simpa using hCoefficient.smul tendsto_const_nhds
  have hzOrthBaseTendsto :
      Tendsto
        (fun n => ((zOrth n : T.rightGeneratorDomain) : P.PhysicalHilbert))
        atTop (nhds (psi : P.PhysicalHilbert)) := by
    simpa [zOrth, vacuumDomain] using hzBaseTendsto.sub hCorrection
  have hzOrthogonal : ∀ n,
      inner ℝ
        ((zOrth n : T.rightGeneratorDomain) : P.PhysicalHilbert)
        P.vacuum = 0 := by
    intro n
    change
      inner ℝ
          (((z n : T.rightHamiltonianLinearPMap.domain) : P.PhysicalHilbert) -
            coefficient n • P.vacuum)
          P.vacuum = 0
    rw [inner_sub_left, real_inner_smul_left, hVacuumInner]
    simp [coefficient]
  have hzOrthValueEq : ∀ n,
      T.rightHamiltonian (zOrth n) =
        T.rightHamiltonianLinearPMap (z n) := by
    intro n
    simp [zOrth, vacuumDomain]
  have hzOrthValueTendsto :
      Tendsto
        (fun n => T.rightHamiltonian (zOrth n))
        atTop (nhds (T.closedRightHamiltonian psi)) := by
    have hfun :
        (fun n => T.rightHamiltonian (zOrth n)) =
          fun n => T.rightHamiltonianLinearPMap (z n) :=
      funext hzOrthValueEq
    rw [hfun]
    exact hzValueTendsto
  have hLeft :
      Tendsto
        (fun n => G.mass *
          ‖((zOrth n : T.rightGeneratorDomain) : P.PhysicalHilbert)‖ ^ 2)
        atTop
        (nhds (G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2)) :=
    tendsto_const_nhds.mul (hzOrthBaseTendsto.norm.pow 2)
  have hRight :
      Tendsto
        (fun n => inner ℝ
          (T.rightHamiltonian (zOrth n))
          ((zOrth n : T.rightGeneratorDomain) : P.PhysicalHilbert))
        atTop
        (nhds
          (inner ℝ (T.closedRightHamiltonian psi)
            (psi : P.PhysicalHilbert))) :=
    hzOrthValueTendsto.inner hzOrthBaseTendsto
  apply le_of_tendsto_of_tendsto hLeft hRight
  exact Filter.Eventually.of_forall fun n =>
    FiniteVolumeVacuumGapTransfer.rightHamiltonian_inner_ge_mass_mul_norm_sq
      T G (zOrth n) (hzOrthogonal n)

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
