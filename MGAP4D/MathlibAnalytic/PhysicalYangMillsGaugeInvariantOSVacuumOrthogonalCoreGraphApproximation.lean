import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRescaledDefectCoreGraphLimit
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

/-- Every graph-domain vector of the closed excitation Hamiltonian is a graph
limit of canonical right-Hamiltonian core vectors that remain exactly
vacuum-orthogonal.

The construction starts with a graph-approximating sequence for the ambient
closure and subtracts the vacuum coefficient from every core vector.  Vacuum
normalization makes the corrected vectors orthogonal, while zero vacuum energy
leaves all Hamiltonian values unchanged. -/
theorem exists_vacuumOrthogonalRightHamiltonianCore_graph_approximation
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
    ∃ u : ℕ → T.vacuumOrthogonalRightHamiltonianCoreDomain,
      Tendsto
          (fun n =>
            ((u n : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
              P.VacuumOrthogonalHilbert))
          atTop
          (𝓝 (psi : P.VacuumOrthogonalHilbert)) ∧
        Tendsto
          (fun n =>
            T.vacuumOrthogonalClosedRightHamiltonian
              (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric
                hInnerSymmetric)
              (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint
                (u n)))
          atTop
          (𝓝
            (T.vacuumOrthogonalClosedRightHamiltonian
              (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric
                hInnerSymmetric)
              psi)) := by
  let hClosedSymmetric :=
    T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric hInnerSymmetric
  let psiAmbient := T.vacuumOrthogonalAmbientDomainPoint psi
  have hgraph :
      (((psiAmbient : T.closedRightHamiltonian.domain) : P.PhysicalHilbert),
          T.closedRightHamiltonian psiAmbient) ∈
        T.rightHamiltonianLinearPMap.graph.topologicalClosure := by
    rw [T.closedRightHamiltonian_graph_eq]
    exact T.closedRightHamiltonian.mem_graph psiAmbient
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    mem_closure_iff_seq_limit] at hgraph
  rcases hgraph with ⟨v, hvGraph, hv⟩
  choose z hzBase hzValue using fun n =>
    (LinearPMap.mem_graph_iff T.rightHamiltonianLinearPMap).1 (hvGraph n)

  have hvFst :
      Tendsto (fun n => (v n).1) atTop
        (𝓝 ((psiAmbient : T.closedRightHamiltonian.domain) :
          P.PhysicalHilbert)) := by
    simpa only [Function.comp_apply] using
      (continuous_fst.tendsto
        (((psiAmbient : T.closedRightHamiltonian.domain) : P.PhysicalHilbert),
          T.closedRightHamiltonian psiAmbient)).comp hv
  have hbaseEq :
      (fun n => (v n).1) =
        fun n => ((z n : T.rightHamiltonianLinearPMap.domain) :
          P.PhysicalHilbert) :=
    funext fun n => (hzBase n).symm
  rw [hbaseEq] at hvFst

  have hvSnd :
      Tendsto (fun n => (v n).2) atTop
        (𝓝 (T.closedRightHamiltonian psiAmbient)) := by
    simpa only [Function.comp_apply] using
      (continuous_snd.tendsto
        (((psiAmbient : T.closedRightHamiltonian.domain) : P.PhysicalHilbert),
          T.closedRightHamiltonian psiAmbient)).comp hv
  have hvalueEq :
      (fun n => (v n).2) =
        fun n => T.rightHamiltonianLinearPMap (z n) := by
    funext n
    exact (hzValue n).symm
  rw [hvalueEq] at hvSnd

  let zCore : ℕ → T.rightGeneratorDomain := fun n =>
    (show T.rightGeneratorDomain from z n)
  have hzCoreFst :
      Tendsto
        (fun n => ((zCore n : T.rightGeneratorDomain) : P.PhysicalHilbert))
        atTop
        (𝓝 ((psi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) := by
    simpa only [zCore, psiAmbient,
      vacuumOrthogonalAmbientDomainPoint] using hvFst
  have hzCoreSnd :
      Tendsto (fun n => T.rightHamiltonian (zCore n)) atTop
        (𝓝 (T.closedRightHamiltonian psiAmbient)) := by
    simpa only [zCore, T.rightHamiltonianLinearPMap_apply] using hvSnd

  let vacuumDomain : T.rightGeneratorDomain :=
    ⟨P.vacuum, T.vacuum_mem_rightHamiltonianDomain⟩
  let coefficient : ℕ → ℝ := fun n =>
    inner ℝ ((zCore n : T.rightGeneratorDomain) : P.PhysicalHilbert)
      P.vacuum
  let zOrth : ℕ → T.rightGeneratorDomain := fun n =>
    zCore n - coefficient n • vacuumDomain

  have hvacuumInner : inner ℝ P.vacuum P.vacuum = 1 := by
    rw [real_inner_self_eq_norm_sq, P.norm_vacuum hP]
    norm_num
  have hVacuumHamiltonian : T.rightHamiltonian vacuumDomain = 0 := by
    simpa only [vacuumDomain] using T.rightHamiltonian_vacuum
  have hzOrthogonal (n : ℕ) :
      inner ℝ ((zOrth n : T.rightGeneratorDomain) : P.PhysicalHilbert)
        P.vacuum = 0 := by
    change inner ℝ
        (((zCore n : T.rightGeneratorDomain) : P.PhysicalHilbert) -
          coefficient n • P.vacuum)
        P.vacuum = 0
    rw [inner_sub_left, real_inner_smul_left, hvacuumInner, mul_one]
    simp [coefficient]
  have hCoefficient : Tendsto coefficient atTop (𝓝 0) := by
    have hinner :
        Tendsto
          (fun n => inner ℝ
            ((zCore n : T.rightGeneratorDomain) : P.PhysicalHilbert)
            P.vacuum)
          atTop
          (𝓝 (inner ℝ
            ((psi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)
            P.vacuum)) :=
      hzCoreFst.inner (𝕜 := ℝ) tendsto_const_nhds
    have hpsi :
        inner ℝ
          ((psi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)
          P.vacuum = 0 := by
      rw [real_inner_comm]
      exact (P.mem_vacuumOrthogonal_iff _).mp
        (psi : P.VacuumOrthogonalHilbert).property
    simpa only [coefficient, hpsi] using hinner
  have hzOrthFst :
      Tendsto
        (fun n => ((zOrth n : T.rightGeneratorDomain) : P.PhysicalHilbert))
        atTop
        (𝓝 ((psi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) := by
    change Tendsto
      (fun n =>
        ((zCore n : T.rightGeneratorDomain) : P.PhysicalHilbert) -
          coefficient n • P.vacuum)
      atTop
      (𝓝 ((psi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))
    simpa using hzCoreFst.sub (hCoefficient.smul_const P.vacuum)
  have hzOrthValue (n : ℕ) :
      T.rightHamiltonian (zOrth n) = T.rightHamiltonian (zCore n) := by
    change T.rightHamiltonian (zCore n - coefficient n • vacuumDomain) =
      T.rightHamiltonian (zCore n)
    rw [map_sub, map_smul, hVacuumHamiltonian, smul_zero, sub_zero]
  have hzOrthSnd :
      Tendsto (fun n => T.rightHamiltonian (zOrth n)) atTop
        (𝓝 (T.closedRightHamiltonian psiAmbient)) := by
    rw [show (fun n => T.rightHamiltonian (zOrth n)) =
        (fun n => T.rightHamiltonian (zCore n)) by
      funext n
      exact hzOrthValue n]
    exact hzCoreSnd

  let u : ℕ → T.vacuumOrthogonalRightHamiltonianCoreDomain := fun n =>
    ⟨⟨((zOrth n : T.rightGeneratorDomain) : P.PhysicalHilbert), by
        rw [P.mem_vacuumOrthogonal_iff, real_inner_comm]
        exact hzOrthogonal n⟩,
      (zOrth n).property⟩
  refine ⟨u, ?_, ?_⟩

  · rw [nhds_subtype, tendsto_comap_iff]
    change Tendsto
      (fun n => (((u n : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
        P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))
      atTop
      (𝓝 ((psi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))
    simpa only [u] using hzOrthFst

  · rw [nhds_subtype, tendsto_comap_iff]
    change Tendsto
      (fun n =>
        (((T.vacuumOrthogonalClosedRightHamiltonian hClosedSymmetric
              (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint
                (u n)) : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)))
      atTop
      (𝓝
        (((T.vacuumOrthogonalClosedRightHamiltonian hClosedSymmetric psi :
          P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)))
    have hFunctions :
        (fun n =>
          (((T.vacuumOrthogonalClosedRightHamiltonian hClosedSymmetric
                (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint
                  (u n)) : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))) =
        (fun n => T.rightHamiltonian (zOrth n)) := by
      funext n
      calc
        (((T.vacuumOrthogonalClosedRightHamiltonian hClosedSymmetric
              (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint
                (u n)) : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) =
            T.rightHamiltonian
              (T.vacuumOrthogonalRightHamiltonianCoreAmbientPoint (u n)) :=
          T.vacuumOrthogonalClosedRightHamiltonian_core_apply
            hInnerSymmetric (u n)
        _ = T.rightHamiltonian (zOrth n) := by
          rfl
    rw [hFunctions]
    simpa only [psiAmbient,
      T.vacuumOrthogonalClosedRightHamiltonian_apply] using hzOrthSnd

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
