import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableCenteredOneStepOperatorRate
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCenteredQuadraticExcitation
import Mathlib.Topology.Sequences
import Mathlib.Tactic

noncomputable section

open Filter Function Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- A centered positive-time OS carrier represents a vector in the actual
complete vacuum-orthogonal physical Hilbert sector. -/
noncomputable def centeredPhysicalStateLinearMap
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized) :
    P.CenteredCarrier →ₗ[ℝ] P.VacuumOrthogonalHilbert where
  toFun := fun F =>
    ⟨P.physicalState (F : P.Carrier), by
      rw [P.mem_vacuumOrthogonal_iff, P.inner_vacuum_physicalState]
      exact F.property⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    change P.physicalState ((F : P.Carrier) + (G : P.Carrier)) =
      P.physicalState (F : P.Carrier) + P.physicalState (G : P.Carrier)
    simpa only [← P.physicalStateLinearMap_apply] using
      P.physicalStateLinearMap.map_add (F : P.Carrier) (G : P.Carrier)
  map_smul' := by
    intro c F
    apply Subtype.ext
    change P.physicalState (c • (F : P.Carrier)) =
      c • P.physicalState (F : P.Carrier)
    simpa only [← P.physicalStateLinearMap_apply] using
      P.physicalStateLinearMap.map_smul c (F : P.Carrier)

@[simp] theorem centeredPhysicalStateLinearMap_apply_coe
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized)
    (F : P.CenteredCarrier) :
    ((P.centeredPhysicalStateLinearMap hP F : P.VacuumOrthogonalHilbert) :
      P.PhysicalHilbert) = P.physicalState (F : P.Carrier) :=
  rfl

/-- The centered represented-state map preserves the OS norm exactly. -/
@[simp] theorem norm_centeredPhysicalStateLinearMap
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized)
    (F : P.CenteredCarrier) :
    ‖P.centeredPhysicalStateLinearMap hP F‖ = ‖F‖ := by
  change ‖P.physicalState (F : P.Carrier)‖ = ‖(F : P.Carrier)‖
  exact P.norm_physicalState (F : P.Carrier)

/-- The expectation-zero carrier is a dense norm-preserving core of the actual
vacuum-orthogonal OS Hilbert sector.

Starting from density of all represented positive-time observables, center each
approximant.  Because the target vector is orthogonal to the normalized vacuum,
the vacuum coefficients of the approximants tend to zero, so centering does not
change the limit. -/
theorem centeredPhysicalStateLinearMap_denseRange
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized) :
    DenseRange (P.centeredPhysicalStateLinearMap hP) := by
  intro psi
  have hClosure :
      (psi : P.PhysicalHilbert) ∈
        closure (Set.range P.physicalStateLinearMap) :=
    P.physicalStateLinearMap_denseRange (psi : P.PhysicalHilbert)
  rw [mem_closure_iff_seq_limit] at hClosure
  rcases hClosure with ⟨u, huRange, huTendsto⟩
  choose F hF using fun n => huRange n
  have hFState :
      Tendsto (fun n => P.physicalState (F n)) atTop
        (nhds (psi : P.PhysicalHilbert)) := by
    have hfun :
        (fun n => P.physicalState (F n)) = u := by
      funext n
      simpa only [P.physicalStateLinearMap_apply] using hF n
    rw [hfun]
    exact huTendsto
  have hpsiOrth : inner ℝ P.vacuum (psi : P.PhysicalHilbert) = 0 :=
    (P.mem_vacuumOrthogonal_iff (psi : P.PhysicalHilbert)).mp psi.property
  have hcoeff :
      Tendsto
        (fun n => inner ℝ P.vacuum (P.physicalState (F n)))
        atTop (nhds 0) := by
    have hinner :
        Continuous (fun x : P.PhysicalHilbert => inner ℝ P.vacuum x) := by
      fun_prop
    have h := hinner.continuousAt.tendsto.comp hFState
    simpa only [hpsiOrth] using h
  let Fc : ℕ → P.CenteredCarrier := fun n =>
    ⟨P.vacuumCenteredCarrier (F n),
      P.vacuumCenteredCarrier_mem_centeredCarrierSubmodule hP (F n)⟩
  have hcenteredAmbient :
      Tendsto
        (fun n =>
          ((P.centeredPhysicalStateLinearMap hP (Fc n) :
            P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))
        atTop (nhds (psi : P.PhysicalHilbert)) := by
    have hvacuumCorrection :
        Tendsto
          (fun n =>
            inner ℝ P.vacuum (P.physicalState (F n)) • P.vacuum)
          atTop (nhds 0) := by
      simpa using hcoeff.smul_const P.vacuum
    have hsub := hFState.sub hvacuumCorrection
    have hfun :
        (fun n =>
          ((P.centeredPhysicalStateLinearMap hP (Fc n) :
            P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) =
        fun n =>
          P.physicalState (F n) -
            inner ℝ P.vacuum (P.physicalState (F n)) • P.vacuum := by
      funext n
      change P.physicalState (P.vacuumCenteredCarrier (F n)) = _
      rw [P.physicalState_vacuumCenteredCarrier]
      rfl
    rw [hfun]
    simpa using hsub
  have hcentered :
      Tendsto (fun n => P.centeredPhysicalStateLinearMap hP (Fc n))
        atTop (nhds psi) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    rcases (Metric.tendsto_atTop.1 hcenteredAmbient) ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    change dist
      (((P.centeredPhysicalStateLinearMap hP (Fc n) :
        P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))
      (psi : P.PhysicalHilbert) < ε
    exact hN n hn
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun n => P.centeredPhysicalStateLinearMap hP (Fc n), ?_, hcentered⟩
  intro n
  exact ⟨Fc n, rfl⟩

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end