import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRescaledDefectSpectrum
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalHamiltonian

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

/-- The canonical right-Hamiltonian core inside the complete
vacuum-orthogonal excitation Hilbert space. -/
def vacuumOrthogonalRightHamiltonianCoreDomain
    (T : P.StronglyContinuousPhysicalSemigroup) :
    Submodule ℝ P.VacuumOrthogonalHilbert where
  carrier := {x |
    (((x : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) ∈
      T.rightGeneratorDomain}
  zero_mem' := T.rightGeneratorDomain.zero_mem
  add_mem' := by
    intro x y hx hy
    change
      (((x + y : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) ∈
        T.rightGeneratorDomain
    exact T.rightGeneratorDomain.add_mem hx hy
  smul_mem' := by
    intro c x hx
    change
      ((c • (x : P.VacuumOrthogonalHilbert) :
          P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) ∈
        T.rightGeneratorDomain
    exact T.rightGeneratorDomain.smul_mem c hx

/-- A vacuum-orthogonal core vector viewed in the ambient right-generator
domain. -/
def vacuumOrthogonalRightHamiltonianCoreAmbientPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
    T.rightGeneratorDomain :=
  ⟨(((x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
      P.VacuumOrthogonalHilbert) : P.PhysicalHilbert), x.property⟩

/-- The same core vector viewed in the domain of the partially defined right
Hamiltonian. -/
def vacuumOrthogonalRightHamiltonianCoreLinearPMapPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
    T.rightHamiltonianLinearPMap.domain :=
  ⟨(((x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
      P.VacuumOrthogonalHilbert) : P.PhysicalHilbert), by
    simpa only [T.rightHamiltonianLinearPMap_domain] using x.property⟩

/-- The canonical core embeds into the graph-closed excitation Hamiltonian
domain. -/
def vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
    T.vacuumOrthogonalClosedRightHamiltonianDomain :=
  ⟨((x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
      P.VacuumOrthogonalHilbert), by
    apply T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.1
    simpa only [T.rightHamiltonianLinearPMap_domain] using x.property⟩

/-- On a core vector, the excitation-sector rescaled defect is exactly the
ambient right Hamiltonian difference quotient. -/
theorem vacuumOrthogonalRescaledDefect_coe_eq_rightHamiltonianDifferenceQuotient
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal)
    (x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
    (((T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hSymmetric t
          (x : P.VacuumOrthogonalHilbert) :
        P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) =
      T.rightHamiltonianDifferenceQuotient
        (((x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
          P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) t := by
  change
    (t : ℝ)⁻¹ •
        ((((x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
            P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) -
          T.toPhysicalSemigroup.operator t
            (((x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
              P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) =
      (t : ℝ)⁻¹ •
        ((((x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
            P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) -
          T.toPhysicalSemigroup.operator t
            (((x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
              P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))
  rfl

/-- The semigroup difference quotient converges to the canonical right
Hamiltonian on every vector of its defining core. -/
theorem rightHamiltonianDifferenceQuotient_tendsto_on_vacuumOrthogonalCore
    (T : P.StronglyContinuousPhysicalSemigroup)
    (x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
    Tendsto
      (fun t : NNReal =>
        T.rightHamiltonianDifferenceQuotient
          (((x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
            P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) t)
      (nhdsWithin 0 (Ioi 0))
      (nhds
        (T.rightHamiltonian
          (T.vacuumOrthogonalRightHamiltonianCoreAmbientPoint x))) := by
  have h :=
    T.rightHamiltonian_hasRightHamiltonianValue
      (T.vacuumOrthogonalRightHamiltonianCoreAmbientPoint x)
  unfold HasRightHamiltonianValue HasRightGeneratorValue at h
  have hneg := h.neg
  simpa only [rightHamiltonianDifferenceQuotient_eq_neg, neg_neg] using hneg

/-- The graph closure agrees with the original right Hamiltonian on the
canonical vacuum-orthogonal core. -/
theorem vacuumOrthogonalClosedRightHamiltonian_core_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
    (((T.vacuumOrthogonalClosedRightHamiltonian
          (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric hSymmetric)
          (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint x) :
        P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) =
      T.rightHamiltonian
        (T.vacuumOrthogonalRightHamiltonianCoreAmbientPoint x) := by
  let corePoint := T.vacuumOrthogonalRightHamiltonianCoreLinearPMapPoint x
  have hvalue :
      T.rightHamiltonianLinearPMap corePoint =
        T.closedRightHamiltonian
          (T.vacuumOrthogonalAmbientDomainPoint
            (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint x)) :=
    T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.2 rfl
  change
    T.closedRightHamiltonian
        (T.vacuumOrthogonalAmbientDomainPoint
          (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint x)) =
      T.rightHamiltonian
        (T.vacuumOrthogonalRightHamiltonianCoreAmbientPoint x)
  simpa only [corePoint, rightHamiltonianLinearPMap_apply,
    vacuumOrthogonalRightHamiltonianCoreLinearPMapPoint,
    vacuumOrthogonalRightHamiltonianCoreAmbientPoint] using hvalue.symm

/-- The bounded excitation difference quotients converge strongly, on the
canonical core, to the graph-closed vacuum-orthogonal Hamiltonian. -/
theorem vacuumOrthogonalRescaledDefect_tendsto_closedRightHamiltonian_on_core
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
    Tendsto
      (fun t : NNReal =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hSymmetric t (x : P.VacuumOrthogonalHilbert))
      (nhdsWithin 0 (Ioi 0))
      (nhds
        (T.vacuumOrthogonalClosedRightHamiltonian
          (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric hSymmetric)
          (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint x))) := by
  have hAmbient :=
    T.rightHamiltonianDifferenceQuotient_tendsto_on_vacuumOrthogonalCore x
  rw [← T.vacuumOrthogonalClosedRightHamiltonian_core_apply hSymmetric x] at hAmbient
  rw [nhds_subtype, tendsto_comap_iff]
  change
    Tendsto
      (fun t : NNReal =>
        (((T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hSymmetric t (x : P.VacuumOrthogonalHilbert) :
          P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)))
      (nhdsWithin 0 (Ioi 0))
      (nhds
        (((T.vacuumOrthogonalClosedRightHamiltonian
            (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric hSymmetric)
            (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint x) :
          P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)))
  have hFunctions :
      (fun t : NNReal =>
        (((T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hSymmetric t (x : P.VacuumOrthogonalHilbert) :
          P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))) =
      (fun t : NNReal =>
        T.rightHamiltonianDifferenceQuotient
          (((x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
            P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) t) := by
    funext t
    exact
      T.vacuumOrthogonalRescaledDefect_coe_eq_rightHamiltonianDifferenceQuotient
        hSymmetric t x
  rw [hFunctions]
  exact hAmbient

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
