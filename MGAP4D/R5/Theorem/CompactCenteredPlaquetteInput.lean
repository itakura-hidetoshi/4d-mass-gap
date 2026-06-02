import MGAP4D.R4.Theorem.SpectralMeasurePVMInput
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapCompactPlaquetteInputHandoff
import MGAP4D.R5.TheoremSurface.ExportSurface

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R5 compact-centered plaquette observable input packet in the seven-stage
analytic roadmap.

In the seven-stage roadmap, R4 is the spectral-measure/PVM layer and R5 is the
compact centered plaquette observable layer.  This packet therefore starts from
R4 spectral-measure/PVM input readiness and records the compact/centered/smeared
observable input surface.  It does not yet claim a concrete lattice-gauge
plaquette construction. -/
def CompactCenteredPlaquetteInputPacket : Prop :=
  R4.Theorem.SpectralMeasurePVMInputReady ∧
  MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapCompactPlaquetteInputHandoffReady ∧
  IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
    (MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
      MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) ∧
  MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
    (MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
      MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) ∧
  MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
    (MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
      MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) ∧
  MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
    MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
      MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette

/-- The R5 compact-centered plaquette observable input packet is ready. -/
theorem compact_centered_plaquette_input_packet_ready :
    CompactCenteredPlaquetteInputPacket := by
  exact ⟨
    R4.Theorem.spectral_measure_pvm_input_ready,
    MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_compact_plaquette_input_handoff_ready,
    R4.Theorem.r4_self_adjoint_operator_input_ready,
    MathlibAnalytic.singleton_compact_plaquette_constructed_compact_support,
    MathlibAnalytic.singleton_compact_plaquette_constructed_centered,
    MathlibAnalytic.singleton_compact_plaquette_constructed_smeared,
    MathlibAnalytic.singleton_compact_plaquette_chosen_observable_def⟩

/-- R5 compact-centered plaquette boundary.

The compact/centered/smeared observable input is ready.  The concrete
lattice-gauge plaquette construction remains a visible R5 downstream obligation. -/
def CompactCenteredPlaquetteBoundary : Prop :=
  CompactCenteredPlaquetteInputPacket ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapCompactPlaquetteInputHandoffSurface.boundaryConcreteLatticeGaugePlaquetteStillSeparate

/-- The R5 compact-centered plaquette boundary is ready. -/
theorem compact_centered_plaquette_boundary_ready :
    CompactCenteredPlaquetteBoundary := by
  exact ⟨compact_centered_plaquette_input_packet_ready, trivial⟩

/-- Public R5 readiness predicate in the seven-stage analytic roadmap. -/
def CompactCenteredPlaquetteInputReady : Prop :=
  CompactCenteredPlaquetteInputPacket ∧ CompactCenteredPlaquetteBoundary

/-- R5 compact-centered plaquette input is ready. -/
theorem compact_centered_plaquette_input_ready :
    CompactCenteredPlaquetteInputReady := by
  exact ⟨compact_centered_plaquette_input_packet_ready, compact_centered_plaquette_boundary_ready⟩

end

end Theorem
end R5
end MGAP4D