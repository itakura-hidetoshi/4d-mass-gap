import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCoreGraphApproximation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRescaledDefectCoreResolvent
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolvent

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

/-- A positive continuum vacuum-sector mass slope gives the same Rayleigh lower
bound on the graph-closed Hamiltonian restricted to the complete excitation
Hilbert space. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalClosedRightHamiltonian_gap
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (x : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
    G.mass * ‖(x : P.VacuumOrthogonalHilbert)‖ ^ 2 ≤
      inner ℝ
        (T.vacuumOrthogonalClosedRightHamiltonian
          (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric
            hInnerSymmetric)
          x)
        (x : P.VacuumOrthogonalHilbert) := by
  have hxOrthogonal :
      inner ℝ
          (((x : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
            P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)
          P.vacuum = 0 := by
    rw [real_inner_comm]
    exact (P.mem_vacuumOrthogonal_iff _).mp
      (x : P.VacuumOrthogonalHilbert).property
  simpa [vacuumOrthogonalClosedRightHamiltonian,
    vacuumOrthogonalClosedRightHamiltonianLinearMap] using
    G.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      T hP (T.vacuumOrthogonalAmbientDomainPoint x) hxOrthogonal

/-- If the shift of the full graph-closed excitation Hamiltonian has dense
range, then its restriction to the canonical right-Hamiltonian core also has
dense range.  Graph-core approximation is exactly the missing passage. -/
theorem vacuumOrthogonalClosedRightHamiltonianCoreShift_denseRange_of_fullShift_dense
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (lambda : ℝ)
    (hFullDense :
      Dense
        (LinearMap.range
          ((T.vacuumOrthogonalClosedRightHamiltonian
            (T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric
              hInnerSymmetric)).realShift lambda) :
            Set P.VacuumOrthogonalHilbert)) :
    DenseRange
      (fun x : T.vacuumOrthogonalRightHamiltonianCoreDomain =>
        T.vacuumOrthogonalClosedRightHamiltonianCoreShift
          hInnerSymmetric lambda x) := by
  let hClosedSymmetric :=
    T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric hInnerSymmetric
  let coreShift :=
    fun x : T.vacuumOrthogonalRightHamiltonianCoreDomain =>
      T.vacuumOrthogonalClosedRightHamiltonianCoreShift
        hInnerSymmetric lambda x
  have hFullSubset :
      LinearMap.range
          ((T.vacuumOrthogonalClosedRightHamiltonian
            hClosedSymmetric).realShift lambda) ⊆
        closure (Set.range coreShift) := by
    rintro y ⟨psi, rfl⟩
    obtain ⟨u, huBase, huValue⟩ :=
      T.exists_vacuumOrthogonalRightHamiltonianCore_graph_approximation
        hP hInnerSymmetric psi
    have hShift :
        Tendsto
          (fun n => coreShift (u n))
          atTop
          (𝓝
            ((T.vacuumOrthogonalClosedRightHamiltonian
                hClosedSymmetric).realShift lambda psi)) := by
      have hSub := huValue.sub (huBase.smul_const lambda)
      simpa only [coreShift,
        vacuumOrthogonalClosedRightHamiltonianCoreShift,
        LinearPMap.realShift_apply] using hSub
    apply mem_closure_of_tendsto hShift
    exact Eventually.of_forall fun n => ⟨u n, rfl⟩
  change Dense (Set.range coreShift)
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro y
  have hyFull :
      y ∈ closure
        (LinearMap.range
          ((T.vacuumOrthogonalClosedRightHamiltonian
            hClosedSymmetric).realShift lambda) :
          Set P.VacuumOrthogonalHilbert) := by
    rw [hFullDense.closure_eq]
    exact Set.mem_univ y
  exact (closure_minimal hFullSubset isClosed_closure) hyFull

/-- Self-adjointness and the positive transferred mass make every sub-mass
shift of the canonical excitation Hamiltonian core dense in the full
excitation Hilbert space. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalClosedRightHamiltonianCoreShift_denseRange
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass) :
    DenseRange
      (fun x : T.vacuumOrthogonalRightHamiltonianCoreDomain =>
        T.vacuumOrthogonalClosedRightHamiltonianCoreShift
          hInnerSymmetric lambda x) := by
  let hClosedSymmetric :=
    T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric hInnerSymmetric
  have hRestrictedSelf :
      IsSelfAdjoint
        (T.vacuumOrthogonalClosedRightHamiltonian hClosedSymmetric) := by
    simpa only [vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
        hP hSelf
  have hFullDense :
      Dense
        (LinearMap.range
          ((T.vacuumOrthogonalClosedRightHamiltonian
            hClosedSymmetric).realShift lambda) :
          Set P.VacuumOrthogonalHilbert) :=
    LinearPMap.realShift_dense_range
      (A := T.vacuumOrthogonalClosedRightHamiltonian hClosedSymmetric)
      hRestrictedSelf hlambda
      (G.vacuumOrthogonalClosedRightHamiltonian_gap
        T hP hInnerSymmetric)
  exact
    T.vacuumOrthogonalClosedRightHamiltonianCoreShift_denseRange_of_fullShift_dense
      hP hInnerSymmetric lambda hFullDense

/-- In particular, the fixed half-mass resolvent region used by the rescaled
semigroup defects has dense canonical core shift range. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalClosedRightHamiltonianCoreShift_denseRange_halfMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2) :
    DenseRange
      (fun x : T.vacuumOrthogonalRightHamiltonianCoreDomain =>
        T.vacuumOrthogonalClosedRightHamiltonianCoreShift
          hInnerSymmetric lambda x) :=
  G.vacuumOrthogonalClosedRightHamiltonianCoreShift_denseRange
    T hP hInnerSymmetric hSelf
    (hlambda.trans (half_lt_self G.mass_pos))

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
