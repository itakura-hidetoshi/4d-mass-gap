import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedMassTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingReflectedQuadraticGap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

/-- Vacuum centering of an represented positive-time observable lands in the
actual complete OS excitation sector once the vacuum is normalized. -/
theorem physicalState_vacuumCenteredCarrier_mem_vacuumOrthogonal
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized)
    (F : P.Carrier) :
    P.physicalState (P.vacuumCenteredCarrier F) ∈ P.vacuumOrthogonal := by
  rw [P.mem_vacuumOrthogonal_iff, P.physicalState_vacuumCenteredCarrier]
  unfold finiteVacuumCentered
  have hvacuumInner : inner ℝ P.vacuum P.vacuum = 1 := by
    rw [real_inner_self_eq_norm_sq, P.norm_vacuum hP]
    norm_num
  rw [inner_sub_right, inner_smul_right, hvacuumInner]
  simp

/-- Strict positivity of a centered OS quadratic value is exactly enough to
prevent its represented physical state from collapsing to zero in the OS
quotient/completion. -/
theorem physicalState_vacuumCenteredCarrier_ne_zero_of_osQuadraticValue_pos
    (P : D.OSPreHilbertData)
    (F : P.Carrier)
    (hF : 0 < P.osQuadraticValue (P.vacuumCenteredCarrier F)) :
    P.physicalState (P.vacuumCenteredCarrier F) ≠ 0 := by
  let Fc := P.vacuumCenteredCarrier F
  have hnormsq :
      ‖P.physicalState Fc‖ ^ 2 = P.osQuadraticValue Fc := by
    rw [P.norm_physicalState, P.osQuadraticValue_eq_norm_sq]
  have hnormsqPos : 0 < ‖P.physicalState Fc‖ ^ 2 := by
    rw [hnormsq]
    exact hF
  intro hzero
  rw [hzero, norm_zero] at hnormsqPos
  norm_num at hnormsqPos

/-- The canonical actual excitation vector represented by a centered OS
observable. -/
def centeredPhysicalExcitation
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized)
    (F : P.Carrier) : P.VacuumOrthogonalHilbert :=
  ⟨P.physicalState (P.vacuumCenteredCarrier F),
    P.physicalState_vacuumCenteredCarrier_mem_vacuumOrthogonal hP F⟩

/-- A strictly positive centered OS quadratic value gives a nonzero vector in
the actual complete excitation Hilbert space. -/
theorem centeredPhysicalExcitation_ne_zero_of_osQuadraticValue_pos
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized)
    (F : P.Carrier)
    (hF : 0 < P.osQuadraticValue (P.vacuumCenteredCarrier F)) :
    P.centeredPhysicalExcitation hP F ≠ 0 := by
  intro hzero
  have hval :
      P.physicalState (P.vacuumCenteredCarrier F) = 0 := by
    exact congrArg Subtype.val hzero
  exact
    (P.physicalState_vacuumCenteredCarrier_ne_zero_of_osQuadraticValue_pos F hF)
      hval

namespace StronglyContinuousPhysicalSemigroup

/-- A positive centered OS variance produces the genuine nonzero
vacuum-orthogonal closed-Hamiltonian-domain witness required by the variational
Yang--Mills mass.  No synthetic Hilbert carrier or prescribed mass value occurs
in this construction. -/
noncomputable def physicalYangMillsExcitationDomainWitness_of_centered_osQuadraticValue_pos
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (F : P.Carrier)
    (hF : 0 < P.osQuadraticValue (P.vacuumCenteredCarrier F)) :
    T.PhysicalYangMillsExcitationDomainWitness :=
  T.physicalYangMillsExcitationDomainWitness_of_nonzeroExcitation
    hP hSelf (P.centeredPhysicalExcitation hP F)
    (P.centeredPhysicalExcitation_ne_zero_of_osQuadraticValue_pos hP F hF)

/-- A continuum transfer gap is a lower bound on the derived physical
Yang--Mills mass as soon as one centered OS observable has strictly positive
quadratic value. -/
theorem VacuumSemigroupGapSlope.mass_le_physicalYangMillsMass_of_centered_osQuadraticValue_pos
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (F : P.Carrier)
    (hF : 0 < P.osQuadraticValue (P.vacuumCenteredCarrier F)) :
    G.mass ≤ T.physicalYangMillsMass :=
  G.mass_le_physicalYangMillsMass T hP
    (T.physicalYangMillsExcitationDomainWitness_of_centered_osQuadraticValue_pos
      hP hSelf F hF)

/-- Consequently a positive continuum transfer slope proves a positive mass for
the actual Yang--Mills Hamiltonian from one genuinely nonzero centered OS
observable. -/
theorem VacuumSemigroupGapSlope.physicalYangMillsMass_pos_of_centered_osQuadraticValue_pos
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (F : P.Carrier)
    (hF : 0 < P.osQuadraticValue (P.vacuumCenteredCarrier F)) :
    0 < T.physicalYangMillsMass :=
  lt_of_lt_of_le G.mass_pos
    (G.mass_le_physicalYangMillsMass_of_centered_osQuadraticValue_pos
      T hP hSelf F hF)

/-- The finite-volume transfer package has the same correct interpretation:
its mass parameter bounds the actual derived continuum mass from below. -/
theorem FiniteVolumeVacuumGapTransfer.mass_le_physicalYangMillsMass_of_centered_osQuadraticValue_pos
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (F : P.Carrier)
    (hF : 0 < P.osQuadraticValue (P.vacuumCenteredCarrier F)) :
    G.mass ≤ T.physicalYangMillsMass :=
  G.mass_le_physicalYangMillsMass T hP
    (T.physicalYangMillsExcitationDomainWitness_of_centered_osQuadraticValue_pos
      hP hSelf F hF)

/-- Any positive finite-volume transfer gap therefore yields positivity of the
mass derived from the actual continuum OS Hamiltonian, provided the continuum
OS theory contains one positive-variance centered observable. -/
theorem FiniteVolumeVacuumGapTransfer.physicalYangMillsMass_pos_of_centered_osQuadraticValue_pos
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (F : P.Carrier)
    (hF : 0 < P.osQuadraticValue (P.vacuumCenteredCarrier F)) :
    0 < T.physicalYangMillsMass :=
  lt_of_lt_of_le G.mass_pos
    (G.mass_le_physicalYangMillsMass_of_centered_osQuadraticValue_pos
      T hP hSelf F hF)

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
