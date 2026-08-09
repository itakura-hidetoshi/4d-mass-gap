import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSemigroupSymmetry
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSTimeAverageGeneratorDomain
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCore
import Mathlib.Analysis.InnerProductSpace.Dual
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

/-- Inner-product symmetry together with the fixed vacuum shows that every
positive-time physical operator preserves the vacuum-orthogonal excitation
sector.  No spectral or mass input enters this statement. -/
theorem physicalOperator_mem_vacuumOrthogonal_of_innerSymmetric
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) {psi : P.PhysicalHilbert}
    (hpsi : psi ∈ P.vacuumOrthogonal) :
    T.toPhysicalSemigroup.operator t psi ∈ P.vacuumOrthogonal := by
  rw [P.mem_vacuumOrthogonal_iff] at hpsi ⊢
  calc
    inner ℝ P.vacuum (T.toPhysicalSemigroup.operator t psi) =
        inner ℝ (T.toPhysicalSemigroup.operator t P.vacuum) psi := by
      symm
      exact hSymmetric t P.vacuum psi
    _ = inner ℝ P.vacuum psi := by
      rw [T.toPhysicalSemigroup.fixes_vacuum]
    _ = 0 := hpsi

/-- The real-time orbit used by the Bochner average remains in the excitation
sector whenever the completed semigroup is inner-product symmetric. -/
theorem realPhysicalOrbit_mem_vacuumOrthogonal_of_innerSymmetric
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (s : ℝ) {psi : P.PhysicalHilbert}
    (hpsi : psi ∈ P.vacuumOrthogonal) :
    T.realPhysicalOrbit psi s ∈ P.vacuumOrthogonal := by
  exact T.physicalOperator_mem_vacuumOrthogonal_of_innerSymmetric
    hSymmetric s.toNNReal hpsi

/-- The unnormalized Bochner time integral preserves vacuum orthogonality.

The proof applies the continuous linear functional
`innerSL ℝ vacuum` through the interval integral and uses pointwise excitation
preservation. -/
theorem timeIntegral_mem_vacuumOrthogonal_of_innerSymmetric
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (h : NNReal) {psi : P.PhysicalHilbert}
    (hpsi : psi ∈ P.vacuumOrthogonal) :
    T.timeIntegral h psi ∈ P.vacuumOrthogonal := by
  rw [P.mem_vacuumOrthogonal_iff]
  unfold timeIntegral
  calc
    inner ℝ P.vacuum
        (∫ s in (0 : ℝ)..(h : ℝ), T.realPhysicalOrbit psi s) =
      ∫ s in (0 : ℝ)..(h : ℝ),
        inner ℝ P.vacuum (T.realPhysicalOrbit psi s) := by
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm
        (innerSL ℝ P.vacuum)
        (T.realPhysicalOrbit_intervalIntegrable psi 0 (h : ℝ))]
      rfl
    _ = ∫ s in (0 : ℝ)..(h : ℝ), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact (P.mem_vacuumOrthogonal_iff
        (T.realPhysicalOrbit psi s)).mp
          (T.realPhysicalOrbit_mem_vacuumOrthogonal_of_innerSymmetric
            hSymmetric s hpsi)
    _ = 0 := by simp

/-- Every normalized time average preserves the physical excitation sector.
This also includes zero averaging width, where the average is the zero vector. -/
theorem timeAverage_mem_vacuumOrthogonal_of_innerSymmetric
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (h : NNReal) {psi : P.PhysicalHilbert}
    (hpsi : psi ∈ P.vacuumOrthogonal) :
    T.timeAverage h psi ∈ P.vacuumOrthogonal := by
  unfold timeAverage
  exact P.vacuumOrthogonal.smul_mem
    ((h : ℝ)⁻¹)
    (T.timeIntegral_mem_vacuumOrthogonal_of_innerSymmetric
      hSymmetric h hpsi)

/-- A time average bundled in the canonical right-generator domain. -/
def timeAverageGeneratorDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    T.rightGeneratorDomain :=
  ⟨T.timeAverage h psi, T.timeAverage_mem_rightGeneratorDomain h psi⟩

@[simp] theorem timeAverageGeneratorDomain_coe
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    (T.timeAverageGeneratorDomain h psi : P.PhysicalHilbert) =
      T.timeAverage h psi :=
  rfl

/-- The selected canonical right generator has the explicit endpoint-difference
value on every time average. -/
theorem rightGenerator_timeAverage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    T.rightGenerator (T.timeAverageGeneratorDomain h psi) =
      (h : ℝ)⁻¹ •
        (T.toPhysicalSemigroup.operator h psi - psi) := by
  apply T.hasRightGeneratorValue_unique
    (T.rightGenerator_hasRightGeneratorValue
      (T.timeAverageGeneratorDomain h psi))
  exact T.hasRightGeneratorValue_timeAverage h psi

/-- A time average bundled directly in the actual graph-closed physical
Hamiltonian domain. -/
def timeAverageClosedRightHamiltonianDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    T.closedRightHamiltonian.domain :=
  ⟨T.timeAverage h psi,
    T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.1
      (T.timeAverage_mem_rightGeneratorDomain h psi)⟩

@[simp] theorem timeAverageClosedRightHamiltonianDomain_coe
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    (T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert) =
      T.timeAverage h psi :=
  rfl

/-- The graph closure agrees with the canonical right Hamiltonian on the
regularized time-average core. -/
theorem closedRightHamiltonian_timeAverage_eq_rightHamiltonian
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    T.closedRightHamiltonian
        (T.timeAverageClosedRightHamiltonianDomain h psi) =
      T.rightHamiltonian (T.timeAverageGeneratorDomain h psi) := by
  exact (T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.2
    (x := T.timeAverageGeneratorDomain h psi)
    (y := T.timeAverageClosedRightHamiltonianDomain h psi) rfl).symm

/-- Exact graph-closed Hamiltonian formula for a time-averaged vector:

`H A_h psi = h⁻¹ (psi - T_h psi)`.

This is the generator-form identity needed downstream for the moving-state
Mosco-limsup estimate. -/
theorem closedRightHamiltonian_timeAverage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    T.closedRightHamiltonian
        (T.timeAverageClosedRightHamiltonianDomain h psi) =
      (h : ℝ)⁻¹ •
        (psi - T.toPhysicalSemigroup.operator h psi) := by
  rw [T.closedRightHamiltonian_timeAverage_eq_rightHamiltonian,
    T.rightHamiltonian_apply, T.rightGenerator_timeAverage]
  module

/-- Under semigroup symmetry, a vacuum-orthogonal input remains an actual
vacuum-orthogonal graph-domain state after time averaging. -/
theorem timeAverageClosedRightHamiltonianDomain_mem_vacuumOrthogonal_of_innerSymmetric
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (h : NNReal) {psi : P.PhysicalHilbert}
    (hpsi : psi ∈ P.vacuumOrthogonal) :
    (T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert) ∈
      P.vacuumOrthogonal := by
  exact T.timeAverage_mem_vacuumOrthogonal_of_innerSymmetric
    hSymmetric h hpsi

/-- In the orientation used by the physical Rayleigh recovery structures,
time averaging preserves orthogonality to the vacuum. -/
theorem inner_timeAverageClosedRightHamiltonianDomain_vacuum_eq_zero_of_innerSymmetric
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (h : NNReal) {psi : P.PhysicalHilbert}
    (hpsi : psi ∈ P.vacuumOrthogonal) :
    inner ℝ
      (T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert)
      P.vacuum = 0 := by
  rw [real_inner_comm]
  exact (P.mem_vacuumOrthogonal_iff
    (T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert)).mp
      (T.timeAverageClosedRightHamiltonianDomain_mem_vacuumOrthogonal_of_innerSymmetric
        hSymmetric h hpsi)

/-- The graph-domain regularization converges strongly back to the original
physical vector as the averaging width tends to zero from the right. -/
theorem timeAverageClosedRightHamiltonianDomain_tendsto_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    Tendsto
      (fun h : NNReal =>
        (T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert))
      (nhdsWithin 0 (Ioi 0)) (nhds psi) := by
  simpa only [timeAverageClosedRightHamiltonianDomain_coe] using
    T.timeAverage_tendsto_zero psi

/-- A nonzero vector cannot be annihilated by all sufficiently small positive
time averages.  Thus time-average graph regularization introduces no local
vanishing obstruction for each fixed nonzero state. -/
theorem eventually_timeAverageClosedRightHamiltonianDomain_ne_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0) :
    ∀ᶠ h : NNReal in nhdsWithin 0 (Ioi 0),
      (T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert) ≠ 0 := by
  have hnorm :
      Tendsto
        (fun h : NNReal =>
          ‖(T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert)‖)
        (nhdsWithin 0 (Ioi 0)) (nhds ‖psi‖) :=
    (T.timeAverageClosedRightHamiltonianDomain_tendsto_zero psi).norm
  have hnorm_pos : 0 < ‖psi‖ := norm_pos_iff.mpr hpsi
  have hevent :
      ∀ᶠ h : NNReal in nhdsWithin 0 (Ioi 0),
        0 < ‖(T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert)‖ :=
    hnorm.eventually (eventually_lt_nhds hnorm_pos)
  filter_upwards [hevent] with h hh
  exact norm_pos_iff.mp hh

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
