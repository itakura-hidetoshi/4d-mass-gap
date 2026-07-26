import MGAP4D.MathlibAnalytic.FiniteFamilyPositiveDiagonalSelection
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonian
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

/-- A finite moving family of continuum vectors in the right-generator domain,
whose right-Hamiltonian values asymptotically agree with prescribed targets.

No shrinking-time sequence is supplied.  It is selected below from the local
right-Hamiltonian difference-quotient limits, simultaneously for the whole
finite family at every scale. -/
structure MovingRightHamiltonianGraphData
    (T : P.StronglyContinuousPhysicalSemigroup)
    {ι : Type*}
    [Fintype ι]
    (psi target : ℕ → ι → P.PhysicalHilbert) where
  mem_rightGeneratorDomain :
    ∀ n i, psi n i ∈ T.rightGeneratorDomain
  graphDefect_tendsto_zero :
    ∀ i,
      Tendsto
        (fun n =>
          T.rightHamiltonian
              ⟨psi n i, mem_rightGeneratorDomain n i⟩ -
            target n i)
        atTop (nhds 0)

namespace MovingRightHamiltonianGraphData

variable
    {T : P.StronglyContinuousPhysicalSemigroup}
    {ι : Type*}
    [Fintype ι]
    {psi target : ℕ → ι → P.PhysicalHilbert}

/-- A moving continuum vector bundled in the right-generator domain. -/
noncomputable def domainPoint
    (R : MovingRightHamiltonianGraphData T psi target)
    (n : ℕ) (i : ι) : T.rightGeneratorDomain :=
  ⟨psi n i, R.mem_rightGeneratorDomain n i⟩

@[simp] theorem domainPoint_coe
    (R : MovingRightHamiltonianGraphData T psi target)
    (n : ℕ) (i : ι) :
    (R.domainPoint n i : P.PhysicalHilbert) = psi n i :=
  rfl

/-- The local residual between the continuum Hamiltonian difference quotient and
its right-Hamiltonian value at one moving domain point. -/
noncomputable def localDifferenceQuotientResidual
    (R : MovingRightHamiltonianGraphData T psi target)
    (n : ℕ) (i : ι) (t : NNReal) : P.PhysicalHilbert :=
  T.rightHamiltonianDifferenceQuotient (psi n i) t -
    T.rightHamiltonian (R.domainPoint n i)

/-- At each fixed scale and family member, the local continuum Hamiltonian
difference-quotient residual tends to zero through positive times. -/
theorem localDifferenceQuotientResidual_tendsto_zero
    (R : MovingRightHamiltonianGraphData T psi target)
    (n : ℕ) (i : ι) :
    Tendsto (R.localDifferenceQuotientResidual n i)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hvalue :=
    T.rightHamiltonian_hasRightHamiltonianValue (R.domainPoint n i)
  unfold HasRightHamiltonianValue HasRightGeneratorValue at hvalue
  have hneg := hvalue.neg
  have hquotient :
      Tendsto
        (fun t : NNReal =>
          T.rightHamiltonianDifferenceQuotient (psi n i) t)
        (nhdsWithin 0 (Ioi 0))
        (nhds (T.rightHamiltonian (R.domainPoint n i))) := by
    simpa [domainPoint] using hneg
  have hconstant :
      Tendsto
        (fun _ : NNReal => T.rightHamiltonian (R.domainPoint n i))
        (nhdsWithin 0 (Ioi 0))
        (nhds (T.rightHamiltonian (R.domainPoint n i))) :=
    tendsto_const_nhds
  change Tendsto
    (fun t : NNReal =>
      T.rightHamiltonianDifferenceQuotient (psi n i) t -
        T.rightHamiltonian (R.domainPoint n i))
    (nhdsWithin 0 (Ioi 0)) (nhds 0)
  simpa only [sub_self] using hquotient.sub hconstant

/-- Simultaneous positive diagonal selection for the local continuum generator
residuals of the complete finite moving family. -/
noncomputable def diagonalSelection
    (R : MovingRightHamiltonianGraphData T psi target) :
    FiniteFamilyPositiveDiagonalSelectionData
      (fun n i t => R.localDifferenceQuotientResidual n i t) :=
  FiniteFamilyPositiveDiagonalSelectionData.of_tendsto
    R.localDifferenceQuotientResidual_tendsto_zero

/-- The automatically selected positive width at scale `n`. -/
noncomputable def width
    (R : MovingRightHamiltonianGraphData T psi target)
    (n : ℕ) : NNReal :=
  R.diagonalSelection.width n

/-- Every automatically selected width is strictly positive. -/
theorem width_pos
    (R : MovingRightHamiltonianGraphData T psi target)
    (n : ℕ) : 0 < R.width n :=
  R.diagonalSelection.width_pos n

/-- The automatically selected widths shrink to zero through positive times. -/
theorem width_tendsto_zero
    (R : MovingRightHamiltonianGraphData T psi target) :
    Tendsto R.width atTop (nhdsWithin 0 (Ioi 0)) := by
  simpa [width] using R.diagonalSelection.width_tendsto_zero

/-- Every local continuum difference-quotient residual tends to zero along the
one automatically selected common width sequence. -/
theorem localDifferenceQuotientResidual_diagonal_tendsto_zero
    (R : MovingRightHamiltonianGraphData T psi target)
    (i : ι) :
    Tendsto
      (fun n => R.localDifferenceQuotientResidual n i (R.width n))
      atTop (nhds 0) := by
  simpa [width] using R.diagonalSelection.defect_tendsto_zero i

/-- Local right-generator convergence along the selected widths, combined with
asymptotic graph compatibility, gives the prescribed moving target directly. -/
theorem differenceQuotient_sub_target_tendsto_zero
    (R : MovingRightHamiltonianGraphData T psi target)
    (i : ι) :
    Tendsto
      (fun n =>
        T.rightHamiltonianDifferenceQuotient (psi n i) (R.width n) -
          target n i)
      atTop (nhds 0) := by
  have hsum :=
    (R.localDifferenceQuotientResidual_diagonal_tendsto_zero i).add
      (R.graphDefect_tendsto_zero i)
  have hfunction :
      (fun n =>
        T.rightHamiltonianDifferenceQuotient (psi n i) (R.width n) -
          target n i) =
      (fun n =>
        R.localDifferenceQuotientResidual n i (R.width n) +
          (T.rightHamiltonian (R.domainPoint n i) - target n i)) := by
    funext n
    dsimp [localDifferenceQuotientResidual]
    module
  rw [hfunction]
  simpa only [zero_add] using hsum

end MovingRightHamiltonianGraphData

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
