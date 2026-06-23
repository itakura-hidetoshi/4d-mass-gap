import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFiniteLaplaceGeneratorDomain
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The scalar exponential weight tends to zero at natural Euclidean times. -/
theorem exponentialWeight_nat_tendsto_zero
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun n : ℕ => Real.exp ((-lambda) * (n : ℝ)))
      atTop (nhds 0) := by
  have hnonneg : 0 ≤ Real.exp (-lambda) := Real.exp_nonneg _
  have hlt : Real.exp (-lambda) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hlambda)
  have hpow :
      Tendsto (fun n : ℕ => (Real.exp (-lambda)) ^ n)
        atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hnonneg hlt
  apply hpow.congr'
  exact Filter.Eventually.of_forall fun n => by
    rw [← Real.exp_nat_mul]
    congr 1
    ring

/-- The exponentially weighted terminal orbit converges strongly to zero. -/
theorem exponentialTerminal_nat_tendsto_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (psi : P.PhysicalHilbert) :
    Tendsto
      (fun n : ℕ =>
        Real.exp ((-lambda) * (n : ℝ)) •
          T.toPhysicalSemigroup.operator (n : NNReal) psi)
      atTop (nhds 0) := by
  apply squeeze_zero_norm
    (a := fun n : ℕ =>
      Real.exp ((-lambda) * (n : ℝ)) * ‖psi‖)
  · intro n
    simpa using
      T.norm_exponential_terminal_le lambda (n : NNReal) psi
  · simpa only [zero_mul] using
      (exponentialWeight_nat_tendsto_zero hlambda).mul_const ‖psi‖

/-- Finite Laplace resolvent values converge to the target after applying the
positive closed-Hamiltonian shift. -/
theorem closedRightHamiltonianShift_finiteLaplace_tendsto
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (psi : P.PhysicalHilbert) :
    Tendsto
      (fun n : ℕ =>
        T.closedRightHamiltonianShift lambda
          (T.finiteLaplaceIntegralClosedDomain lambda (n : NNReal) psi))
      atTop (nhds psi) := by
  have hterminal := T.exponentialTerminal_nat_tendsto_zero hlambda psi
  have hsub :
      Tendsto
        (fun n : ℕ =>
          psi - Real.exp ((-lambda) * (n : ℝ)) •
            T.toPhysicalSemigroup.operator (n : NNReal) psi)
        atTop (nhds (psi - 0)) :=
    tendsto_const_nhds.sub hterminal
  simpa only [sub_zero,
    T.closedRightHamiltonianShift_finiteLaplaceIntegral] using hsub

/-- Every positive closed-Hamiltonian shift has dense range. -/
theorem closedRightHamiltonianShift_denseRange
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Dense (Set.range (T.closedRightHamiltonianShift lambda)) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro psi
  apply mem_closure_of_tendsto
    (T.closedRightHamiltonianShift_finiteLaplace_tendsto hlambda psi)
  exact Filter.Eventually.of_forall fun n =>
    ⟨T.finiteLaplaceIntegralClosedDomain lambda (n : NNReal) psi, rfl⟩

/-- Every positive closed-Hamiltonian shift is surjective. -/
theorem closedRightHamiltonianShift_surjective
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Surjective (T.closedRightHamiltonianShift lambda) :=
  T.closedRightHamiltonianShift_surjective_of_denseRange hlambda
    (T.closedRightHamiltonianShift_denseRange hlambda)

/-- Every positive closed-Hamiltonian shift is bijective. -/
theorem closedRightHamiltonianShift_bijective
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Bijective (T.closedRightHamiltonianShift lambda) :=
  ⟨T.closedRightHamiltonianShift_injective hlambda,
    T.closedRightHamiltonianShift_surjective hlambda⟩

/-- Closedness, dense domain, nonnegativity, and all positive-shift
bijections, packaged as the maximal-accretive output used below. -/
theorem closedRightHamiltonian_maximalAccretive_package
    (T : P.StronglyContinuousPhysicalSemigroup) :
    LinearPMap.IsClosed T.closedRightHamiltonian ∧
      Dense ((T.closedRightHamiltonian.domain : Set P.PhysicalHilbert)) ∧
      (∀ psi : T.closedRightHamiltonian.domain,
        0 ≤ ⟪T.closedRightHamiltonian psi,
          (psi : P.PhysicalHilbert)⟫_ℝ) ∧
      (∀ lambda : ℝ, 0 < lambda →
        Function.Bijective (T.closedRightHamiltonianShift lambda)) :=
  ⟨T.closedRightHamiltonian_isClosed,
    T.closedRightHamiltonian_dense_domain,
    T.closedRightHamiltonian_inner_nonneg,
    fun _ hlambda => T.closedRightHamiltonianShift_bijective hlambda⟩

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
