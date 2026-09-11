import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedMassGronwallNormSqDecay
import Mathlib.Tactic

/-!
# Generator-domain norm decay from the derived physical Yang--Mills mass

The preceding Gronwall layer proves the squared-norm estimate

`‖T_t ψ‖² ≤ ‖ψ‖² * exp (-2 * physicalYangMillsMass * t)`

for vacuum-orthogonal vectors in the canonical right-generator domain.

This file takes the nonnegative square root algebraically.  Mathlib's positivity
of the real exponential and nonnegativity of norms are sufficient; no positivity
assumption on `physicalYangMillsMass` is added.  The result is the sharp norm
estimate

`‖T_t ψ‖ ≤ ‖ψ‖ * exp (-physicalYangMillsMass * t)`.

This is the convenient form for the subsequent dense-domain/closed-subspace
extension to the full vacuum-orthogonal physical Hilbert sector.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Real
open scoped InnerProductSpace NNReal

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The derived physical Yang--Mills mass controls the physical semigroup norm
exponentially on vacuum-orthogonal vectors in the canonical right-generator
domain.  This is the nonnegative square-root form of the Gronwall squared-norm
estimate and introduces no additional physical hypothesis. -/
theorem physicalOperator_norm_le_exp_neg_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (t : NNReal) (psi : T.rightGeneratorDomain)
    (horthogonal :
      inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    ‖T.toPhysicalSemigroup.operator t
        (psi : P.PhysicalHilbert)‖ ≤
      ‖(psi : P.PhysicalHilbert)‖ *
        Real.exp ((-T.physicalYangMillsMass) * (t : ℝ)) := by
  have hsq :=
    T.physicalOperator_norm_sq_le_exp_neg_two_physicalYangMillsMass
      hP t psi horthogonal
  have hexp :
      Real.exp ((-2 * T.physicalYangMillsMass) * (t : ℝ)) =
        Real.exp ((-T.physicalYangMillsMass) * (t : ℝ)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hsq
  have hleft :
      0 ≤ ‖T.toPhysicalSemigroup.operator t
        (psi : P.PhysicalHilbert)‖ := norm_nonneg _
  have hright :
      0 ≤ ‖(psi : P.PhysicalHilbert)‖ *
        Real.exp ((-T.physicalYangMillsMass) * (t : ℝ)) :=
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  nlinarith [hsq]

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
