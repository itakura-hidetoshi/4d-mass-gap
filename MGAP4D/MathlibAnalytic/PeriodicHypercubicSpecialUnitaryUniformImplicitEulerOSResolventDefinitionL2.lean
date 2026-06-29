import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryUniformImplicitEulerOSGapL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSRealResolventL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData

variable {sideLength : ℕ → ℕ} {sideLength_pos : ∀ n, 0 < sideLength n}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {beta_nonneg : ∀ n, 0 ≤ beta n}
variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {W : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : W.OSPreHilbertData}
variable {T : P.StronglyContinuousPhysicalSemigroup}

end PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData

end

end MathlibAnalytic
end MGAP4D
