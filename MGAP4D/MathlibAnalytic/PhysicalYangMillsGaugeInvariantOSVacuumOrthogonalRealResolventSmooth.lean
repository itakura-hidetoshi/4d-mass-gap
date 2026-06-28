import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

set_option maxHeartbeats 800000

/-- The vacuum-orthogonal real resolvent is `Cⁿ` in operator norm for every
finite order on the open real sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_contDiffOn_nat
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (n : ℕ) :
    ContDiffOn ℝ n
      (G.vacuumOrthogonalRealResolventOn T hP hSelf)
      (Set.Iio G.mass) := by
  induction n with
  | zero =>
      change ContDiffOn ℝ 0
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (Set.Iio G.mass)
      exact (contDiffOn_zero (𝕜 := ℝ)).2
        (G.vacuumOrthogonalRealResolventOn_continuousOn T hP hSelf)
  | succ n ih =>
      apply (contDiffOn_succ_iff_deriv_of_isOpen
        (n := (n : ℕ∞ω)) isOpen_Iio).2
      refine ⟨G.vacuumOrthogonalRealResolventOn_differentiableOn
        T hP hSelf, ?_, ?_⟩
      · simp
      · have hsquare :
            ContDiffOn ℝ n
              (fun lambda =>
                (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda).comp
                  (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda))
              (Set.Iio G.mass) :=
          ih.clm_comp ih
        apply hsquare.congr
        intro lambda hlambda
        calc
          deriv (G.vacuumOrthogonalRealResolventOn T hP hSelf) lambda =
              (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
                (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda) :=
            G.vacuumOrthogonalRealResolventOn_deriv T hP hSelf hlambda
          _ = (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda).comp
                (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) := by
            rw [G.vacuumOrthogonalRealResolventOn_of_lt T hP hSelf hlambda]

/-- The vacuum-orthogonal real resolvent is smooth in the operator-norm
topology throughout the open real sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_contDiffOn_infty
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    ContDiffOn ℝ ∞
      (G.vacuumOrthogonalRealResolventOn T hP hSelf)
      (Set.Iio G.mass) :=
  contDiffOn_infty.2 fun n =>
    G.vacuumOrthogonalRealResolventOn_contDiffOn_nat T hP hSelf n

/-- Finite-order and smooth regularity package for the excitation resolvent. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventSmoothness_package
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    ContDiffOn ℝ ∞
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (Set.Iio G.mass) ∧
      ∀ n : ℕ,
        ContDiffOn ℝ n
          (G.vacuumOrthogonalRealResolventOn T hP hSelf)
          (Set.Iio G.mass) :=
  ⟨G.vacuumOrthogonalRealResolventOn_contDiffOn_infty T hP hSelf,
    fun n =>
      G.vacuumOrthogonalRealResolventOn_contDiffOn_nat T hP hSelf n⟩

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
