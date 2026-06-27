import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventQuadraticDerivative
import Mathlib.Analysis.Calculus.AbsolutelyMonotone
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Calculus
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

set_option maxHeartbeats 1200000

/-- Every composition power of the positive real excitation resolvent has a
nonnegative quadratic form. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent_pow_inner_self_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass)
    (n : ℕ) (y : P.VacuumOrthogonalHilbert) :
    0 ≤ inner ℝ
      (((G.vacuumOrthogonalRealResolvent T hP hSelf hlambda) ^ n) y) y := by
  let R := G.vacuumOrthogonalRealResolvent T hP hSelf hlambda
  induction n using Nat.strong_induction_on generalizing y with
  | h n ih =>
      rcases n with _ | n
      · simpa [R] using (real_inner_self_nonneg y)
      · rcases n with _ | k
        · simpa [R] using
            G.vacuumOrthogonalRealResolvent_inner_self_nonneg
              T hP hSelf hlambda y
        · have hk : k < Nat.succ (Nat.succ k) := by omega
          have hRsymm : ∀ u v : P.VacuumOrthogonalHilbert,
              inner ℝ (R u) v = inner ℝ u (R v) := by
            intro u v
            simpa [R] using
              G.vacuumOrthogonalRealResolvent_symmetric
                T hP hSelf hlambda u v
          have hpow :
              R ^ (Nat.succ (Nat.succ k)) = R * (R ^ k) * R := by
            rw [show Nat.succ (Nat.succ k) = (1 + k) + 1 by omega]
            rw [pow_add, pow_add]
            simp
          rw [hpow]
          change 0 ≤ inner ℝ (R ((R ^ k) (R y))) y
          rw [hRsymm]
          exact ih k hk (R y)

/-- The derivative of the `k`-th resolvent-power quadratic form is `k` times
the next resolvent-power quadratic form. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_pow_quadratic_hasDerivWithinAt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (k : ℕ) {lambda : ℝ} (hlambda : lambda < G.mass)
    (y : P.VacuumOrthogonalHilbert) :
    HasDerivWithinAt
      (fun mu => inner ℝ
        (((G.vacuumOrthogonalRealResolventOn T hP hSelf mu) ^ k) y) y)
      ((k : ℝ) * inner ℝ
        (((G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ (k + 1)) y) y)
      (Set.Iio G.mass) lambda := by
  have hpow :=
    G.vacuumOrthogonalRealResolventOn_pow_hasDerivWithinAt
      T hP hSelf k hlambda
  have hconstant :
      HasDerivWithinAt (fun _ : ℝ => y) 0 (Set.Iio G.mass) lambda :=
    hasDerivWithinAt_const lambda (Set.Iio G.mass) y
  have happly :
      HasDerivWithinAt
        (fun mu =>
          ((G.vacuumOrthogonalRealResolventOn T hP hSelf mu) ^ k) y)
        ((((k : ℝ) •
          (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ (k + 1))) y)
        (Set.Iio G.mass) lambda := by
    simpa using hpow.clm_apply hconstant
  have hinner := happly.inner ℝ hconstant
  simpa only [inner_zero_right, zero_add, smul_apply,
    real_inner_smul_left] using hinner

/-- Every scalar quadratic resolvent derivative within the open sub-mass
interval is the factorial multiple of the corresponding resolvent-power
quadratic form. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventQuadraticOn_iteratedDerivWithin
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (y : P.VacuumOrthogonalHilbert)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < G.mass) :
    iteratedDerivWithin n
        (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y)
        (Set.Iio G.mass) lambda =
      (n.factorial : ℝ) * inner ℝ
        (((G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ (n + 1)) y) y := by
  induction n generalizing lambda with
  | zero =>
      simp [vacuumOrthogonalRealResolventQuadraticOn]
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hcongr :
          derivWithin
              (iteratedDerivWithin n
                (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y)
                (Set.Iio G.mass))
              (Set.Iio G.mass) lambda =
            derivWithin
              (fun mu =>
                (n.factorial : ℝ) * inner ℝ
                  (((G.vacuumOrthogonalRealResolventOn T hP hSelf mu) ^
                    (n + 1)) y) y)
              (Set.Iio G.mass) lambda :=
        derivWithin_congr
          (fun mu hmu => ih (lambda := mu) hmu)
          (ih (lambda := lambda) hlambda)
      rw [hcongr]
      have hpower :=
        G.vacuumOrthogonalRealResolventOn_pow_quadratic_hasDerivWithinAt
          T hP hSelf (n + 1) hlambda y
      have hscaled :
          HasDerivWithinAt
            (fun mu =>
              (n.factorial : ℝ) * inner ℝ
                (((G.vacuumOrthogonalRealResolventOn T hP hSelf mu) ^
                  (n + 1)) y) y)
            ((n.factorial : ℝ) *
              (((n + 1 : ℕ) : ℝ) * inner ℝ
                (((G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^
                  (n + 2)) y) y))
            (Set.Iio G.mass) lambda := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          hpower.const_mul (n.factorial : ℝ)
      rw [hscaled.derivWithin (isOpen_Iio.uniqueDiffOn lambda hlambda)]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      ring

/-- Ordinary all-order scalar derivative formula below the transferred mass. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventQuadraticOn_iteratedDeriv
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (y : P.VacuumOrthogonalHilbert)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < G.mass) :
    iteratedDeriv n
        (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y) lambda =
      (n.factorial : ℝ) * inner ℝ
        (((G.vacuumOrthogonalRealResolvent T hP hSelf hlambda) ^ (n + 1)) y) y := by
  calc
    iteratedDeriv n
        (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y) lambda =
      iteratedDerivWithin n
        (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y)
        (Set.Iio G.mass) lambda :=
      (iteratedDerivWithin_of_isOpen
        (n := n)
        (f := G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y)
        isOpen_Iio hlambda).symm
    _ = (n.factorial : ℝ) * inner ℝ
        (((G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ (n + 1)) y) y :=
      G.vacuumOrthogonalRealResolventQuadraticOn_iteratedDerivWithin
        T hP hSelf y n hlambda
    _ = (n.factorial : ℝ) * inner ℝ
        (((G.vacuumOrthogonalRealResolvent T hP hSelf hlambda) ^ (n + 1)) y) y := by
      rw [G.vacuumOrthogonalRealResolventOn_of_lt T hP hSelf hlambda]

/-- The scalar quadratic resolvent is smooth on the full open real sub-mass
interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventQuadraticOn_contDiffOn_infty
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (y : P.VacuumOrthogonalHilbert) :
    ContDiffOn ℝ ∞
      (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y)
      (Set.Iio G.mass) := by
  have hR :=
    G.vacuumOrthogonalRealResolventOn_contDiffOn_infty T hP hSelf
  have hy : ContDiffOn ℝ ∞ (fun _ : ℝ => y) (Set.Iio G.mass) :=
    contDiffOn_const
  have happly := hR.clm_apply hy
  simpa only [vacuumOrthogonalRealResolventQuadraticOn] using
    happly.inner ℝ hy

/-- All scalar quadratic resolvent derivatives are nonnegative below the
transferred mass. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventQuadraticOn_iteratedDerivWithin_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (y : P.VacuumOrthogonalHilbert)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < G.mass) :
    0 ≤ iteratedDerivWithin n
      (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y)
      (Set.Iio G.mass) lambda := by
  rw [G.vacuumOrthogonalRealResolventQuadraticOn_iteratedDerivWithin
    T hP hSelf y n hlambda]
  exact mul_nonneg (Nat.cast_nonneg n.factorial)
    (G.vacuumOrthogonalRealResolvent_pow_inner_self_nonneg
      T hP hSelf hlambda (n + 1) y)

/-- The positive scalar resolvent is absolutely monotone on the entire open
sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventQuadraticOn_absolutelyMonotoneOn
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (y : P.VacuumOrthogonalHilbert) :
    AbsolutelyMonotoneOn
      (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y)
      (Set.Iio G.mass) := by
  rw [AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg
    isOpen_Iio.uniqueDiffOn]
  refine ⟨G.vacuumOrthogonalRealResolventQuadraticOn_contDiffOn_infty
    T hP hSelf y, ?_⟩
  intro n lambda hlambda
  exact G.vacuumOrthogonalRealResolventQuadraticOn_iteratedDerivWithin_nonneg
    T hP hSelf y n hlambda

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
