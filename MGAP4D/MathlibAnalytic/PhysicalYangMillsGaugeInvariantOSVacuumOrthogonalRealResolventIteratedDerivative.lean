import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventSmooth
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
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

/-- The `k`-th composition power of the excitation resolvent has derivative
`k • R^(k+1)` within the open real sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_pow_hasDerivWithinAt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (k : ℕ) {lambda : ℝ} (hlambda : lambda < G.mass) :
    HasDerivWithinAt
      (fun mu =>
        (G.vacuumOrthogonalRealResolventOn T hP hSelf mu) ^ k)
      ((k : ℝ) •
        (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ (k + 1))
      (Set.Iio G.mass) lambda := by
  induction k with
  | zero =>
      simpa only [pow_zero, Nat.cast_zero, zero_smul] using
        (hasDerivWithinAt_const lambda (Set.Iio G.mass)
          (1 : P.VacuumOrthogonalHilbert →L[ℝ]
            P.VacuumOrthogonalHilbert))
  | succ k ih =>
      have hR :
          HasDerivWithinAt
            (G.vacuumOrthogonalRealResolventOn T hP hSelf)
            ((G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ 2)
            (Set.Iio G.mass) lambda := by
        simpa [pow_two, ContinuousLinearMap.mul_def,
          G.vacuumOrthogonalRealResolventOn_of_lt T hP hSelf hlambda] using
          G.vacuumOrthogonalRealResolventOn_hasDerivWithinAt
            T hP hSelf hlambda
      have hmul := HasDerivWithinAt.mul
        (𝕜 := ℝ)
        (𝔸 := P.VacuumOrthogonalHilbert →L[ℝ]
          P.VacuumOrthogonalHilbert)
        ih hR
      convert hmul using 1
      · funext mu
        simp [pow_succ]
      · let Rlambda :=
          G.vacuumOrthogonalRealResolventOn T hP hSelf lambda
        change
          ((k : ℝ) • Rlambda ^ (k + 1)) * Rlambda +
              Rlambda ^ k * Rlambda ^ 2 =
            ((Nat.succ k : ℕ) : ℝ) •
              Rlambda ^ (Nat.succ k + 1)
        rw [smul_mul_assoc]
        have hfirst : Rlambda ^ (k + 1) * Rlambda = Rlambda ^ (k + 2) := by
          simpa [Nat.add_assoc] using (pow_succ Rlambda (k + 1)).symm
        have hsecond : Rlambda ^ k * Rlambda ^ 2 = Rlambda ^ (k + 2) := by
          simpa using (pow_add Rlambda k 2).symm
        rw [hfirst, hsecond]
        simp [Nat.cast_succ, Nat.succ_eq_add_one, add_smul, Nat.add_assoc]

/-- Every iterated derivative within the open real sub-mass interval is the
factorial multiple of the corresponding composition power. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_iteratedDerivWithin
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < G.mass) :
    iteratedDerivWithin n
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (Set.Iio G.mass) lambda =
      (n.factorial : ℝ) •
        (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ (n + 1) := by
  induction n generalizing lambda with
  | zero => simp
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hcongr :
          derivWithin
              (iteratedDerivWithin n
                (G.vacuumOrthogonalRealResolventOn T hP hSelf)
                (Set.Iio G.mass))
              (Set.Iio G.mass) lambda =
            derivWithin
              (fun mu =>
                (n.factorial : ℝ) •
                  (G.vacuumOrthogonalRealResolventOn T hP hSelf mu) ^ (n + 1))
              (Set.Iio G.mass) lambda :=
        derivWithin_congr
          (fun mu hmu => ih (lambda := mu) hmu)
          (ih (lambda := lambda) hlambda)
      rw [hcongr]
      have hpow :=
        G.vacuumOrthogonalRealResolventOn_pow_hasDerivWithinAt
          T hP hSelf (n + 1) hlambda
      have hscaled :
          HasDerivWithinAt
            (fun mu =>
              (n.factorial : ℝ) •
                (G.vacuumOrthogonalRealResolventOn T hP hSelf mu) ^ (n + 1))
            ((n.factorial : ℝ) •
              (((n + 1 : ℕ) : ℝ) •
                (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^
                  (n + 2)))
            (Set.Iio G.mass) lambda := by
        simpa only [Pi.smul_apply] using
          (HasDerivWithinAt.const_smul
            (𝕜 := ℝ) (R := ℝ)
            (F := P.VacuumOrthogonalHilbert →L[ℝ]
              P.VacuumOrthogonalHilbert)
            (n.factorial : ℝ) hpow)
      have hscaledDeriv :
          derivWithin
              (fun mu =>
                (n.factorial : ℝ) •
                  (G.vacuumOrthogonalRealResolventOn T hP hSelf mu) ^ (n + 1))
              (Set.Iio G.mass) lambda =
            (n.factorial : ℝ) •
              (((n + 1 : ℕ) : ℝ) •
                (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^
                  (n + 2)) := by
        exact HasDerivWithinAt.derivWithin
          (𝕜 := ℝ) hscaled
          (isOpen_Iio.uniqueDiffOn lambda hlambda)
      rw [hscaledDeriv]
      simp [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
        smul_smul, Nat.succ_eq_add_one, mul_comm, mul_left_comm,
        mul_assoc, Nat.add_assoc]

/-- Explicit ordinary all-order derivative formula below the transferred mass:
`R^(n)(lambda) = n! • R(lambda)^(n+1)`. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_iteratedDeriv
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < G.mass) :
    iteratedDeriv n
        (G.vacuumOrthogonalRealResolventOn T hP hSelf) lambda =
      (n.factorial : ℝ) •
        (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda) ^ (n + 1) := by
  calc
    iteratedDeriv n
        (G.vacuumOrthogonalRealResolventOn T hP hSelf) lambda =
      iteratedDerivWithin n
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (Set.Iio G.mass) lambda :=
      (iteratedDerivWithin_of_isOpen
        (n := n)
        (f := G.vacuumOrthogonalRealResolventOn T hP hSelf)
        isOpen_Iio hlambda).symm
    _ = (n.factorial : ℝ) •
        (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda) ^ (n + 1) :=
      G.vacuumOrthogonalRealResolventOn_iteratedDerivWithin
        T hP hSelf n hlambda
    _ = (n.factorial : ℝ) •
        (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda) ^ (n + 1) := by
      rw [G.vacuumOrthogonalRealResolventOn_of_lt T hP hSelf hlambda]

/-- Smoothness and all-order derivative package for the excitation resolvent. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventSmooth_package
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    ContDiffOn ℝ ∞
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (Set.Iio G.mass) ∧
      ∀ (n : ℕ) {lambda : ℝ} (hlambda : lambda < G.mass),
        iteratedDeriv n
            (G.vacuumOrthogonalRealResolventOn T hP hSelf) lambda =
          (n.factorial : ℝ) •
            (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda) ^ (n + 1) :=
  ⟨G.vacuumOrthogonalRealResolventOn_contDiffOn_infty T hP hSelf,
    fun n {lambda} hlambda =>
      G.vacuumOrthogonalRealResolventOn_iteratedDeriv
        T hP hSelf n (lambda := lambda) hlambda⟩

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
