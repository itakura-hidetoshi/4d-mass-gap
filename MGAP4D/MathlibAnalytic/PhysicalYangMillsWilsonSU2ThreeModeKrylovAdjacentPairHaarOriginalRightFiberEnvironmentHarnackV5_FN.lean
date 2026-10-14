import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumKernelHarnack
import Mathlib.Tactic

/-!
# P4-Q2-FN: sharp actual Wilson right-environment one-link factor (14 beta)

The exact one-slab Wilson kernel factorizes into:
* the spatial half-Boltzmann weight on its left/right boundaries; and
* the actual product of temporal crossing Wilson relative-link kernels.

When varying a selected RIGHT spatial link, the part independent of the
corresponding left-link gauge variable is

  r_{beta,B,e}(g) = exp (-beta/2 * spatialAction(B[e <- g]))
                     * Omega_beta(B[e <- g]),

with the actual continuous positive physical Perron vacuum Omega_beta.

The genuine spatial Wilson action changes by at most 12, costing 6 beta
for the half weight; the verified continuous vacuum changes by at most
exp(8 beta). Hence

  r(g) <= exp(14 beta) * r(h),  0 < r(g),

independently of spatial volume H, physical link e, and original physical
boundary B. This improves the coarse combined exp(16 beta) estimate
for the left-link-INDEPENDENT environment factor. It is a genuine Wilson
factor with the true canonical vacuum, not a surrogate or independence
assumption.

The remaining analytic tasks are exact crossing-kernel factorization
at the selected link and Haar left-translation averaging to obtain an
all-link physical RMS frame floor. No such floor, summability, or continuum
mass-gap theorem is claimed here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 650000

/-- Actual spatial-half-weight times positive continuous physical vacuum,
with the selected right physical link updated to g. Unlike the full
one-slab joint weight, this environment term has no dependence on the
corresponding LEFT temporal-crossing link value. -/
noncomputable def p4Q2FN_originalWilsonRightFiberEnvironmentWeight
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
    H N beta (Function.update right e g) *
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H N hN beta hbeta (Function.update right e g)

/-- The exact local right-environment factor is pointwise strictly positive;
the physical Wilson vacuum is never evaluated through an arbitrary L²
representative at an exceptional point. -/
theorem p4Q2FN_originalWilsonRightFiberEnvironmentWeight_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 < p4Q2FN_originalWilsonRightFiberEnvironmentWeight
      H N hN beta hbeta right e g := by
  unfold p4Q2FN_originalWilsonRightFiberEnvironmentWeight
  exact mul_pos
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos
      H N beta (Function.update right e g))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta (Function.update right e g))

/-- The genuine spatial WILSON HALF WEIGHT costs at most exp(6 beta)
under one arbitrary physical right-link replacement, uniformly in H. -/
theorem p4Q2FN_originalWilsonRightSpatialHalfWeight_le_exp_six
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
        H N beta (Function.update right e g) ≤
      Real.exp (6 * beta) *
        periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
          H N beta (Function.update right e h) := by
  let Bg := Function.update right e g
  let Bh := Function.update right e h
  let A := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
  have hAction :
      |A Bg - A Bh| ≤ 12 := by
    simpa [A, Bg, Bh,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuousVacuumReplaceLink_sub_abs_le_twelve
        H N hN right e g h
  have hDiff : A Bh - A Bg ≤ 12 := by
    have hLower : -12 ≤ A Bg - A Bh := (abs_le.mp hAction).1
    linarith
  have hHalfBeta : 0 ≤ beta / 2 := by positivity
  have hMult :
      (beta / 2) * (A Bh - A Bg) ≤ (beta / 2) * 12 :=
    mul_le_mul_of_nonneg_left hDiff hHalfBeta
  have hExponent :
      -(beta / 2) * A Bg ≤ (6 * beta) + (-(beta / 2) * A Bh) := by
    nlinarith [hMult]
  change Real.exp (-(beta / 2) * A Bg) ≤
    Real.exp (6 * beta) * Real.exp (-(beta / 2) * A Bh)
  calc
    Real.exp (-(beta / 2) * A Bg) ≤
        Real.exp ((6 * beta) + (-(beta / 2) * A Bh)) :=
      Real.exp_le_exp.mpr hExponent
    _ = Real.exp (6 * beta) * Real.exp (-(beta / 2) * A Bh) := by
      rw [Real.exp_add]

/-- The original Wilson physical right-environment link weight has a
volume-uniform pairwise Harnack ratio exp(14 beta)=exp(6 beta)*exp(8 beta).
Its source-independent right environment is not replaced by Haar. -/
theorem p4Q2FN_originalWilsonRightFiberEnvironmentWeight_le_exp_fourteen
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    p4Q2FN_originalWilsonRightFiberEnvironmentWeight
        H N hN beta hbeta right e g ≤
      Real.exp (14 * beta) *
        p4Q2FN_originalWilsonRightFiberEnvironmentWeight
          H N hN beta hbeta right e h := by
  let Bg := Function.update right e g
  let Bh := Function.update right e h
  let S := periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta
  let Omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H N hN beta hbeta
  have hs : S Bg ≤ Real.exp (6 * beta) * S Bh :=
    p4Q2FN_originalWilsonRightSpatialHalfWeight_le_exp_six
      H N hN beta hbeta right e g h
  have ho : Omega Bg ≤ Real.exp (8 * beta) * Omega Bh := by
    simpa [Omega, Bg, Bh] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_update_right_le_exp_eight_mul_update_right
        H N hN beta hbeta right e g h
  have hOg : 0 ≤ Omega Bg :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta Bg).le
  have hSh : 0 ≤ S Bh :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos
      H N beta Bh).le
  have hE6 : 0 ≤ Real.exp (6 * beta) := (Real.exp_pos _).le
  have hProductExp :
      Real.exp (6 * beta) * Real.exp (8 * beta) =
        Real.exp (14 * beta) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change S Bg * Omega Bg ≤ Real.exp (14 * beta) * (S Bh * Omega Bh)
  calc
    S Bg * Omega Bg ≤
        (Real.exp (6 * beta) * S Bh) * Omega Bg :=
      mul_le_mul_of_nonneg_right hs hOg
    _ ≤
        (Real.exp (6 * beta) * S Bh) *
          (Real.exp (8 * beta) * Omega Bh) :=
      mul_le_mul_of_nonneg_left ho (mul_nonneg hE6 hSh)
    _ =
        (Real.exp (6 * beta) * Real.exp (8 * beta)) *
          (S Bh * Omega Bh) := by ring
    _ = Real.exp (14 * beta) * (S Bh * Omega Bh) := by
      rw [hProductExp]

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2FN_originalWilsonRightFiberEnvironmentWeight_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2FN_originalWilsonRightSpatialHalfWeight_le_exp_six
#print axioms MGAP4D.MathlibAnalytic.p4Q2FN_originalWilsonRightFiberEnvironmentWeight_le_exp_fourteen
