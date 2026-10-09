import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalPosteriorOscillation
import Mathlib.Tactic

/-!
# P4-Q2: constructed original-Wilson half-density / physical-mean link budgets

PR #5325 establishes that TRUE original Wilson posterior two-copy
resampling losses for the uncentered fine-right Krylov family are
controlled by certified physical right-link oscillations.

This file CONSTRUCTS those oscillation coefficients from the actual
frozen-Wilson receiver, without an abstract coefficient hypothesis.

The ORIGINAL signed physical joint receiver is exactly W_beta * M_beta,F:
 W_beta(A,B) = lambda_beta^{-1} Omega_beta(B)/sqrt(rho_beta(A,B)),
 M_beta,F(A,B) = (S_beta F)(B) / Omega_beta(B).
Both are preexisting actual bounded-continuous functions. In particular,
the continuous vacuum and physical normalization are not discarded.

For a true right-link update e and gauge g, construct the bounded
continuous difference on the compact (joint x gauge) carrier:
  delta_e G(z,g) = G(z) - G(z.1, update z.2 e g).

Use the honest BCF sup norm osc_e(G) = ||delta_e G||.
The exact Leibniz identity yields a *certified*, link-resolved,
fully constructed physical bound

  |(W*M)(z)-(W*M)(z[e<-g])|
    <= ||W|| osc_e(M) + ||M|| osc_e(W).

Hence the actual UN-CENTERED physical right-Krylov Gram obeys

  a*G_right*a <= 1/2 sum_e
      (||W_beta|| osc_e(M_beta,F) +
       ||M_beta,F|| osc_e(W_beta))^2.

No |Links(H)| worst-case step or mode-count multiplier occurs, and
there is no invented posterior or independent measure. The separate
half-density and physical mean contributions are exposed for genuine
further SU(2) Wilson local-plaquette/vacuum-response estimates.

These norms can still depend on the finite volume; neither a
volume-uniform coefficient bound nor continuum mass gap is proved.
No Dobrushin reconstruction, sorry, admit, or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4HalfMeanTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4HalfMeanCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4HalfMeanSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4HalfMeanMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4HalfMeanBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4HalfMeanLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The true right-link difference of a bounded original-Wilson joint
observable is a bounded continuous function of the entire context AND
the candidate new SU(N) link value. This is not a finite-support
hypothesis or a supremum over a fabricated law. -/
noncomputable def physicalJointBCFRightLinkDifference
    (H N : ℕ)
    (A : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
       PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    BoundedContinuousFunction
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ := by
  classical
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let Pair := Cfg × Cfg
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  have hUpdate :
      Continuous (fun t : Pair × Gauge =>
        (t.1.1, Function.update t.1.2 e t.2)) := by
    refine (continuous_fst.comp continuous_fst).prodMk ?_
    apply continuous_pi
    intro i
    by_cases hi : i = e
    · subst i
      simpa only [Function.update_self] using
        (continuous_snd : Continuous (fun t : Pair × Gauge => t.2))
    · have hOther : Continuous (fun t : Pair × Gauge => t.1.2 i) :=
        (continuous_apply i).comp (continuous_snd.comp continuous_fst)
      simpa only [Function.update_of_ne hi] using hOther
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun t : Pair × Gauge =>
        A t.1 - A (t.1.1, Function.update t.1.2 e t.2),
      (A.continuous.comp continuous_fst).sub (A.continuous.comp hUpdate)⟩

@[simp] theorem physicalJointBCFRightLinkDifference_apply
    (H N : ℕ)
    (A : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
       PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    physicalJointBCFRightLinkDifference H N A e (z, g) =
      A z - A (z.1, Function.update z.2 e g) := by
  rfl

/-- The link coefficient is the genuine BCF sup norm of the
pointwise original-Wilson right-link update difference, therefore
every actual update is bounded by it without a new hypothesis. -/
theorem physicalJointBCFRightLinkDifference_abs_le_norm
    (H N : ℕ)
    (A : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
       PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |A z - A (z.1, Function.update z.2 e g)| ≤
      ‖physicalJointBCFRightLinkDifference H N A e‖ := by
  simpa only [physicalJointBCFRightLinkDifference_apply, Real.norm_eq_abs] using
    (physicalJointBCFRightLinkDifference H N A e).norm_coe_le_norm (z, g)

/-- Exact right-link Leibniz splitting, then the honest SUP NORM bound
of the TWO actual separate factors. Both physically meaningful
oscillations remain link-dependent instead of replacing them by
one global worst-case link bound. -/
theorem physicalJointBCF_product_rightLinkVariation_le_factorNorms
    (H N : ℕ)
    (A B : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
       PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |(A * B) z - (A * B) (z.1, Function.update z.2 e g)| ≤
      ‖A‖ * ‖physicalJointBCFRightLinkDifference H N B e‖ +
      ‖B‖ * ‖physicalJointBCFRightLinkDifference H N A e‖ := by
  let z' := (z.1, Function.update z.2 e g)
  have hA : |A z| ≤ ‖A‖ := by
    simpa only [Real.norm_eq_abs] using A.norm_coe_le_norm z
  have hB : |B z'| ≤ ‖B‖ := by
    simpa only [Real.norm_eq_abs] using B.norm_coe_le_norm z'
  have hDeltaA : |A z - A z'| ≤
      ‖physicalJointBCFRightLinkDifference H N A e‖ :=
    physicalJointBCFRightLinkDifference_abs_le_norm H N A e z g
  have hDeltaB : |B z - B z'| ≤
      ‖physicalJointBCFRightLinkDifference H N B e‖ :=
    physicalJointBCFRightLinkDifference_abs_le_norm H N B e z g
  have hFirst :
      |A z| * |B z - B z'| ≤
      ‖A‖ * ‖physicalJointBCFRightLinkDifference H N B e‖ := by
    calc
      |A z| * |B z - B z'| ≤ ‖A‖ * |B z - B z'| :=
        mul_le_mul_of_nonneg_right hA (abs_nonneg _)
      _ ≤ ‖A‖ * ‖physicalJointBCFRightLinkDifference H N B e‖ :=
        mul_le_mul_of_nonneg_left hDeltaB (norm_nonneg _)
  have hSecond :
      |A z - A z'| * |B z'| ≤
      ‖B‖ * ‖physicalJointBCFRightLinkDifference H N A e‖ := by
    calc
      |A z - A z'| * |B z'| ≤
          |A z - A z'| * ‖B‖ :=
        mul_le_mul_of_nonneg_left hB (abs_nonneg _)
      _ ≤ ‖physicalJointBCFRightLinkDifference H N A e‖ * ‖B‖ :=
        mul_le_mul_of_nonneg_right hDeltaA (norm_nonneg _)
      _ = ‖B‖ * ‖physicalJointBCFRightLinkDifference H N A e‖ :=
        mul_comm _ _
  have hLeibniz := jointBCF_mul_sub_right_update A B e z g
  change (A * B) z - (A * B) z' =
      A z * (B z - B z') + (A z - A z') * B z' at hLeibniz
  calc
    |(A * B) z - (A * B) z'| =
        |A z * (B z - B z') + (A z - A z') * B z'| :=
      congrArg abs hLeibniz
    _ ≤ |A z * (B z - B z')| + |(A z - A z') * B z'| :=
      abs_add_le _ _
    _ = |A z| * |B z - B z'| + |A z - A z'| * |B z'| := by
      simp only [abs_mul]
    _ ≤ ‖A‖ * ‖physicalJointBCFRightLinkDifference H N B e‖ +
        ‖B‖ * ‖physicalJointBCFRightLinkDifference H N A e‖ :=
      add_le_add hFirst hSecond

/-- The original fine-right actual physical normalized-transfer
receiver on the FROZEN positive-beta Wilson joint law. It is the
pre-existing right-only mean factor of the genuine signed receiver. -/
noncomputable def fineRightKrylovOriginalVacuumMeanJointBCF
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
        (halfExtent (n + 1)) 2 ×
       PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
        (halfExtent (n + 1)) 2) ℝ :=
  normalizedPhysicalOneSlabVacuumMeanJointBCF
    (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
    (beta n) (hbeta n)
    (∑ j : Fin (r + 1), a j •
      physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ))

/-- The certified link-by-link PHYSICAL oscillation bound separating the
genuine frozen-Wilson half-density/output drift from the genuine
frozen transfer mean of the fine-right Krylov input. Neither input
is replaced by an arbitrary fitted local profile. -/
noncomputable def fineRightKrylovOriginalHalfDensityMeanLinkBudget
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ :=
  let H := halfExtent (n + 1)
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let M := fineRightKrylovOriginalVacuumMeanJointBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  ‖W‖ * ‖physicalJointBCFRightLinkDifference H 2 M e‖ +
    ‖M‖ * ‖physicalJointBCFRightLinkDifference H 2 W e‖

theorem fineRightKrylovOriginalHalfDensityMeanLinkBudget_nonneg
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) :
    0 ≤ fineRightKrylovOriginalHalfDensityMeanLinkBudget
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a e := by
  unfold fineRightKrylovOriginalHalfDensityMeanLinkBudget
  exact add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- No extra pointwise variation assumptions: the actual original
SU(2) Wilson half-density and physical vacuum-mean receiver themselves
construct an upper bound for every genuine right-link update. -/
theorem fineRightKrylovOriginalPhysicalJointObservable_linkVariation_le_halfDensityMean
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
      (halfExtent (n + 1)) 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
      (halfExtent (n + 1)) 2)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    |fineRightKrylovOriginalPhysicalJointObservable
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a z -
      fineRightKrylovOriginalPhysicalJointObservable
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
        (z.1, Function.update z.2 e g)| ≤
      fineRightKrylovOriginalHalfDensityMeanLinkBudget
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a e := by
  let H := halfExtent (n + 1)
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let M := fineRightKrylovOriginalVacuumMeanJointBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hProduct :
      fineRightKrylovOriginalPhysicalJointObservable
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a = W * M := rfl
  change |(W * M) z - (W * M) (z.1, Function.update z.2 e g)| ≤
      ‖W‖ * ‖physicalJointBCFRightLinkDifference H 2 M e‖ +
      ‖M‖ * ‖physicalJointBCFRightLinkDifference H 2 W e‖
  exact physicalJointBCF_product_rightLinkVariation_le_factorNorms H 2 W M e z g

/-- The TRUE ORIGINAL UN-CENTERED Yang--Mills fine-right Krylov Gram
has a CONSTRUCTED linkwise two-factor physical Rayleigh bound, with
full Wilson posterior, signed joint receiver, exact half-density and
physical mean, and independent frozen/fine betas. No hypothetical
locality coefficient is supplied to the theorem. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_constructedHalfDensityMeanLinkBudget
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      (1 / 2 : ℝ) *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
          (fineRightKrylovOriginalHalfDensityMeanLinkBudget
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r a e) ^ 2 := by
  apply fineRightKrylovPairHaarResidualGram_rayleigh_le_originalLinkOscillation
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a
    (fineRightKrylovOriginalHalfDensityMeanLinkBudget
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a)
  intro e z g
  exact fineRightKrylovOriginalPhysicalJointObservable_linkVariation_le_halfDensityMean
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a e z g

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
