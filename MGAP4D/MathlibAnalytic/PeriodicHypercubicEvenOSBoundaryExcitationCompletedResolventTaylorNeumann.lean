import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventAnalyticHierarchy
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct BigOperators

noncomputable section

/-- A ring inverse of a unit is also a left inverse. -/
theorem ringInverse_mul_eq_one_of_isUnit
    {R : Type*}
    [Ring R]
    (x : R)
    (hx : IsUnit x) :
    Ring.inverse x * x = 1 := by
  rw [ringInverse_eq_unit_inv x hx]
  simpa only [hx.unit_spec] using hx.unit.inv_mul

/-- Scalar powers followed by one more algebra multiplication are the
Taylor coefficients that occur in a resolvent Neumann expansion. -/
theorem smul_pow_mul_eq_smul_pow_succ
    {R : Type*}
    [Ring R]
    [Algebra ℝ R]
    (h : ℝ)
    (x : R)
    (n : ℕ) :
    (h • x) ^ n * x = h ^ n • x ^ (n + 1) := by
  rw [smul_pow, Algebra.smul_mul_assoc, pow_succ]

/-- Generic resolvent factorization around a unit base point. If
`A = G - lambda • 1`, `R = A⁻¹`, and `‖h • R‖ < 1`, then

`(G - (lambda + h) • 1)⁻¹ = (1 - h • R)⁻¹ R`.

The proof uses only inverse uniqueness and never unfolds a proof-dependent
unit. -/
theorem ringInverse_sub_add_smul_one_factor
    {R : Type*}
    [NormedRing R]
    [HasSummableGeomSeries R]
    [NormedAlgebra ℝ R]
    (G : R)
    (lambda h : ℝ)
    (hunit : IsUnit (G - lambda • (1 : R)))
    (hsmall :
      ‖h • Ring.inverse (G - lambda • (1 : R))‖ < 1) :
    Ring.inverse (G - (lambda + h) • (1 : R)) =
      Ring.inverse
          (1 - h • Ring.inverse (G - lambda • (1 : R))) *
        Ring.inverse (G - lambda • (1 : R)) := by
  let A : R := G - lambda • (1 : R)
  let res : R := Ring.inverse A
  let t : R := h • res
  have hAunit : IsUnit A := by
    simpa only [A] using hunit
  have hAr : A * res = 1 := by
    simpa only [res] using mul_ringInverse_eq_one_of_isUnit A hAunit
  have hrA : res * A = 1 := by
    simpa only [res] using ringInverse_mul_eq_one_of_isUnit A hAunit
  have htunit : IsUnit (1 - t) := by
    exact (Units.oneSub t (by simpa only [t, res, A] using hsmall)).isUnit
  have hfactor :
      A * (1 - t) = G - (lambda + h) • (1 : R) := by
    calc
      A * (1 - t) = A - A * t := by rw [mul_sub, mul_one]
      _ = A - h • (A * res) := by
        change A - A * (h • res) = A - h • (A * res)
        rw [Algebra.mul_smul_comm]
      _ = A - h • (1 : R) := by rw [hAr]
      _ = G - (lambda + h) • (1 : R) := by
        dsimp [A]
        rw [add_smul]
        abel
  have hshiftUnit : IsUnit (G - (lambda + h) • (1 : R)) := by
    rw [← hfactor]
    exact hAunit.mul htunit
  have hcandidateLeft :
      (Ring.inverse (1 - t) * res) *
          (G - (lambda + h) • (1 : R)) = 1 := by
    rw [← hfactor]
    calc
      (Ring.inverse (1 - t) * res) * (A * (1 - t)) =
          Ring.inverse (1 - t) * (res * A) * (1 - t) := by
        simp only [mul_assoc]
      _ = Ring.inverse (1 - t) * (1 - t) := by rw [hrA, mul_one]
      _ = 1 := ringInverse_mul_eq_one_of_isUnit (1 - t) htunit
  have hringRight :
      (G - (lambda + h) • (1 : R)) *
          Ring.inverse (G - (lambda + h) • (1 : R)) = 1 :=
    mul_ringInverse_eq_one_of_isUnit
      (G - (lambda + h) • (1 : R)) hshiftUnit
  have huniq := left_inv_eq_right_inv hcandidateLeft hringRight
  simpa only [t, res, A] using huniq.symm

/-- Exact finite Taylor-Neumann expansion with algebraic remainder. For every
`n`, the shifted resolvent is the first `n` Taylor coefficients plus
`(hR)^n R(lambda+h)`. -/
theorem ringInverse_sub_add_smul_one_eq_sum_range_add_remainder
    {R : Type*}
    [NormedRing R]
    [HasSummableGeomSeries R]
    [NormedAlgebra ℝ R]
    (G : R)
    (lambda h : ℝ)
    (hunit : IsUnit (G - lambda • (1 : R)))
    (hsmall :
      ‖h • Ring.inverse (G - lambda • (1 : R))‖ < 1)
    (n : ℕ) :
    Ring.inverse (G - (lambda + h) • (1 : R)) =
      (∑ i ∈ Finset.range n,
        h ^ i • Ring.inverse (G - lambda • (1 : R)) ^ (i + 1)) +
      (h • Ring.inverse (G - lambda • (1 : R))) ^ n *
        Ring.inverse (G - (lambda + h) • (1 : R)) := by
  let res : R := Ring.inverse (G - lambda • (1 : R))
  let t : R := h • res
  have hfactor :
      Ring.inverse (G - (lambda + h) • (1 : R)) =
        Ring.inverse (1 - t) * res := by
    simpa only [t, res] using
      ringInverse_sub_add_smul_one_factor G lambda h hunit hsmall
  have hneumann :
      Ring.inverse (1 - t) =
        (∑ i ∈ Finset.range n, t ^ i) +
          t ^ n * Ring.inverse (1 - t) :=
    NormedRing.inverse_one_sub_nth_order' n
      (by simpa only [t, res] using hsmall)
  calc
    Ring.inverse (G - (lambda + h) • (1 : R)) =
        Ring.inverse (1 - t) * res := hfactor
    _ = ((∑ i ∈ Finset.range n, t ^ i) +
          t ^ n * Ring.inverse (1 - t)) * res :=
      congrArg (fun z : R => z * res) hneumann
    _ = (∑ i ∈ Finset.range n,
          h ^ i • res ^ (i + 1)) +
        t ^ n * (Ring.inverse (1 - t) * res) := by
      rw [add_mul, Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        exact smul_pow_mul_eq_smul_pow_succ h res i
      · rw [mul_assoc]
    _ = (∑ i ∈ Finset.range n,
          h ^ i • Ring.inverse (G - lambda • (1 : R)) ^ (i + 1)) +
        (h • Ring.inverse (G - lambda • (1 : R))) ^ n *
          Ring.inverse (G - (lambda + h) • (1 : R)) := by
      rw [hfactor]

/-- Infinite Taylor-Neumann expansion of the generic affine resolvent. -/
theorem ringInverse_sub_add_smul_one_hasSum
    {R : Type*}
    [NormedRing R]
    [HasSummableGeomSeries R]
    [NormedAlgebra ℝ R]
    (G : R)
    (lambda h : ℝ)
    (hunit : IsUnit (G - lambda • (1 : R)))
    (hsmall :
      ‖h • Ring.inverse (G - lambda • (1 : R))‖ < 1) :
    HasSum
      (fun n : ℕ =>
        h ^ n • Ring.inverse (G - lambda • (1 : R)) ^ (n + 1))
      (Ring.inverse (G - (lambda + h) • (1 : R))) := by
  let res : R := Ring.inverse (G - lambda • (1 : R))
  let t : R := h • res
  have ht : ‖t‖ < 1 := by simpa only [t, res] using hsmall
  have hsumm : Summable (fun n : ℕ => t ^ n) :=
    summable_geometric_of_norm_lt_one ht
  have hinvTsum : Ring.inverse (1 - t) = ∑' n : ℕ, t ^ n := by
    exact NormedRing.inverse_one_sub t ht
  have hgeom : HasSum (fun n : ℕ => t ^ n) (Ring.inverse (1 - t)) := by
    rw [hinvTsum]
    exact hsumm.hasSum
  have hfactor :
      Ring.inverse (G - (lambda + h) • (1 : R)) =
        Ring.inverse (1 - t) * res := by
    simpa only [t, res] using
      ringInverse_sub_add_smul_one_factor G lambda h hunit hsmall
  rw [hfactor]
  simpa only [t, res, smul_pow_mul_eq_smul_pow_succ] using
    hgeom.mul_right res

/-- A small generic operator-norm lemma used to keep power and multiplication
instance synthesis away from the huge concrete completed carrier. -/
theorem continuousLinearMap_pow_mul_norm_le
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A B : E →L[ℝ] E)
    (n : ℕ)
    (q M : ℝ)
    (hA : ‖A‖ ≤ q)
    (hB : ‖B‖ ≤ M) :
    ‖A ^ n * B‖ ≤ q ^ n * M := by
  cases n with
  | zero =>
      simpa using hB
  | succ n =>
      have hpow : ‖A ^ (n + 1)‖ ≤ q ^ (n + 1) := by
        calc
          ‖A ^ (n + 1)‖ ≤ ‖A‖ ^ (n + 1) :=
            norm_pow_le' A (Nat.succ_pos n)
          _ ≤ q ^ (n + 1) :=
            pow_le_pow_left₀ (norm_nonneg A) hA (n + 1)
      exact norm_mul_le_of_le hpow hB

local instance osBoundaryExcitationCompletedResolventTaylorNeumannSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedResolventTaylorNeumannSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedResolventTaylorNeumannSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedResolventTaylorNeumannSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedResolventTaylorNeumannSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedResolventTaylorNeumannSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedResolventTaylorNeumannSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedResolventTaylorNeumannPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The explicit inverse-gap radius implies the abstract Neumann smallness
condition at every completed below-gap base point. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_neumannSmall_of_abs_lt_gap_sub
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda h : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)
    (hh :
      |h| <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda) :
    ‖h •
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta lambda‖ < 1 := by
  let gap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
      H N hN beta hbeta
  let res :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
      H N hN beta hbeta lambda
  have hgap : 0 < gap - lambda := sub_pos.mpr hlambda
  have hres : ‖res‖ ≤ (gap - lambda)⁻¹ := by
    dsimp [res, gap]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_eq_green
        H N hN beta hbeta lambda hlambda]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_norm_le
        H N hN beta hbeta lambda hlambda
  calc
    ‖h • res‖ = |h| * ‖res‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |h| * (gap - lambda)⁻¹ :=
      mul_le_mul_of_nonneg_left hres (abs_nonneg h)
    _ < 1 := by
      rw [mul_inv_lt_iff₀ hgap]
      simpa only [one_mul] using hh

/-- The completed resolvent Taylor-Neumann series converges in operator norm
throughout the explicit radius `|h| < gap - lambda`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_hasSum_taylorNeumann
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda h : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)
    (hh :
      |h| <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda) :
    HasSum
      (fun n : ℕ =>
        h ^ n •
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta lambda) ^ (n + 1))
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
        H N hN beta hbeta (lambda + h)) := by
  have hunit :
      IsUnit
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta -
          lambda •
            (1 :
              periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta →L[ℝ]
                periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta)) := by
    simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator] using
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_isUnit_of_lt_gap
        H N hN beta hbeta lambda hlambda
  have hsmall :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_neumannSmall_of_abs_lt_gap_sub
      H N hN beta hbeta lambda h hlambda hh
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily] using
    ringInverse_sub_add_smul_one_hasSum
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      lambda h hunit hsmall

/-- Exact finite Taylor-Neumann expansion of the completed resolvent with
algebraic remainder `(h R_lambda)^n R_(lambda+h)`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_eq_sum_range_add_remainder
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda h : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)
    (hh :
      |h| <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
        H N hN beta hbeta (lambda + h) =
      (∑ i ∈ Finset.range n,
        h ^ i •
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta lambda) ^ (i + 1)) +
      (h •
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta lambda) ^ n *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta (lambda + h) := by
  have hunit :
      IsUnit
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta -
          lambda •
            (1 :
              periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta →L[ℝ]
                periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta)) := by
    simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator] using
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_isUnit_of_lt_gap
        H N hN beta hbeta lambda hlambda
  have hsmall :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_neumannSmall_of_abs_lt_gap_sub
      H N hN beta hbeta lambda h hlambda hh
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily] using
    ringInverse_sub_add_smul_one_eq_sum_range_add_remainder
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      lambda h hunit hsmall n

/-- Quantitative operator-norm estimate for the exact finite Taylor remainder.
The bound is geometric in `|h| / (gap-lambda)` and uses the already proved
below-gap bound at the shifted parameter. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_taylorRemainder_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda h : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)
    (hh :
      |h| <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda)
    (n : ℕ) :
    ‖(h •
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta lambda) ^ n *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta (lambda + h)‖ ≤
      (|h| *
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta - lambda)⁻¹) ^ n *
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta - (lambda + h))⁻¹ := by
  let gap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
      H N hN beta hbeta
  let res :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
      H N hN beta hbeta lambda
  let shifted :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
      H N hN beta hbeta (lambda + h)
  have hshift : lambda + h < gap := by
    have hle : h ≤ |h| := le_abs_self h
    linarith
  have hres : ‖res‖ ≤ (gap - lambda)⁻¹ := by
    dsimp [res, gap]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_eq_green
        H N hN beta hbeta lambda hlambda]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_norm_le
        H N hN beta hbeta lambda hlambda
  have hshifted : ‖shifted‖ ≤ (gap - (lambda + h))⁻¹ := by
    dsimp [shifted, gap]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_eq_green
        H N hN beta hbeta (lambda + h) hshift]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_norm_le
        H N hN beta hbeta (lambda + h) hshift
  have ht :
      ‖h • res‖ ≤ |h| * (gap - lambda)⁻¹ := by
    calc
      ‖h • res‖ = |h| * ‖res‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |h| * (gap - lambda)⁻¹ :=
        mul_le_mul_of_nonneg_left hres (abs_nonneg h)
  change ‖(h • res) ^ n * shifted‖ ≤
    (|h| * (gap - lambda)⁻¹) ^ n *
      (gap - (lambda + h))⁻¹
  exact
    continuousLinearMap_pow_mul_norm_le
      (h • res) shifted n
      (|h| * (gap - lambda)⁻¹)
      ((gap - (lambda + h))⁻¹)
      ht hshifted

/-- Audit-visible package for the completed finite-volume Taylor-Neumann
resolvent expansion. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventTaylorNeumannPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  hasTaylorNeumannSum :
    ∀ (lambda h : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta)
      (hh :
        |h| <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta - lambda),
      HasSum
        (fun n : ℕ =>
          h ^ n •
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
              H N hN beta hbeta lambda) ^ (n + 1))
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta (lambda + h))
  exactFiniteRemainder :
    ∀ (lambda h : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta)
      (hh :
        |h| <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta - lambda)
      (n : ℕ),
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
          H N hN beta hbeta (lambda + h) =
        (∑ i ∈ Finset.range n,
          h ^ i •
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
              H N hN beta hbeta lambda) ^ (i + 1)) +
        (h •
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
              H N hN beta hbeta lambda) ^ n *
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta (lambda + h)
  remainderNormBound :
    ∀ (lambda h : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta)
      (hh :
        |h| <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta - lambda)
      (n : ℕ),
      ‖(h •
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
              H N hN beta hbeta lambda) ^ n *
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily
            H N hN beta hbeta (lambda + h)‖ ≤
        (|h| *
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
              H N hN beta hbeta - lambda)⁻¹) ^ n *
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
              H N hN beta hbeta - (lambda + h))⁻¹

/-- Construct the completed finite-volume Taylor-Neumann package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedResolventTaylorNeumannPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventTaylorNeumannPackage
      H N hN beta hbeta := by
  refine ⟨?_, ?_, ?_⟩
  · intro lambda h hlambda hh
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_hasSum_taylorNeumann
        H N hN beta hbeta lambda h hlambda hh
  · intro lambda h hlambda hh n
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_eq_sum_range_add_remainder
        H N hN beta hbeta lambda h hlambda hh n
  · intro lambda h hlambda hh n
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenResolventFamily_taylorRemainder_norm_le
        H N hN beta hbeta lambda h hlambda hh n

end

end MathlibAnalytic
end MGAP4D
