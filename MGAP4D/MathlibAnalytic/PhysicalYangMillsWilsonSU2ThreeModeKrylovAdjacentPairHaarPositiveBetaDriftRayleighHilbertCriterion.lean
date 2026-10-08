import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveBetaDriftRayleigh
import Mathlib.Tactic

/-!
# P4: physical Hilbert norm bound and conditional positive-beta Rayleigh control

PR #5289 obtained the EXACT Rayleigh identity for the original
positive-beta projection-drift Gram B_beta and separated the full
original physical residual Gram G_beta into
  a*G_beta a <= 2 (A_beta(F) + inner(unit,F)^2 E_beta^vac)
for the COMBINED physical input F = sum_i a_i f_i.

The canonical physical Haar-L2 constant unit has norm one. The
actual Hilbert-space Cauchy--Schwarz inequality therefore sharpens
the projection-drift control to

  a*B_beta a <= ||F||^2 * E_beta^vac,

with no factor depending on number of physical modes or spatial links.
When the combined input is constant-orthogonal, the entire
projection-drift Rayleigh form vanishes exactly, leaving only the
genuine physical receiver drift.

Finally we record the purely CONDITIONAL finite-volume-to-uniform
Rayleigh interface: if genuine full-link receiver drift is bounded
by C_drift * ||F||^2 for every physical F, and the genuine one-vacuum
posterior-fiber energy is at most C_vac, then

  a*G_beta a <= 2 (C_drift + C_vac) ||F||^2.

No such positive-beta volume-uniform hypotheses are asserted or
proved here. No Dobrushin, surrogate posterior, or continuum
Yang--Mills mass-gap statement is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

/-- Sharp real Hilbert Cauchy--Schwarz for a unit vector; retains the
square of the TRUE signed inner product, not a sup norm. -/
private theorem real_unit_inner_sq_le_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u x : E) (hu : ‖u‖ = 1) :
    (inner ℝ u x) ^ 2 ≤ ‖x‖ ^ 2 := by
  have hCS : |inner ℝ u x| ≤ ‖x‖ := by
    calc
      |inner ℝ u x| ≤ ‖u‖ * ‖x‖ := abs_real_inner_le_norm u x
      _ = ‖x‖ := by rw [hu, one_mul]
  have hprod : 0 ≤
      (‖x‖ - |inner ℝ u x|) * (‖x‖ + |inner ℝ u x|) :=
    mul_nonneg (sub_nonneg.mpr hCS)
      (add_nonneg (norm_nonneg _) (abs_nonneg _))
  nlinarith [sq_abs (inner ℝ u x)]

local instance p4HilbertCritTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4HilbertCritCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4HilbertCritSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4HilbertCritMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4HilbertCritBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4HilbertCritSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Positive-beta physical projection-drift Gram Rayleigh form is bounded
by the actual combined PHYSICAL Hilbert norm squared times the true
one-vacuum joint posterior energy; no mode-count or link-count loss. -/
theorem physicalPairHaarZeroAnchoredProjectionDriftGram_rayleigh_le_physicalNorm_vacuum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec
        (physicalPairHaarZeroAnchoredProjectionDriftGram H N hN beta hbeta f) a) ≤
      ‖∑ i : ι, a i • f i‖ ^ 2 *
        physicalPairHaarOriginalJointVacuumFullLinkEnergy H N hN beta hbeta := by
  classical
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let F := ∑ i : ι, a i • f i
  let E := physicalPairHaarOriginalJointVacuumFullLinkEnergy H N hN beta hbeta
  have hunit : ‖u‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N
  have hsq : (inner ℝ u F) ^ 2 ≤ ‖F‖ ^ 2 :=
    real_unit_inner_sq_le_norm_sq u F hunit
  have hE : 0 ≤ E := by
    dsimp [E, physicalPairHaarOriginalJointVacuumFullLinkEnergy]
    apply Finset.sum_nonneg
    intro e _he
    exact sq_nonneg _
  have hRay :=
    physicalPairHaarZeroAnchoredProjectionDriftGram_rayleigh_jointVacuum
      H N hN beta hbeta f a
  change
    star a ⬝ᵥ
      (Matrix.mulVec (physicalPairHaarZeroAnchoredProjectionDriftGram
        H N hN beta hbeta f) a) =
      (inner ℝ u F) ^ 2 * E at hRay
  rw [hRay]
  exact mul_le_mul_of_nonneg_right hsq hE

/-- The full original positive-beta projection-drift Rayleigh form
vanishes when the COMBINED input is constant-orthogonal, even when
individual members of the family are not. -/
theorem physicalPairHaarZeroAnchoredProjectionDriftGram_rayleigh_zero_of_combinedOrthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ)
    (horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
      (∑ i : ι, a i • f i) = 0) :
    star a ⬝ᵥ
      (Matrix.mulVec
        (physicalPairHaarZeroAnchoredProjectionDriftGram H N hN beta hbeta f) a) = 0 := by
  rw [physicalPairHaarZeroAnchoredProjectionDriftGram_rayleigh_jointVacuum
    H N hN beta hbeta f a]
  simp [horth]

/-- For physical combinations orthogonal to the canonical constant
unit, the ACTUAL positive-beta residual Gram Rayleigh bound contains
ONLY the genuine receiver drift; the posterior projection drift
contributes exactly zero. -/
theorem pairHaarSpatialLinkResidualGram_physicalFamily_rayleigh_le_receiverDrift_of_orthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ)
    (horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
      (∑ i : ι, a i • f i) = 0) :
    star a ⬝ᵥ
      (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H N hN beta hbeta
          (fun i : ι =>
            normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i))) a) ≤
      2 * physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta
        (∑ i : ι, a i • f i) := by
  have h :=
    pairHaarSpatialLinkResidualGram_physicalFamily_rayleigh_le_betaDrift_jointVacuum
      H N hN beta hbeta f a
  simpa [horth] using h

/-- Conditional mode-count-free uniform Rayleigh interface.
All physical inputs g must obey the original receiver-drift estimate,
and the ORIGINAL positive-beta Wilson vacuum energy must obey its
specified bound. Neither estimate is assumed to exist automatically.
No volume-uniform theorem is claimed unless the hypotheses themselves
are discharged with constants independent of H. -/
theorem pairHaarSpatialLinkResidualGram_physicalFamily_rayleigh_le_of_vacuum_receiver_bounds
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (Cdrift Cvac : ℝ)
    (hDrift : ∀ g :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
      physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta g ≤
        Cdrift * ‖g‖ ^ 2)
    (hVac : physicalPairHaarOriginalJointVacuumFullLinkEnergy
        H N hN beta hbeta ≤ Cvac)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H N hN beta hbeta
          (fun i : ι =>
            normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i))) a) ≤
      2 * (Cdrift + Cvac) * ‖∑ i : ι, a i • f i‖ ^ 2 := by
  classical
  let F := ∑ i : ι, a i • f i
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let E := physicalPairHaarOriginalJointVacuumFullLinkEnergy H N hN beta hbeta
  let A := physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta F
  have hunit : ‖u‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N
  have hCoeff : (inner ℝ u F) ^ 2 ≤ ‖F‖ ^ 2 :=
    real_unit_inner_sq_le_norm_sq u F hunit
  have hE : 0 ≤ E := by
    dsimp [E, physicalPairHaarOriginalJointVacuumFullLinkEnergy]
    apply Finset.sum_nonneg
    intro e _he
    exact sq_nonneg _
  have hVac' : E ≤ Cvac := hVac
  have hVacTerm :
      (inner ℝ u F) ^ 2 * E ≤ ‖F‖ ^ 2 * Cvac := by
    calc
      (inner ℝ u F) ^ 2 * E ≤ ‖F‖ ^ 2 * E :=
        mul_le_mul_of_nonneg_right hCoeff hE
      _ ≤ ‖F‖ ^ 2 * Cvac :=
        mul_le_mul_of_nonneg_left hVac' (sq_nonneg _)
  have hA : A ≤ Cdrift * ‖F‖ ^ 2 := hDrift F
  have hMain :=
    pairHaarSpatialLinkResidualGram_physicalFamily_rayleigh_le_betaDrift_jointVacuum
      H N hN beta hbeta f a
  change
    star a ⬝ᵥ
      (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H N hN beta hbeta
          (fun i : ι => normalizedPhysicalOneSlabPairHaarReceiver
            H N hN beta hbeta (f i))) a) ≤
      2 * (A + (inner ℝ u F) ^ 2 * E) at hMain
  calc
    star a ⬝ᵥ
        (Matrix.mulVec
          (pairHaarSpatialLinkResidualGram H N hN beta hbeta
            (fun i : ι => normalizedPhysicalOneSlabPairHaarReceiver
              H N hN beta hbeta (f i))) a) ≤
        2 * (A + (inner ℝ u F) ^ 2 * E) := hMain
    _ ≤ 2 * (Cdrift * ‖F‖ ^ 2 + ‖F‖ ^ 2 * Cvac) := by
      have hsum := add_le_add hA hVacTerm
      linarith
    _ = 2 * (Cdrift + Cvac) * ‖F‖ ^ 2 := by ring

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
