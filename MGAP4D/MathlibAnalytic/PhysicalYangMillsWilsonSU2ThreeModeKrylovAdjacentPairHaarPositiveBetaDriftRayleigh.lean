import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveBetaProjectionDriftRankOneGram
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# P4: rank-one vacuum Rayleigh and actual positive-beta receiver-drift criterion

The exact physical posterior-projection drift Gram from PR #5287 is a
positive-beta rank-one outer product with coefficient the unchanged
full-link Wilson vacuum conditional-expectation energy.

This file proves its COMPLETE real finite-mode Rayleigh identity.
Crucially its coefficient is the original Fourier coefficient of the
COMBINED physical input, not an estimate by number of modes:

  a* B_beta a =
    inner(unit, sum_i a_i f_i)^2 * E_beta^vac.

It also combines the ORIGINAL physical residual Gram Rayleigh identity
(#5271), the genuine beta-zero-anchored two-drift bound (#5280), and
the true joint posterior vacuum identity (#5282), giving the sharp
structural separation (factor 2 from the norm sum inequality):

  a* G_beta a <= 2 (A_beta(sum_i a_i f_i)
                    + inner(unit,sum_i a_i f_i)^2 * E_beta^vac).

There is no link-count or number-of-modes factor in this P4 reduction.
It does NOT prove either genuine positive-beta drift term is bounded
uniformly in volume. No Dobrushin, surrogate posterior, or continuum
Yang--Mills mass-gap inference is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

/-- Elementary exact real rank-one matrix Rayleigh formula, with
arbitrary finite index set, no normalization, and no mode-count loss. -/
private theorem real_rankOne_outerMatrix_rayleigh
    {ι : Type*} [Fintype ι]
    (c a : ι → ℝ) (E : ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec (Matrix.of (fun i j : ι => c i * c j * E)) a) =
      (∑ i : ι, a i * c i) ^ 2 * E := by
  classical
  calc
    star a ⬝ᵥ
        (Matrix.mulVec (Matrix.of (fun i j : ι => c i * c j * E)) a) =
      ∑ i : ι, ∑ j : ι, a i * (c i * c j * E * a j) := by
        simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ = (∑ i : ι, a i * c i) * (∑ j : ι, a j * c j * E) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = (∑ i : ι, a i * c i) ^ 2 * E := by
      rw [← Finset.sum_mul]
      ring

local instance p4DriftRayleighTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4DriftRayleighCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4DriftRayleighSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4DriftRayleighMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4DriftRayleighBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4DriftRayleighSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- EXACT Rayleigh form of the original positive-beta posterior
projection-drift Gram. The physical input is combined BEFORE taking
its Fourier coefficient. -/
theorem physicalPairHaarZeroAnchoredProjectionDriftGram_rayleigh_rankOne
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec
        (physicalPairHaarZeroAnchoredProjectionDriftGram
          H N hN beta hbeta f) a) =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
        (∑ i : ι, a i • f i)) ^ 2 *
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖(Lp.const 2
            (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
            (1 : ℝ)) -
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
            (Lp.const 2
              (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
              (1 : ℝ))‖ ^ 2) := by
  classical
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let c : ι → ℝ := fun i => inner ℝ u (f i)
  let E : ℝ := ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
    ‖(Lp.const 2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
        (1 : ℝ)) -
      pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
        (Lp.const 2
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
          (1 : ℝ))‖ ^ 2
  have hCoeff :
      inner ℝ u (∑ i : ι, a i • f i) =
        ∑ i : ι, a i * c i := by
    simp only [inner_sum, real_inner_smul_right, c]
  have hOuter :
      physicalPairHaarZeroAnchoredProjectionDriftGram H N hN beta hbeta f =
        Matrix.of (fun i j : ι => c i * c j * E) :=
    physicalPairHaarZeroAnchoredProjectionDriftGram_eq_outerProduct
      H N hN beta hbeta f
  change star a ⬝ᵥ
      (Matrix.mulVec
        (physicalPairHaarZeroAnchoredProjectionDriftGram H N hN beta hbeta f) a) =
      (inner ℝ u (∑ i : ι, a i • f i)) ^ 2 * E
  rw [hOuter, hCoeff]
  exact real_rankOne_outerMatrix_rayleigh c a E

/-- The SAME physical Rayleigh identity with the original conditional
expectation on the positive-beta ground-state joint law, not a
pair-Haar replacement kernel. -/
theorem physicalPairHaarZeroAnchoredProjectionDriftGram_rayleigh_jointVacuum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec
        (physicalPairHaarZeroAnchoredProjectionDriftGram
          H N hN beta hbeta f) a) =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
        (∑ i : ι, a i • f i)) ^ 2 *
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta e
            (originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta)‖ ^ 2) := by
  rw [physicalPairHaarZeroAnchoredProjectionDriftGram_rayleigh_rankOne
    H N hN beta hbeta f a]
  rw [pairHaarConstantOne_fullLinkResidual_eq_jointCondExpVacuum]
  rfl

/-- The actual normalized positive-beta receiver drift, carrying
the unchanged physical inverse-transfer normalization. -/
noncomputable def physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ℝ :=
  ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
    ‖(normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
        normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
      pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
          normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2

/-- The original, true joint-law positive-beta vacuum posterior energy.
This is a name for the pre-existing #5282 energy, not a new kernel. -/
noncomputable def physicalPairHaarOriginalJointVacuumFullLinkEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
    ‖originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta e
        (originalGroundStateJointTransportedPairHaarOne H N hN beta hbeta)‖ ^ 2

/-- TRUE physical residual Gram Rayleigh bound, now retaining the
exact rank-one (hence mode-count-free) projection drift and the
separate genuine receiver drift for the COMBINED physical input.
No nonzero-beta uniform estimate is inserted. -/
theorem pairHaarSpatialLinkResidualGram_physicalFamily_rayleigh_le_betaDrift_jointVacuum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H N hN beta hbeta
          (fun i : ι => normalizedPhysicalOneSlabPairHaarReceiver
            H N hN beta hbeta (f i))) a) ≤
      2 * (
        physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta
          (∑ i : ι, a i • f i) +
        (inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
          (∑ i : ι, a i • f i)) ^ 2 *
        physicalPairHaarOriginalJointVacuumFullLinkEnergy H N hN beta hbeta) := by
  let g := ∑ i : ι, a i • f i
  have hRay :=
    pairHaarSpatialLinkResidualGram_rayleigh_physicalInput
      H N hN beta hbeta f a
  have hBound :=
    normalizedPhysicalOneSlabPairHaarReceiver_beta_fullLinkResidual_le_zeroAnchored
      H N hN beta hbeta g
  have hVac :=
    normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_fullProjectionDrift_eq_jointVacuum
      H N hN beta hbeta g
  rw [hVac] at hBound
  have hBound' :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta g -
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta g)‖ ^ 2) ≤
      2 * (physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta g +
        (inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) g) ^ 2 *
        physicalPairHaarOriginalJointVacuumFullLinkEnergy H N hN beta hbeta) := by
    simpa only [physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy,
      physicalPairHaarOriginalJointVacuumFullLinkEnergy,
      originalGroundStateJointTransportedPairHaarOne] using hBound
  exact hRay.le_trans hBound'

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
