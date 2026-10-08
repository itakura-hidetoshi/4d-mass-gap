import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFrozenZeroConstantFixed
import Mathlib.Tactic

/-!
# P4: the original frozen-beta-zero full-link physical receiver defect vanishes

The genuine frozen posterior projection on pair-Haar L2 is
  Q_e = U.symm ∘ P_e ∘ U
with P_e the ORIGINAL one-link conditional expectation on the physical
ground-state joint law. PR #5278 proves Q_e fixes the literal physical
constant receiver at beta=0. PR #5274 proves the beta-zero receiver of
any physical input f is its true constant Fourier coefficient times
that constant receiver.

Therefore, by REAL linearity of Q_e, EVERY original frozen-beta-zero
physical receiver lies in the fixed space of EVERY one-link projection.
Its one-link residual and full spatial-link sum are exactly zero, and
all entries of the genuine physical-pair-Haar residual Gram matrix
are zero, not just the diagonal.

These are exact finite-volume beta=0 statements, with unchanged
physical normalization lambda^(-1), signed receiver, half-density,
endpoint swap and original posterior law. The fine adjacent orbit
at beta(n+1) may be arbitrary; frozen beta(n)=0 does NOT imply a
positive-beta volume-uniform diagonal bound, spacing-scaled generator
gap, or continuum Yang--Mills mass gap. No Dobrushin is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4ZeroAllTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4ZeroAllCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4ZeroAllSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4ZeroAllMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4ZeroAllBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4ZeroAllSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Every ACTUAL frozen-beta-zero physical receiver is fixed by every
original one-link posterior projection. This combines the genuine
physical transfer rank-one result and #5278, not a new kernel. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_zero_spatialLink_fixed
    (H N : ℕ) (hN : 0 < N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    pairHaarTransportedGroundStateSpatialLinkProjection
        H N hN 0 (by norm_num) e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) =
      normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let V := normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection
    H N hN 0 (by norm_num) e
  let c : ℝ := inner ℝ u f
  have hv : V f = c • V u :=
    normalizedPhysicalOneSlabPairHaarReceiver_zero_rankOne H N hN f
  have hu : Q (V u) = V u :=
    pairHaarTransportedGroundStateSpatialLinkProjection_zero_fixed_constantReceiver
      H N hN e
  change Q (V f) = V f
  calc
    Q (V f) = Q (c • V u) := by rw [hv]
    _ = c • Q (V u) :=
      pairHaarTransportedGroundStateSpatialLinkProjection_smul
        H N hN 0 (by norm_num) e c (V u)
    _ = c • V u := by rw [hu]
    _ = V f := hv.symm

/-- Every genuine one-link posterior energy of every frozen-beta-zero
physical receiver is zero in the ORIGINAL pair-Haar carrier. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_zero_linkResidual_sq_eq_zero
    (H N : ℕ) (hN : 0 < N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f -
      pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0
        (by norm_num) e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2 =
      0 := by
  rw [normalizedPhysicalOneSlabPairHaarReceiver_zero_spatialLink_fixed H N hN f e]
  simp

/-- The FULL actual spatial-link posterior residual sum is zero for ALL
physical inputs at frozen beta=0. No link counting or surrogate bound. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_zero_fullLinkResidual_eq_zero
    (H N : ℕ) (hN : 0 < N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0
          (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2) =
      0 := by
  classical
  apply Finset.sum_eq_zero
  intro e _he
  exact normalizedPhysicalOneSlabPairHaarReceiver_zero_linkResidual_sq_eq_zero
    H N hN f e

/-- The TRUE original spatial-link posterior residual Gram matrix is
the zero matrix at frozen beta=0, for ANY finite physical input family.
Every off-diagonal entry is zero as well. -/
theorem pairHaarSpatialLinkResidualGram_zero_eq_zero_of_physicalFamily
    (H N : ℕ) (hN : 0 < N)
    {ι : Type*} [Fintype ι]
    (f : ι →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    pairHaarSpatialLinkResidualGram H N hN 0 (by norm_num)
        (fun i : ι =>
          normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) (f i)) =
      0 := by
  classical
  ext i j
  simp only [pairHaarSpatialLinkResidualGram, Matrix.sum_apply,
    Matrix.gram_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro e _he
  have hi := normalizedPhysicalOneSlabPairHaarReceiver_zero_spatialLink_fixed
    H N hN (f i) e
  have hj := normalizedPhysicalOneSlabPairHaarReceiver_zero_spatialLink_fixed
    H N hN (f j) e
  rw [hi, hj]
  simp

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- At frozen beta(n)=0 the ACTUAL right Krylov residual Gram is zero,
with no condition whatsoever on the distinct fine beta(n+1). -/
theorem fineRightKrylovPairHaarResidualGram_zero_of_frozen_beta_zero
    (hzero : beta n = 0) :
    fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r = 0 := by
  change pairHaarSpatialLinkResidualGram Hn 2 Pos (beta n) (hbeta n)
      (fun j : Fin (r + 1) =>
        normalizedPhysicalOneSlabPairHaarReceiver
          Hn 2 Pos (beta n) (hbeta n) (RightFactor n (j : ℕ))) = 0
  rw [hzero]
  exact pairHaarSpatialLinkResidualGram_zero_eq_zero_of_physicalFamily
    Hn 2 Pos (fun j : Fin (r + 1) => RightFactor n (j : ℕ))

/-- The three actual fine left Gram--Schmidt residual modes also have
zero frozen Gram matrix whenever frozen beta(n)=0. -/
theorem fineLeftThreeModePairHaarResidualGram_zero_of_frozen_beta_zero
    (hzero : beta n = 0) :
    fineLeftThreeModePairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r = 0 := by
  change pairHaarSpatialLinkResidualGram Hn 2 Pos (beta n) (hbeta n)
      (fun j : Fin 3 =>
        normalizedPhysicalOneSlabPairHaarReceiver
          Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r j)) = 0
  rw [hzero]
  exact pairHaarSpatialLinkResidualGram_zero_eq_zero_of_physicalFamily
    Hn 2 Pos (fun j : Fin 3 => LeftFactor n r j)

end ActualAdjacentOrbit
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
