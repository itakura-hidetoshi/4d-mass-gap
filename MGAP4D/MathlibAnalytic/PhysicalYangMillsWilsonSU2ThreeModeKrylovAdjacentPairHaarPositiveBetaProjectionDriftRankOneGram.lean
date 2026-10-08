import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumZeroIffRetainedWilson
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# P4: the ACTUAL positive-beta physical posterior-projection drift Gram is rank one

PRs #5280--#5285 reduced the genuine frozen-positive-beta posterior
projection drift of the beta-zero physical receiver to ONE original
Wilson vacuum joint conditional-expectation energy. PR #5286 clarifies
when this same energy can vanish. These results were previously
packaged chiefly as squared diagonal identities.

Here we preserve ALL off-diagonal inner products for an arbitrary
finite family of physical inputs f_i. The exact physical posterior
projection-drift Gram matrix

  B_beta(i,j) = sum_e < (Q_0,e-Q_beta,e) V_0 f_i,
                         (Q_0,e-Q_beta,e) V_0 f_j >

is the outer product of the true constant Fourier coefficients times
one and the SAME original full-link positive-beta vacuum energy:

  B_beta(i,j) = <u,f_i> <u,f_j> E_beta^vac.

The result is an exact positive-semidefinite rank-at-most-one Gram
structure for any finite number of physical modes, with no multiplier
equal to number of links or physical modes. It leaves the separate
true receiver drift A_beta and the vacuum energy E_beta^vac
unbounded in positive-beta spatial volume. No Dobrushin, alternative
posterior, or continuum Yang--Mills mass gap is invoked.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4DriftGramTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4DriftGramCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4DriftGramSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4DriftGramMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4DriftGramBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4DriftGramSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Vector-level reduction of the ORIGINAL projection drift to the
single literal pair-Haar L2 constant one. This is the exact #5281
rank-one receiver identity plus #5278--#5279 constant fixedness. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_projectionDrift_eq_constOne
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
      pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) •
        ((Lp.const 2
            (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
            (1 : ℝ)) -
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
            (Lp.const 2
              (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
              (1 : ℝ))) := by
  rw [normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_projectionDrift_rankOne
        H N hN beta hbeta f e,
      normalizedPhysicalOneSlabPairHaarReceiver_zero_spatialLink_fixed
        H N hN
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) e,
      normalizedPhysicalOneSlabPairHaarReceiver_zero_constantUnit_eq_one H N hN]

/-- The Gram matrix of genuine original-posterior projection drifts
for arbitrary finite physical inputs. All signed cross terms and
joint half-density dependence are retained. -/
noncomputable def physicalPairHaarZeroAnchoredProjectionDriftGram
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    Matrix ι ι ℝ :=
  ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
    Matrix.gram ℝ (fun i : ι =>
      pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) (f i)) -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) (f i)))

/-- Exact OFF-DIAGONAL rank-one identity. Every Gram entry is the
product of the original physical constant Fourier coefficients
and the same genuine all-link vacuum residual, with no combinatorial
loss in either the number of links or the number of physical modes. -/
theorem physicalPairHaarZeroAnchoredProjectionDriftGram_apply_rankOne
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (i j : ι) :
    physicalPairHaarZeroAnchoredProjectionDriftGram H N hN beta hbeta f i j =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) (f i)) *
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) (f j)) *
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖(Lp.const 2
            (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
            (1 : ℝ)) -
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
            (Lp.const 2
              (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
              (1 : ℝ))‖ ^ 2) := by
  classical
  simp only [physicalPairHaarZeroAnchoredProjectionDriftGram, Matrix.sum_apply,
    Matrix.gram_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  rw [normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_projectionDrift_eq_constOne
        H N hN beta hbeta (f i) e,
      normalizedPhysicalOneSlabPairHaarReceiver_beta_zeroAnchored_projectionDrift_eq_constOne
        H N hN beta hbeta (f j) e]
  simp only [real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

/-- Matrix-level exact outer-product factorization. This establishes
rank at most one algebraically, including all mixed entries, rather
than only a diagonal norm identity. -/
theorem physicalPairHaarZeroAnchoredProjectionDriftGram_eq_outerProduct
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    physicalPairHaarZeroAnchoredProjectionDriftGram H N hN beta hbeta f =
      Matrix.of (fun i j : ι =>
        (inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) (f i)) *
        (inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) (f j)) *
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖(Lp.const 2
              (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
              (1 : ℝ)) -
            pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
              (Lp.const 2
                (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
                (1 : ℝ))‖ ^ 2)) := by
  ext i j
  exact physicalPairHaarZeroAnchoredProjectionDriftGram_apply_rankOne
    H N hN beta hbeta f i j

/-- The original physical projection-drift Gram stays positive
semidefinite even at positive beta: this follows from its genuine
Gram origin and requires NO volume-uniform posterior estimate. -/
theorem physicalPairHaarZeroAnchoredProjectionDriftGram_posSemidef
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (physicalPairHaarZeroAnchoredProjectionDriftGram H N hN beta hbeta f).PosSemidef := by
  unfold physicalPairHaarZeroAnchoredProjectionDriftGram
  exact Matrix.posSemidef_sum
    (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) (by
      intro e _he
      exact Matrix.posSemidef_gram ℝ
        (fun i : ι =>
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
              (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) (f i)) -
            pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
              (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) (f i))))

/-- If every physical mode is orthogonal to the constant unit,
the ENTIRE positive-beta projection-drift Gram, including every
off-diagonal entry, is exactly the zero matrix. This makes no claim
that the separate positive-beta receiver-drift Gram vanishes. -/
theorem physicalPairHaarZeroAnchoredProjectionDriftGram_zero_of_constantOrthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (horth : ∀ i : ι,
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) (f i) = 0) :
    physicalPairHaarZeroAnchoredProjectionDriftGram H N hN beta hbeta f = 0 := by
  ext i j
  rw [physicalPairHaarZeroAnchoredProjectionDriftGram_apply_rankOne
      H N hN beta hbeta f i j, horth i]
  simp

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
