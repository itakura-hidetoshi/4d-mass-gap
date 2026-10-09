import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredOriginalJointConditionalCovariance
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarProjectionPosteriorFiber
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# P4-Q2: signed ORIGINAL Wilson posterior fiber cross-covariance

PR #5322 proved that the authentic pair-Haar posterior innovations
are the exact original Wilson joint CondExpL2 covariance loss.
Here we identify their SIGNED cross-inner-product with the *literal*
pair-Haar integral of the two physical posterior-fiber residuals:

  R_beta,e(f)(z) =
    V_beta(f)(z) - sqrt(rho_beta(z)) *
      posteriorMean_beta,e(W_beta * M_f)(z).

  inner(V_beta f - Q_beta,e V_beta f,
        V_beta g - Q_beta,e V_beta g)
    = integral_z inner(R_beta,e(f)(z), R_beta,e(g)(z)) d mu_pairHaar.

The proof uses the pinned mathlib L2.inner_def and the already
established original physical posteriorMean representative, including
the half-density, inverse physical-transfer normalization, and full
source/output signs. It does NOT polarize a proxy conditional law.

Specialize to the genuine UN-CENTERED fine-right Krylov orbit and
identify each signed link covariance, its mode-pair sum, and the
actual right Gram entries with physical posterior-fiber integrals.
The Schur bound from #5321 can then consume a *proved row bound
on these literal signed covariance integrals*.

Frozen beta(n) and fine beta(n+1) remain distinct. These exact
finite-volume identities do not assert locality decay, volume-uniform
summability, a continuum limit or a positive continuum mass gap.
No Dobrushin, surrogate posterior, sorry/admit, or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4FiberCrossTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4FiberCrossCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4FiberCrossSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4FiberCrossMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4FiberCrossBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4FiberCrossLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The pointwise ORIGINAL physical Wilson posterior-fiber innovation.
It uses the actual normalized physical pair-Haar receiver, the genuine
Wilson joint sqrt density, and the actual retained posteriorMean e. -/
noncomputable def originalWilsonPhysicalPosteriorFiberResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f z -
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
      H N hN beta hbeta z *
      posteriorMean H N hN beta hbeta e
        (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) z

/-- The SIGNED cross covariance of two actual physical Wilson receivers
equals the literal integral of their two original posterior-fiber
innovations. No absolute value or cancellation has been dropped. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_residualInner_eq_originalFiberIntegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
    let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
    inner ℝ (v f - Q (v f)) (v g - Q (v g)) =
      ∫ z,
        inner ℝ
          (originalWilsonPhysicalPosteriorFiberResidual H N hN beta hbeta f e z)
          (originalWilsonPhysicalPosteriorFiberResidual H N hN beta hbeta g e z)
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N := by
  let μP := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
  let rf : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N := v f - Q (v f)
  let rg : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N := v g - Q (v g)
  have hf :
      rf =ᵐ[μP] originalWilsonPhysicalPosteriorFiberResidual H N hN beta hbeta f e := by
    simpa only [rf, v, Q, μP, originalWilsonPhysicalPosteriorFiberResidual] using
      (normalizedPhysicalOneSlabPairHaarReceiver_projectionResidual_coeFn
        H N hN beta hbeta f e)
  have hg :
      rg =ᵐ[μP] originalWilsonPhysicalPosteriorFiberResidual H N hN beta hbeta g e := by
    simpa only [rg, v, Q, μP, originalWilsonPhysicalPosteriorFiberResidual] using
      (normalizedPhysicalOneSlabPairHaarReceiver_projectionResidual_coeFn
        H N hN beta hbeta g e)
  change inner ℝ rf rg =
      ∫ z, inner ℝ
        (originalWilsonPhysicalPosteriorFiberResidual H N hN beta hbeta f e z)
        (originalWilsonPhysicalPosteriorFiberResidual H N hN beta hbeta g e z) ∂μP
  calc
    inner ℝ rf rg =
        ∫ z, inner ℝ (rf z) (rg z) ∂μP := L2.inner_def rf rg
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf, hg] with z hzf hzg
      rw [hzf, hzg]

/-- Genuine uncentered right-Krylov SIGNED link covariance is the
literal original Wilson posterior-fiber cross integral. -/
theorem fineRightKrylovOriginalPosteriorLinkCovariance_eq_originalFiberIntegral
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (i j : Fin (r + 1)) :
    let H := halfExtent (n + 1)
    let R : Fin (r + 1) →
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
      fun k => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (k : ℕ)
    fineRightKrylovOriginalPosteriorLinkCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e i j =
      ∫ z, inner ℝ
        (originalWilsonPhysicalPosteriorFiberResidual
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R i) e z)
        (originalWilsonPhysicalPosteriorFiberResidual
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R j) e z)
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2 := by
  classical
  let H := halfExtent (n + 1)
  let R : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun k => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (k : ℕ)
  simpa only [H, R, fineRightKrylovOriginalPosteriorLinkCovariance,
    fineRightKrylovOriginalPosteriorLinkResidual] using
    (normalizedPhysicalOneSlabPairHaarReceiver_residualInner_eq_originalFiberIntegral
      H 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n) (R i) (R j) e)

/-- Signed mode-pair covariance equals the all-link sum of LITERAL
original Wilson posterior-fiber cross integrals (no absolute values
taken inside or outside the physical link sum). -/
theorem fineRightKrylovOriginalPosteriorModeCovariance_eq_originalFiberIntegralSum
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i j : Fin (r + 1)) :
    let H := halfExtent (n + 1)
    let R : Fin (r + 1) →
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
      fun k => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (k : ℕ)
    fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r i j =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ∫ z, inner ℝ
          (originalWilsonPhysicalPosteriorFiberResidual
            H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R i) e z)
          (originalWilsonPhysicalPosteriorFiberResidual
            H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R j) e z)
          ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2 := by
  classical
  let H := halfExtent (n + 1)
  let R : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun k => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (k : ℕ)
  change fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r i j =
    ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ∫ z, inner ℝ
        (originalWilsonPhysicalPosteriorFiberResidual
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R i) e z)
        (originalWilsonPhysicalPosteriorFiberResidual
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R j) e z)
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  unfold fineRightKrylovOriginalPosteriorModeCovariance
  apply Finset.sum_congr rfl
  intro e _he
  exact
    (fineRightKrylovOriginalPosteriorLinkCovariance_eq_originalFiberIntegral
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r e i j)

/-- The TRUE uncentered fine-right Krylov Gram entries admit this
concrete posteriorMean fiber-cross-integral representation. -/
theorem fineRightKrylovPairHaarResidualGram_entry_eq_originalFiberIntegralSum
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i j : Fin (r + 1)) :
    let H := halfExtent (n + 1)
    let R : Fin (r + 1) →
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
      fun k => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (k : ℕ)
    (fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) i j =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ∫ z, inner ℝ
          (originalWilsonPhysicalPosteriorFiberResidual
            H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R i) e z)
          (originalWilsonPhysicalPosteriorFiberResidual
            H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R j) e z)
          ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2 := by
  classical
  let H := halfExtent (n + 1)
  let R : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun k => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (k : ℕ)
  calc
    (fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) i j =
      fineRightKrylovOriginalPosteriorModeCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i j :=
          fineRightKrylovPairHaarResidualGram_entry_eq_originalPosteriorCovariance
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r i j
    _ = ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ∫ z, inner ℝ
          (originalWilsonPhysicalPosteriorFiberResidual
            H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R i) e z)
          (originalWilsonPhysicalPosteriorFiberResidual
            H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R j) e z)
          ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2 :=
          fineRightKrylovOriginalPosteriorModeCovariance_eq_originalFiberIntegralSum
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r i j

/-- Exact signed original posterior-fiber covariance row criterion
for the REAL uncentered physical right-Krylov Rayleigh form. Its
hypothesis is to be proved from local Wilson interaction estimates;
it is not treated as automatically uniform in lattice volume. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_originalFiberIntegralSchur
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) (C : ℝ)
    (hRow : ∀ i : Fin (r + 1),
      (∑ j : Fin (r + 1),
        |(∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
          ∫ z, inner ℝ
            (originalWilsonPhysicalPosteriorFiberResidual
              (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
                (beta n) (hbeta n)
                (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
                  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                  n (i : ℕ)) e z)
            (originalWilsonPhysicalPosteriorFiberResidual
              (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
                (beta n) (hbeta n)
                (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
                  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                  n (j : ℕ)) e z)
            ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
              (halfExtent (n + 1)) 2)|) ≤ C) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤ C * (∑ j : Fin (r + 1), (a j) ^ 2) := by
  apply fineRightKrylovPairHaarResidualGram_rayleigh_le_originalCovarianceSchur
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a C
  intro i
  simpa only [fineRightKrylovOriginalPosteriorModeCovariance_eq_originalFiberIntegralSum]
    using hRow i

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
