import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredOriginalFiberCrossCovariance
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalInputRayleigh
import Mathlib.Tactic

/-!
# P4-Q2: signed original Wilson posterior resampling polarization

PR #5323 identifies the uncentered right Krylov Gram entries with
literal signed ORIGINAL posterior-fiber cross integrals. We now
identify precisely the same signed cross terms with *differences*
of the actual two-copy Wilson posteriorResamplingEnergy, not a
surrogate conditional covariance or a made-up positive kernel.

For the original physical input f, write
  I_beta,e(f) = V_beta(f) - Q_beta,e(V_beta(f)).
The genuine original physical-to-pair-Haar receiver and the
transported Wilson CondExpL2 projection are real linear; hence
  I(f+g) = I(f)+I(g),  I(f-g)=I(f)-I(g).

Native real Hilbert polarization and the already proven exact
resampling normalization yield
  8 * inner(I(f),I(g))
    = E_beta,e(W*M_(f+g)) - E_beta,e(W*M_(f-g)),
where E_beta,e is the original posteriorResamplingEnergy under
the genuine Wilson joint law and conditional link-update kernel.

We also identify for the authentic UN-CENTERED fine-right Krylov
orbit (fine beta(n+1), frozen beta(n)):
  8 * G_right(i,j) = sum_e (E_beta,e(R_i+R_j) - E_beta,e(R_i-R_j)),
and for any coefficient vector a, exactly
  a*G_right*a = (1/2) * sum_e E_beta,e(sum_j a_j R_j).

These identities leave all signs and the original physical Wilson
measure untouched and expose a two-replica finite-link correlation
target for subsequent locality estimates. NO independent volume
uniformity, correlation decay, Dobrushin assumption, or continuum
Yang--Mills mass-gap conclusion is made; no sorry/admit/new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4ResamplePolTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4ResamplePolCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4ResamplePolSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4ResamplePolMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4ResamplePolBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4ResamplePolLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Alias for the actual physical pair-Haar receiver residual of the
ORIGINAL Wilson transported conditional expectation at link e. -/
noncomputable def physicalOriginalReceiverPosteriorInnovation
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f
  v - pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e v

/-- Original Wilson receiver innovations are additive in the physical
input because both the transfer receiver and posterior projection are
real-linear, without assuming anything about spatial locality. -/
theorem physicalOriginalReceiverPosteriorInnovation_add
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e (f + g) =
      physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e f +
      physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e g := by
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
  let L := normalizedPhysicalOneSlabPairHaarReceiverLinearMap H N hN beta hbeta
  have hv : v (f + g) = v f + v g := by
    change L (f + g) = L f + L g
    exact map_add L f g
  change v (f + g) - Q (v (f + g)) =
    (v f - Q (v f)) + (v g - Q (v g))
  rw [hv]
  have hQ : Q (v f + v g) = Q (v f) + Q (v g) :=
    pairHaarTransportedGroundStateSpatialLinkProjection_add
      H N hN beta hbeta e (v f) (v g)
  rw [hQ]
  abel

/-- Exact subtraction, including the minus sign of the signed receiver. -/
theorem physicalOriginalReceiverPosteriorInnovation_sub
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e (f - g) =
      physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e f -
      physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e g := by
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
  let L := normalizedPhysicalOneSlabPairHaarReceiverLinearMap H N hN beta hbeta
  have hv : v (f - g) = v f - v g := by
    change L (f - g) = L f - L g
    exact map_sub L f g
  have hQneg : Q (-(v g)) = -(Q (v g)) := by
    simpa only [neg_one_smul] using
      (pairHaarTransportedGroundStateSpatialLinkProjection_smul
        H N hN beta hbeta e (-1 : ℝ) (v g))
  have hQ : Q (v f - v g) = Q (v f) - Q (v g) := by
    calc
      Q (v f - v g) = Q (v f + -(v g)) := by rw [sub_eq_add_neg]
      _ = Q (v f) + Q (-(v g)) :=
        pairHaarTransportedGroundStateSpatialLinkProjection_add
          H N hN beta hbeta e (v f) (-(v g))
      _ = Q (v f) - Q (v g) := by rw [hQneg]; rfl
  change v (f - g) - Q (v (f - g)) =
    (v f - Q (v f)) - (v g - Q (v g))
  rw [hv, hQ]
  abel

/-- TRUE original Wilson posterior-resampling polarization: the
signed innovation cross-covariance is one eighth of the difference
of the two physical conditional two-copy resampling energies. -/
theorem physicalOriginalReceiverPosteriorInnovation_inner_eq_resamplingPolarization
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    8 * inner ℝ
      (physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e f)
      (physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e g) =
      posteriorResamplingEnergy H N hN beta hbeta e
        (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta (f + g)) -
      posteriorResamplingEnergy H N hN beta hbeta e
        (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta (f - g)) := by
  let x := physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e f
  let y := physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e g
  have hPlus :
      posteriorResamplingEnergy H N hN beta hbeta e
        (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta (f + g)) =
        2 * ‖x + y‖ ^ 2 := by
    have h := normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_two_pairHaarResidual
      H N hN beta hbeta (f + g) e
    change posteriorResamplingEnergy H N hN beta hbeta e
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta (f + g)) =
      2 * ‖physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e (f + g)‖ ^ 2 at h
    rw [physicalOriginalReceiverPosteriorInnovation_add] at h
    exact h
  have hMinus :
      posteriorResamplingEnergy H N hN beta hbeta e
        (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta (f - g)) =
        2 * ‖x - y‖ ^ 2 := by
    have h := normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_two_pairHaarResidual
      H N hN beta hbeta (f - g) e
    change posteriorResamplingEnergy H N hN beta hbeta e
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta (f - g)) =
      2 * ‖physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e (f - g)‖ ^ 2 at h
    rw [physicalOriginalReceiverPosteriorInnovation_sub] at h
    exact h
  have hPol : ‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 = 4 * inner ℝ x y := by
    rw [norm_add_sq_real, norm_sub_sq_real]
    ring
  change 8 * inner ℝ x y =
    posteriorResamplingEnergy H N hN beta hbeta e
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta (f + g)) -
    posteriorResamplingEnergy H N hN beta hbeta e
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta (f - g))
  calc
    8 * inner ℝ x y = 2 * (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) := by rw [hPol]; ring
    _ = _ := by rw [hPlus, hMinus]; ring

/-- For the original SU(2) physical Krylov family the genuine signed
posterior link covariance is directly the difference of original
two-copy resampling energies of sum/difference physical right inputs. -/
theorem fineRightKrylovOriginalPosteriorLinkCovariance_resamplingPolarization
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (i j : Fin (r + 1)) :
    let H := halfExtent (n + 1)
    let R : Fin (r + 1) →
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
      fun k => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (k : ℕ)
    8 * fineRightKrylovOriginalPosteriorLinkCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r e i j =
      posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) e
        (normalizedPhysicalOneSlabJointReceiverProductBCF H 2
          specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R i + R j)) -
      posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) e
        (normalizedPhysicalOneSlabJointReceiverProductBCF H 2
          specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R i - R j)) := by
  classical
  let H := halfExtent (n + 1)
  let R : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun k => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (k : ℕ)
  simpa only [H, R, fineRightKrylovOriginalPosteriorLinkCovariance,
    fineRightKrylovOriginalPosteriorLinkResidual,
    physicalOriginalReceiverPosteriorInnovation] using
    (physicalOriginalReceiverPosteriorInnovation_inner_eq_resamplingPolarization
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e (R i) (R j))

/-- ORIGINAL uncentered true right Gram mode-pair is the all-link sum
of signed two-copy posterior-resampling polarizations. The sum is kept
BEFORE any absolute values, hence genuine cancellations are preserved. -/
theorem fineRightKrylovPairHaarResidualGram_entry_resamplingPolarization
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i j : Fin (r + 1)) :
    let H := halfExtent (n + 1)
    let R : Fin (r + 1) →
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
      fun k => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (k : ℕ)
    8 * (fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) i j =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) e
          (normalizedPhysicalOneSlabJointReceiverProductBCF H 2
            specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R i + R j)) -
        posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) e
          (normalizedPhysicalOneSlabJointReceiverProductBCF H 2
            specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R i - R j))) := by
  classical
  let H := halfExtent (n + 1)
  let R : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun k => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (k : ℕ)
  calc
    8 * (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) i j =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        8 * fineRightKrylovOriginalPosteriorLinkCovariance
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r e i j := by
        rw [fineRightKrylovPairHaarResidualGram_entry_eq_originalPosteriorCovariance,
          fineRightKrylovOriginalPosteriorModeCovariance, Finset.mul_sum]
    _ = ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) e
          (normalizedPhysicalOneSlabJointReceiverProductBCF H 2
            specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R i + R j)) -
        posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) e
          (normalizedPhysicalOneSlabJointReceiverProductBCF H 2
            specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) (R i - R j))) := by
          apply Finset.sum_congr rfl
          intro e _he
          exact fineRightKrylovOriginalPosteriorLinkCovariance_resamplingPolarization
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r e i j

/-- Exact genuine right-Krylov Rayleigh energy as ONE HALF of the
full-link original-Wilson posterior resampling energy of the SINGLE
physical input combination. No mode-count/volume worst-case bound. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_eq_half_originalResamplingEnergy
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    let H := halfExtent (n + 1)
    let F :=
      ∑ j : Fin (r + 1), a j •
        physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (j : ℕ)
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) =
      (1 / 2 : ℝ) * ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) e
          (normalizedPhysicalOneSlabJointReceiverProductBCF H 2
            specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) F) := by
  classical
  let H := halfExtent (n + 1)
  let F :=
    ∑ j : Fin (r + 1), a j •
      physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (j : ℕ)
  let V := normalizedPhysicalOneSlabPairHaarReceiver
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  have hRay :
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖V F - Q e (V F)‖ ^ 2 := by
    simpa only [H, F, V, Q] using
      (fineRightKrylovPairHaarResidualGram_rayleigh_physicalInput
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a)
  have hEnergy (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      ‖V F - Q e (V F)‖ ^ 2 =
      (1 / 2 : ℝ) *
        posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) e
          (normalizedPhysicalOneSlabJointReceiverProductBCF H 2
            specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) F) := by
    have h := normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_two_pairHaarResidual
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) F e
    change posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) e
          (normalizedPhysicalOneSlabJointReceiverProductBCF H 2
            specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) F) =
        2 * ‖V F - Q e (V F)‖ ^ 2 at h
    linarith
  calc
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖V F - Q e (V F)‖ ^ 2 := hRay
    _ = ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (1 / 2 : ℝ) *
          posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) e
            (normalizedPhysicalOneSlabJointReceiverProductBCF H 2
              specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) F) := by
          apply Finset.sum_congr rfl
          intro e _he
          exact hEnergy e
    _ = (1 / 2 : ℝ) * ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) e
            (normalizedPhysicalOneSlabJointReceiverProductBCF H 2
              specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) F) := by
          rw [Finset.mul_sum]

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
