import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredResamplingPolarization
import Mathlib.Tactic

/-!
# P4-Q2: pointwise original-Wilson posterior-resampling local variation

The exact #5324 true uncentered right-Krylov Gram equals half the sum
of genuine Wilson joint/posterior *two-copy* resampling energies of the
single combined physical input. This file takes the next physical step:
the squared resampling difference is bounded link by link by a VERIFIED
pointwise variation envelope for the SAME original joint BCF.

For any original Wilson joint observable F and target spatial link e,
if |F(z)-F(z[e <- g])| <= b_e(z) for every actual target group value g,
then the ACTUAL original Wilson conditional probability, followed by
the ACTUAL original joint measure, proves

  posteriorResamplingEnergy_e(F) <= integral b_e(z)^2 d mu_joint(z).

No replacement joint law, vacuum factorization, finite-range support,
or Dobrushin estimate is used. In particular, an observable which is
actually invariant under a target update has exactly zero resampling
energy at that link, independent of the nonlocal positive-beta vacuum.

For the AUTHENTIC uncentered fine-right physical Krylov combination
F = sum_j a_j S_{beta(n+1)}^j 1, we retain the complete signed original
Wilson joint receiver W_{beta(n)} M_F and prove a Rayleigh upper bound
from certified per-link pointwise oscillation coefficients b(e).
The sum over actual links precedes any worst-case cardinality bound.

This is a rigorous LOCAL-OSCILLATION HANDOFF, not a claim that the
physical right Krylov receiver has compact support, summable variation,
a volume-uniform bound, or a continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4PhysicalOscTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4PhysicalOscCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4PhysicalOscSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4PhysicalOscMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4PhysicalOscBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4PhysicalOscLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- For the genuine Wilson joint measure and genuine conditional one-link
probability, a pointwise local *observable difference* controls the
actual two-replica resampling energy. There is no factor |Links(H)|. -/
theorem originalWilsonPosteriorResamplingEnergy_le_pointwiseLinkOscillation
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hb : Integrable (fun z => b z ^ 2)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta))
    (hOsc : ∀ z (g : Matrix.specialUnitaryGroup (Fin N) ℂ),
      |F z - F (z.1, Function.update z.2 e g)| ≤ b z) :
    posteriorResamplingEnergy H N hN beta hbeta e F ≤
      ∫ z, b z ^ 2
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta := by
  classical
  let μJ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
  have hEach (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      posteriorResamplingSquare H N hN beta hbeta e F z ≤ b z ^ 2 := by
    let ν := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta z.1 z.2 e
    letI : IsProbabilityMeasure ν :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
        H N hN beta hbeta z.1 z.2 e
    change (∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        (F z - F (z.1, Function.update z.2 e g)) ^ 2 ∂ν) ≤ b z ^ 2
    calc
      (∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        (F z - F (z.1, Function.update z.2 e g)) ^ 2 ∂ν) ≤
          ∫ _g : Matrix.specialUnitaryGroup (Fin N) ℂ, b z ^ 2 ∂ν := by
            apply integral_mono
              (posteriorResamplingDifferenceSquare_integrable
                H N hN beta hbeta e F z)
              (integrable_const _)
            intro g
            have hs := pow_le_pow_left₀ (abs_nonneg _) (hOsc z g) 2
            simpa only [sq_abs] using hs
      _ = b z ^ 2 := by simp
  change (∫ z, posteriorResamplingSquare H N hN beta hbeta e F z ∂μJ) ≤
    ∫ z, b z ^ 2 ∂μJ
  exact integral_mono
    (posteriorResamplingSquare_integrable H N hN beta hbeta e F) hb hEach

/-- A constant certified one-link oscillation is evaluated against the
actual normalized original Wilson probability, yielding coefficient 1. -/
theorem originalWilsonPosteriorResamplingEnergy_le_constantLinkOscillation
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (c : ℝ)
    (hc : ∀ z (g : Matrix.specialUnitaryGroup (Fin N) ℂ),
      |F z - F (z.1, Function.update z.2 e g)| ≤ c) :
    posteriorResamplingEnergy H N hN beta hbeta e F ≤ c ^ 2 := by
  letI : IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  have h := originalWilsonPosteriorResamplingEnergy_le_pointwiseLinkOscillation
    H N hN beta hbeta e F (fun _ => c)
    (integrable_const _) (by intro z g; exact hc z g)
  simpa only [integral_const] using h

/-- Actual target-link invariance forces exact vanishing of the ORIGINAL
posterior two-copy energy, independently of any remote Wilson density. -/
theorem originalWilsonPosteriorResamplingEnergy_eq_zero_of_linkInvariant
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (hInv : ∀ z (g : Matrix.specialUnitaryGroup (Fin N) ℂ),
      F (z.1, Function.update z.2 e g) = F z) :
    posteriorResamplingEnergy H N hN beta hbeta e F = 0 := by
  unfold posteriorResamplingEnergy posteriorResamplingSquare
  simp [hInv]

/-- Named ORIGINAL SU(2) physical joint observable of the actual
UNCENTERED fine-right Krylov combination, with frozen beta(n) and
fine orbit beta(n+1) kept distinct. -/
noncomputable def fineRightKrylovOriginalPhysicalJointObservable
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
        (halfExtent (n + 1)) 2 ×
       PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
        (halfExtent (n + 1)) 2) ℝ :=
  normalizedPhysicalOneSlabJointReceiverProductBCF
    (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
    (beta n) (hbeta n)
    (∑ j : Fin (r + 1), a j •
      physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ))

/-- TRUE uncentered original-Wilson right Krylov Rayleigh bound in
terms of genuinely certified physical source/output one-link
oscillations. No global Wilson action, volume factor or mode count is
inserted. Any nonzero variation must be proved for the actual BCF. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_originalLinkOscillation
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (b : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)) → ℝ)
    (hb : ∀ e z (g : Matrix.specialUnitaryGroup (Fin 2) ℂ),
      |fineRightKrylovOriginalPhysicalJointObservable
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a z -
       fineRightKrylovOriginalPhysicalJointObservable
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a (z.1, Function.update z.2 e g)| ≤ b e) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) a) ≤
      (1 / 2 : ℝ) *
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
        (b e) ^ 2) := by
  classical
  let H := halfExtent (n + 1)
  let O := fineRightKrylovOriginalPhysicalJointObservable
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a
  have hRay : star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) a) =
      (1 / 2 : ℝ) *
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) e O) := by
    simpa only [O, fineRightKrylovOriginalPhysicalJointObservable, H] using
      (fineRightKrylovPairHaarResidualGram_rayleigh_eq_half_originalResamplingEnergy
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a)
  have hOne (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) e O ≤ (b e) ^ 2 := by
    apply originalWilsonPosteriorResamplingEnergy_le_constantLinkOscillation
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
      e O (b e)
    intro z g
    exact hb e z g
  calc
    star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) a) =
      (1 / 2 : ℝ) *
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) e O) := hRay
    _ ≤ (1 / 2 : ℝ) *
          (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, (b e) ^ 2) := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro e _he
            exact hOne e
          · norm_num

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
