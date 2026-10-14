import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalTwoBoundaryPosteriorContrastWitnessV5_GS
import Mathlib.Tactic

/-!
# P4-Q2-GT: Haar-positive original signed physical two-boundary witness

GS proved a strictly negative ACTUAL signed physical right-link receiver
difference at a genuine SU(2) pi insertion, conditional on positivity of
the ORIGINAL Wilson transfer of that SAME gauge-invariant physical source.
This statement is pointwise: Haar has no assumed mass at a prescribed
group element.

Here use genuine BOUNDED CONTINUOUS FF response and full-support compact
SU(2) Haar to pass from a single actual point witness to a strictly
positive Haar integral of its SQUARED physical two-left-boundary difference.

The original two left boundaries are identity and the actual linkwise
pi rotation; the receiver is still the genuine original Wilson
half-density normalized physical right-link response, with frozen beta.
Its inner source is the original true one-slab Wilson transfer integral,
and not a free finite-dimensional coefficient vector.

Haar is used ONLY as a positive reference measure for the norm of this
continuous pointwise witness; it is NOT a replacement for the interacting
conditional posterior laws in GI or GN. Hence this Haar-positive
difference is not yet the original GI *two-posterior expectation gap*
Delta or a full physical signed-source frame.

The construction is further specialized to the exact fine right Krylov
and original left three-mode physical sources. Frozen beta(n) in this
Wilson detector and fine beta(n+1) in the sources remain distinct.
No H/r/n-uniform frame, C1/C2/C3 or continuum mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 720000

local instance p4Q2GT_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GT_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GT_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GT_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GT_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2GT_haarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

namespace GroundStatePosteriorJoint

section Frozen

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "μ" => normalizedCompactHaar Gauge

/-- Difference of the two ACTUAL physical signed FF right-link receivers,
at original identity versus actual pi-rotated LEFT Wilson boundaries.
The insertion variable g is arbitrary genuine SU(2). -/
noncomputable def p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
    (f : Phys) (right : Cfg) (e : Link) (g : Gauge) : ℝ :=
  p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      H 2 (by norm_num) beta hbeta f e
      ((originalWilsonExplicitIdentityBoundary H,
        Function.update right e (1 : Gauge)), g) -
    p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      H 2 (by norm_num) beta hbeta f e
      ((p4Q2FQ_originalSU2LeftPiRotationAtLink H e,
        Function.update right e (1 : Gauge)), g)

/-- The TRUE original physical signed receiver difference is continuous
in the updated SU(2) link; no point-mass argument is used. -/
theorem p4Q2GT_originalTwoBoundaryPhysicalSignedResponse_continuous
    (f : Phys) (right : Cfg) (e : Link) :
    Continuous (p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
      H beta hbeta f right e) := by
  let R := p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H 2 (by norm_num) beta hbeta f e
  have h0 : Continuous (fun g : Gauge =>
      R ((originalWilsonExplicitIdentityBoundary H,
        Function.update right e (1 : Gauge)), g)) :=
    R.continuous.comp (continuous_const.prodMk continuous_id)
  have h1 : Continuous (fun g : Gauge =>
      R ((p4Q2FQ_originalSU2LeftPiRotationAtLink H e,
        Function.update right e (1 : Gauge)), g)) :=
    R.continuous.comp (continuous_const.prodMk continuous_id)
  exact h0.sub h1

/-- The squared original signed two-boundary response is integrable
against Haar ONLY as a reference measure, by true BCF continuity. -/
theorem p4Q2GT_originalTwoBoundaryPhysicalSignedResponse_sq_integrable
    (f : Phys) (right : Cfg) (e : Link) :
    Integrable (fun g : Gauge =>
      (p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
        H beta hbeta f right e g) ^ 2) μ := by
  exact ((p4Q2GT_originalTwoBoundaryPhysicalSignedResponse_continuous
    H beta hbeta f right e).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Exact compact-Haar reference squared mass of the ORIGINAL signed
physical two-left-boundary response difference at the actual right link. -/
noncomputable def p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
    (f : Phys) (right : Cfg) (e : Link) : ℝ :=
  ∫ g : Gauge,
    (p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
      H beta hbeta f right e g) ^ 2 ∂μ

theorem p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass_nonneg
    (f : Phys) (right : Cfg) (e : Link) :
    0 ≤ p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
      H beta hbeta f right e := by
  unfold p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
  exact integral_nonneg (fun g => sq_nonneg _)

/-- Exact measured kernel of the ORIGINAL physical signed two-boundary
right receiver, with no source injectivity or frame premise. -/
theorem p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass_zero_iff_ae
    (f : Phys) (right : Cfg) (e : Link) :
    p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
        H beta hbeta f right e = 0 ↔
      ∀ᵐ g ∂μ,
        p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
          H beta hbeta f right e g = 0 := by
  let D := p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
    H beta hbeta f right e
  have hInt : Integrable (fun g : Gauge => (D g) ^ 2) μ :=
    p4Q2GT_originalTwoBoundaryPhysicalSignedResponse_sq_integrable
      H beta hbeta f right e
  have hNonneg : ∀ᵐ g ∂μ, 0 ≤ (D g) ^ 2 :=
    Filter.Eventually.of_forall (fun g => sq_nonneg (D g))
  have hIntegral :
      (∫ g, (D g) ^ 2 ∂μ) = 0 ↔
        (fun g => (D g) ^ 2) =ᵐ[μ] (fun _ => (0 : ℝ)) :=
    integral_eq_zero_iff_of_nonneg_ae hNonneg hInt
  change (∫ g, (D g) ^ 2 ∂μ) = 0 ↔ (∀ᵐ g ∂μ, D g = 0)
  constructor
  · intro hZero
    have hAE := hIntegral.mp hZero
    filter_upwards [hAE] with g hg
    exact sq_eq_zero_iff.mp hg
  · intro hAE
    apply hIntegral.mpr
    filter_upwards [hAE] with g hg
    simp [hg]

/-- Any concrete nonzero value of the SAME continuous original signed
receiver difference produces STRICTLY positive Haar L² mass. This is
topological full support, never a positive Haar atom assumption. -/
theorem p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass_pos_of_witness
    (f : Phys) (right : Cfg) (e : Link) (g0 : Gauge)
    (hWitness :
      p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
        H beta hbeta f right e g0 ≠ 0) :
    0 < p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
      H beta hbeta f right e := by
  let D := p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
    H beta hbeta f right e
  let Q : Gauge → ℝ := fun g => (D g) ^ 2
  have hContD : Continuous D :=
    p4Q2GT_originalTwoBoundaryPhysicalSignedResponse_continuous
      H beta hbeta f right e
  have hContQ : Continuous Q := hContD.pow 2
  have hIntegrable : Integrable Q μ :=
    hContQ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hQNonzero : Q g0 ≠ 0 :=
    pow_ne_zero 2 hWitness
  have hSupportOpen : IsOpen (Function.support Q) := by
    change IsOpen (Q ⁻¹' ({0} : Set ℝ)ᶜ)
    exact isClosed_singleton.isOpen_compl.preimage hContQ
  have hSupportNonempty : (Function.support Q).Nonempty :=
    ⟨g0, hQNonzero⟩
  have hSupportPositive : 0 < μ (Function.support Q) :=
    hSupportOpen.measure_pos μ hSupportNonempty
  change 0 < ∫ g, Q g ∂μ
  rw [integral_pos_iff_support_of_nonneg]
  · exact hSupportPositive
  · intro x
    exact sq_nonneg _
  · exact hIntegrable

/-- GS's explicit genuine SU(2) pi right-insertion witness yields a
strict positive Haar reference mass for the SAME original physical
signed-source two-LEFT-boundary response. -/
theorem p4Q2GT_originalPhysicalSignedTwoBoundaryHaarMass_pos_of_transfer
    (hpos : 0 < beta) (f : Phys) (right : Cfg) (e : Link)
    (hTransfer : 0 <
      decomposableOneSliceTransferIntegral H 2 beta f
        (Function.update right e (specialUnitaryTwoRotation Real.pi))) :
    0 < p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
      H beta hbeta f right e := by
  have hNeg :
      p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
        H beta hbeta f right e (specialUnitaryTwoRotation Real.pi) < 0 :=
    p4Q2GS_originalPhysicalSource_twoBoundaryResponse_strict_neg
      H beta hbeta hpos f right e hTransfer
  exact p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass_pos_of_witness
    H beta hbeta f right e (specialUnitaryTwoRotation Real.pi) (ne_of_lt hNeg)

end Frozen

section ActualAdjacent

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" => physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- The genuine adjacent fine-right Krylov modes have the same strictly
positive Haar-observable signed physical source separation whenever their
actual ORIGINAL frozen Wilson transfer is positive at the explicit
SU(2) pi insertion. There is no abstract replacement source family. -/
theorem p4Q2GT_actualFineRightKrylov_HaarMass_pos_of_transfer
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ) (right : Cfg) (e : Link)
    (hTransfer : 0 <
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Function.update right e (specialUnitaryTwoRotation Real.pi))) :
    0 < p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        right e := by
  have hT : 0 <
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (↑(∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)))
        (Function.update right e (specialUnitaryTwoRotation Real.pi)) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hTransfer
  exact p4Q2GT_originalPhysicalSignedTwoBoundaryHaarMass_pos_of_transfer
    Hn (beta n) (hbeta n) hFrozen _ right e hT

/-- The original three genuine left Gram-Schmidt modes have the same
strict Haar-positive signed receiver certificate for their actual
fine-evolved source combination and FROZEN Wilson target law. -/
theorem p4Q2GT_actualFineLeftThreeMode_HaarMass_pos_of_transfer
    (hFrozen : 0 < beta n) (a : Fin 3 → ℝ) (right : Cfg) (e : Link)
    (hTransfer : 0 <
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ k : Fin 3, a k • LeftFactor n r k)
        (Function.update right e (specialUnitaryTwoRotation Real.pi))) :
    0 < p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
        Hn (beta n) (hbeta n)
        (∑ k : Fin 3, a k • LeftFactor n r k)
        right e := by
  exact p4Q2GT_originalPhysicalSignedTwoBoundaryHaarMass_pos_of_transfer
    Hn (beta n) (hbeta n) hFrozen _ right e hTransfer

end ActualAdjacent

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GT_originalTwoBoundaryPhysicalSignedResponse_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GT_originalTwoBoundaryPhysicalSignedResponse_sq_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass_zero_iff_ae
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass_pos_of_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GT_originalPhysicalSignedTwoBoundaryHaarMass_pos_of_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GT_actualFineRightKrylov_HaarMass_pos_of_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GT_actualFineLeftThreeMode_HaarMass_pos_of_transfer
