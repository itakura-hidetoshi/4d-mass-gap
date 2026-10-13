import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalLinkLocalizedTwoRegimeV5_FD
import Mathlib.Tactic

/-!
# P4-Q2-FE: constructive, genuinely link-varying Wilson oscillation profile

FD's global two-regime physical input bound can be compared link-by-link
with the REAL bounded-continuous original Wilson observable's right-link
oscillation. This gives an explicit nonuniform profile using already
constructed finite Wilson link updates, not an assumed decay law.

We retain the same original positive-beta Wilson conditional law and
the correct full signed half-density receiver. The profile may still be
large or non-summable in volume: no decay or continuum gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4Q2FE_topologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2FE_compactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2FE_secondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2FE_measurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2FE_borelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
private noncomputable instance p4Q2FE_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The directly constructed ORIGINAL Wilson right-link BCF oscillation
is a real geometry-sensitive function of the physical link e. -/
noncomputable def p4Q2FE_originalPhysicalRightLinkOscillation
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ‖physicalJointBCFRightLinkDifference H N
    (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) e‖

/-- Exact link-specific original Wilson 2-copy resampling is dominated
by the real original receiver right-link oscillation, with no invented
conditional Haar, locality assumption, or all-links multiplier. -/
theorem p4Q2FE_originalPhysicalLinkDefect_le_actualOscillation
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FD_originalPhysicalLinkDefect H N hN beta hbeta f e ≤
      (1 / 2 : ℝ) *
        (p4Q2FE_originalPhysicalRightLinkOscillation H N hN beta hbeta f e) ^ 2 := by
  let O := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  let c := p4Q2FE_originalPhysicalRightLinkOscillation H N hN beta hbeta f e
  have hOsc : ∀ z (g : Matrix.specialUnitaryGroup (Fin N) ℂ),
      |O z - O (z.1, Function.update z.2 e g)| ≤ c := by
    intro z g
    exact physicalJointBCFRightLinkDifference_abs_le_norm H N O e z g
  have hE := originalWilsonPosteriorResamplingEnergy_le_constantLinkOscillation
    H N hN beta hbeta e O c hOsc
  have hExact := p4Q2FD_originalPhysicalLinkDefect_eq_half_posterior
    H N hN beta hbeta f e
  calc
    p4Q2FD_originalPhysicalLinkDefect H N hN beta hbeta f e =
      (1 / 2 : ℝ) * posteriorResamplingEnergy H N hN beta hbeta e O := hExact
    _ ≤ (1 / 2 : ℝ) * c ^ 2 :=
      mul_le_mul_of_nonneg_left hE (by norm_num)

/-- A *constructed* nonuniform original Wilson spatial-link upper
profile: the smaller of the measured genuine BCF link oscillation and
the universally certified FD posterior two-regime physical bound. -/
noncomputable def p4Q2FE_originalPhysicalLinkUpperProfile
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  min
    ((1 / 2 : ℝ) *
      (p4Q2FE_originalPhysicalRightLinkOscillation H N hN beta hbeta f e) ^ 2)
    (p4Q2FD_originalPhysicalTwoRegimeCoefficient H N hN beta hbeta * ‖f‖ ^ 2)

theorem p4Q2FE_originalPhysicalLinkDefect_le_constructedProfile
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FD_originalPhysicalLinkDefect H N hN beta hbeta f e ≤
      p4Q2FE_originalPhysicalLinkUpperProfile H N hN beta hbeta f e := by
  unfold p4Q2FE_originalPhysicalLinkUpperProfile
  exact le_min
    (p4Q2FE_originalPhysicalLinkDefect_le_actualOscillation H N hN beta hbeta f e)
    (p4Q2FD_originalPhysicalLinkDefect_le_twoRegime H N hN beta hbeta f e)

/-- Fully unconditional nonuniform spatial-link energy budget: sum
the actual link-dependent constructed min bounds before replacing the
physical links by their entire lattice cardinality. -/
theorem p4Q2FE_originalPhysicalPatch_le_constructedProfile
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2FD_originalPhysicalRestrictedLinkEnergy H N hN beta hbeta f S ≤
      S.sum (p4Q2FE_originalPhysicalLinkUpperProfile H N hN beta hbeta f) := by
  unfold p4Q2FD_originalPhysicalRestrictedLinkEnergy
  apply Finset.sum_le_sum
  intro e _he
  exact p4Q2FE_originalPhysicalLinkDefect_le_constructedProfile H N hN beta hbeta f e

/-- The constructed link profile improves (never worsens) FD's
cardinality budget; it can be STRICTLY smaller for nonuniform real
Wilson source oscillations, but no strict inequality is assumed. -/
theorem p4Q2FE_originalPhysicalPatchProfile_le_twoRegimeCard
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    S.sum (p4Q2FE_originalPhysicalLinkUpperProfile H N hN beta hbeta f) ≤
      (S.card : ℝ) *
        p4Q2FD_originalPhysicalTwoRegimeCoefficient H N hN beta hbeta * ‖f‖ ^ 2 := by
  calc
    S.sum (p4Q2FE_originalPhysicalLinkUpperProfile H N hN beta hbeta f) ≤
        S.sum (fun _e =>
          p4Q2FD_originalPhysicalTwoRegimeCoefficient H N hN beta hbeta * ‖f‖ ^ 2) := by
            apply Finset.sum_le_sum
            intro e _he
            exact min_le_right _ _
    _ = (S.card : ℝ) *
          p4Q2FD_originalPhysicalTwoRegimeCoefficient H N hN beta hbeta * ‖f‖ ^ 2 := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            ring

/-- For each arbitrary physical family, the full signed Gram Rayleigh
is controlled by the sum of *actual* link-dependent Wilson BCF
oscillation/two-regime minima of the single combined PHYSICAL input. -/
theorem p4Q2FE_originalWilsonPhysicalGram_rayleigh_le_constructedProfile
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (pairHaarSpatialLinkResidualGram H N hN beta hbeta
        (fun i => normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i))) a) ≤
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        p4Q2FE_originalPhysicalLinkUpperProfile H N hN beta hbeta
          (∑ i : ι, a i • f i) e := by
  classical
  have hRay := pairHaarSpatialLinkResidualGram_rayleigh_physicalInput
    H N hN beta hbeta f a
  have hBound := p4Q2FE_originalPhysicalPatch_le_constructedProfile
    H N hN beta hbeta (∑ i : ι, a i • f i)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  calc
    star a ⬝ᵥ (Matrix.mulVec
      (pairHaarSpatialLinkResidualGram H N hN beta hbeta
        (fun i => normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i))) a) =
      p4Q2FD_originalPhysicalRestrictedLinkEnergy H N hN beta hbeta
        (∑ i : ι, a i • f i) Finset.univ := by
          simpa only [p4Q2FD_originalPhysicalRestrictedLinkEnergy] using hRay
    _ ≤ _ := hBound

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalPhysicalLinkDefect_le_actualOscillation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalPhysicalLinkDefect_le_constructedProfile
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalPhysicalPatch_le_constructedProfile
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalPhysicalPatchProfile_le_twoRegimeCard
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FE_originalWilsonPhysicalGram_rayleigh_le_constructedProfile
