import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUnitReceiverCrossingMinor
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroRankOne
import Mathlib.Tactic

/-!
# P4-Q2-J: unconditional positive-beta physical constant receiver non-retention

The final analytic hypothesis in P4-Q2-I is discharged for the ACTUAL
physical constant-one input. The original one-slab SU(2) Wilson kernel
K_beta(A,B) is strictly positive at every pair (A,B), has a continuous
bounded fixed-B section on compact Haar probability, and its integral
against the actual physical Haar constant unit is strictly positive.

In particular the true normalized transfer receiver at the explicit
identity boundary is positive: no physical sign or pointwise positivity
of an arbitrary L2 quotient is assumed. Combining with the already
proved strict original Wilson crossing minor and P4-Q2-H/I fiber
descent forces the genuine full-link constant-receiver Dirichlet
energy E_unit(beta,H) to be strictly positive whenever beta>0.

This is a qualitative statement at EVERY FINITE spatial H: no uniform
lower bound as H grows, no cross-scale gap and no continuum mass gap.
No Dobrushin, surrogate joint law, new axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4Q2JTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2JLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- A fixed-right section of the ORIGINAL Wilson kernel is integrable
under Haar probability. Use an explicitly typed section map to avoid
expensive implicit elaboration of the finite-group product topology. -/
theorem originalPhysicalWilsonKernel_fixedRight_integrable
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Integrable
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let K : X → ℝ := fun A =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B
  have hKernel :
      Continuous (fun z : X × X =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H 2 beta z.1 z.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H 2 beta
  have hSection : Continuous (fun A : X => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hKContinuous : Continuous K := hKernel.comp hSection
  apply Integrable.of_bound hKContinuous.aestronglyMeasurable 1
  filter_upwards with A
  change ‖K A‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_pos
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 beta A B)]
  exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_le_one
    H 2 (Nat.zero_lt_succ 1) beta hbeta A B

/-- The strictly positive original Wilson kernel has a positive
fixed-right Haar integral for EVERY finite-volume right boundary. -/
theorem originalPhysicalWilsonKernel_fixedRight_integral_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    0 < ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let K : X → ℝ := fun A =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B
  have hKIntegrable : Integrable K μ :=
    originalPhysicalWilsonKernel_fixedRight_integrable H beta hbeta B
  have hKPos : ∀ A : X, 0 < K A := fun A =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H 2 beta A B
  change 0 < ∫ A, K A ∂μ
  rw [integral_pos_iff_support_of_nonneg (fun A => (hKPos A).le) hKIntegrable]
  have hsupp : Function.support K = Set.univ := by
    ext A
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hKPos A).ne'
  rw [hsupp]
  simp [μ]

/-- Raw true physical transfer of canonical constant Haar unit equals
the positive fixed-right Wilson integral, with no pointwise L² quotient
substitution (the Haar constant equality is used only a.e.). -/
theorem originalPhysicalConstantUnitRawTransferAtIdentity_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 <
      decomposableOneSliceTransferIntegral H 2 beta
        ((periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
        (originalWilsonExplicitIdentityBoundary H) := by
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let B := originalWilsonExplicitIdentityBoundary H
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let K : X → ℝ := fun A =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B
  have hu : (u : Lp ℝ 2 μ) = Lp.const 2 μ (1 : ℝ) := by
    change
      ((periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H 2
    exact periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_coe_eq_HaarOneL2
      H 2
  have huAE : (fun A : X => (u : Lp ℝ 2 μ) A) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    rw [hu]
    exact Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ))
  have hIntPos : 0 < ∫ A, K A ∂μ :=
    originalPhysicalWilsonKernel_fixedRight_integral_pos H beta hbeta B
  have hRaw :
      decomposableOneSliceTransferIntegral H 2 beta (u : Lp ℝ 2 μ) B =
        ∫ A, K A ∂μ := by
    unfold decomposableOneSliceTransferIntegral
    apply integral_congr_ae
    filter_upwards [huAE] with A hA
    change K A * (u : Lp ℝ 2 μ) A = K A
    rw [hA]
    ring
  change 0 < decomposableOneSliceTransferIntegral H 2 beta (u : Lp ℝ 2 μ) B
  rw [hRaw]
  exact hIntPos

/-- Strict positivity of the GENUINE normalized constant-input vacuum
receiver at the explicit Wilson identity boundary, based on the original
positive finite-volume transfer kernel integral, not a pointwise claim
about an arbitrary L² representative. -/
theorem normalizedPhysicalOneSlabVacuumReceiverBCF_unit_identity_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < normalizedPhysicalOneSlabVacuumReceiverBCF
      H 2 (Nat.zero_lt_succ 1) beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
      (originalWilsonExplicitIdentityBoundary H) := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let B := originalWilsonExplicitIdentityBoundary H
  have hT :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (Nat.zero_lt_succ 1) beta hbeta‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (Nat.zero_lt_succ 1) beta hbeta
  have hOmega :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (Nat.zero_lt_succ 1) beta hbeta B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H 2 (Nat.zero_lt_succ 1) beta hbeta B
  have hRaw :
      0 < decomposableOneSliceTransferIntegral H 2 beta
        ((u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) B :=
    originalPhysicalConstantUnitRawTransferAtIdentity_pos H beta hbeta
  change 0 <
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (Nat.zero_lt_succ 1) beta hbeta‖⁻¹ *
        decomposableOneSliceTransferIntegral H 2 beta
          (u :
            Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) B) /
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (Nat.zero_lt_succ 1) beta hbeta B
  exact div_pos (mul_pos (inv_pos.mpr hT) hRaw) hOmega

/-- The first unconditional strict positive-beta physical unit-receiver
posterior energy in the ORIGINAL Wilson law. The proof uses the strict
2x2 crossing of the genuine joint Wilson density, the authentic
constant-input normalized-transfer receiver, and nonvanishing of its
strictly positive kernel integral. No uniformity in H is claimed. -/
theorem physicalOriginalUnitReceiverFullLinkEnergy_pos_of_beta_pos_SU2
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    0 < physicalOriginalUnitReceiverFullLinkEnergy
      H 2 (Nat.zero_lt_succ 1) beta (le_of_lt hbeta) := by
  apply physicalOriginalUnitReceiverFullLinkEnergy_pos_of_explicitConstantTransfer_ne_zero
    H beta hbeta
  exact (normalizedPhysicalOneSlabVacuumReceiverBCF_unit_identity_pos
    H beta (le_of_lt hbeta)).ne'

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
