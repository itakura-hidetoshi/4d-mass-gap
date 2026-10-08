import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveBetaDriftRayleighHilbertCriterion
import Mathlib.Tactic

/-!
# P4: exact constant / constant-orthogonal physical receiver splitting

The canonical physical constant unit u has Haar-L2 norm exactly one.
For every original gauge-invariant physical input f, form the TRUE
Hilbert-space orthogonal component

  f_ortho = f - inner(u,f) • u.

We prove inner(u, f_ortho) = 0, and that the genuine frozen beta-zero
physical receiver V_0 vanishes identically on this component. Thus the
positive-beta receiver drift has the EXACT decomposition

  V_beta f - V_0 f =
    inner(u,f) • (V_beta u - V_0 u) + V_beta f_ortho.

The equality is pushed through the ORIGINAL transported positive-beta
posterior one-link projection without dropping any half-density,
signed receiver, inverse transfer norm, or left/right endpoint
information.

A useful strictly stronger result than the generic two-drift
inequality follows: for physical inputs f with inner(u,f)=0,
the positive-beta full-link residual energy E_beta(f) is EXACTLY
the genuine receiver drift A_beta(f), not merely bounded by
2 * A_beta(f). The same holds for the Rayleigh form of a physical
family whose COMBINED input is orthogonal, whether or not each
family member is individually orthogonal.

This is a finite-volume structural separation, not a volume-uniform
bound on the positive-beta orthogonal sector. No Dobrushin, surrogate
posterior law, or continuum mass-gap assertion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4OrthReceiverTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4OrthReceiverCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4OrthReceiverSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4OrthReceiverMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4OrthReceiverBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4OrthReceiverSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Exact physical Hilbert orthogonal component of the canonical
constant physical unit; this is still an actual gauge-invariant
physical L2 vector, not an altered probability law. -/
noncomputable def physicalConstantOrthogonalComponent
    (H N : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  f - (inner ℝ (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) •
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N

/-- The chosen component is exactly orthogonal to the genuine
norm-one physical constant unit. -/
theorem physicalConstantOrthogonalComponent_inner_zero
    (H N : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
      (physicalConstantOrthogonalComponent H N f) = 0 := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  have hu : ‖u‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N
  change inner ℝ u (f - (inner ℝ u f) • u) = 0
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]
  ring

/-- The original physical input splits exactly into its constant
Fourier coefficient and its true orthogonal physical complement. -/
theorem physicalInput_eq_constant_add_orthogonal
    (H N : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    f =
      (inner ℝ (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) •
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N +
      physicalConstantOrthogonalComponent H N f := by
  unfold physicalConstantOrthogonalComponent
  abel

/-- The genuine frozen beta-zero physical receiver kills EVERY
constant-orthogonal physical input, not just selected basis modes. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_zero_eq_zero_of_constantOrthogonal
    (H N : ℕ) (hN : 0 < N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f = 0) :
    normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f = 0 := by
  rw [normalizedPhysicalOneSlabPairHaarReceiver_zero_rankOne H N hN f, horth]
  simp

/-- In particular the whole orthogonal sector vanishes after the
EXACT beta-zero physical transfer and original pair-Haar pullback. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_zero_orthogonalComponent_eq_zero
    (H N : ℕ) (hN : 0 < N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
      (physicalConstantOrthogonalComponent H N f) = 0 := by
  apply normalizedPhysicalOneSlabPairHaarReceiver_zero_eq_zero_of_constantOrthogonal
  exact physicalConstantOrthogonalComponent_inner_zero H N f

/-- The TRUE signed positive-beta receiver difference has precisely
two physical sectors: a one-dimensional constant-unit drift, plus
the positive-beta receiver applied to the beta-zero-killed orthogonal
physical vector. No assumed operator estimate is hidden. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_minus_zero_eq_constantDrift_add_orthogonalReceiver
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
      normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) •
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) -
          normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)) +
      normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
        (physicalConstantOrthogonalComponent H N f) := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let g := physicalConstantOrthogonalComponent H N f
  let c : ℝ := inner ℝ u f
  let V := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
  let V₀ := normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
  let L := normalizedPhysicalOneSlabPairHaarReceiverLinearMap H N hN beta hbeta
  have hsplit : f = c • u + g :=
    physicalInput_eq_constant_add_orthogonal H N f
  have hlinear : L f = c • L u + L g := by
    rw [hsplit, map_add, map_smul]
  have hV : V f = c • V u + V g := by
    simpa only [L, normalizedPhysicalOneSlabPairHaarReceiverLinearMap_apply] using hlinear
  have hV₀ : V₀ f = c • V₀ u :=
    normalizedPhysicalOneSlabPairHaarReceiver_zero_rankOne H N hN f
  change V f - V₀ f = c • (V u - V₀ u) + V g
  rw [hV, hV₀, smul_sub]
  abel

/-- Original positive-beta posterior RESIDUAL of the true receiver
drift splits into the constant vacuum receiver drift and the
orthogonal-excitation residual, link by link. This is the exact
next analytic interface for non-Dobrushin physical estimates. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_linkDrift_eq_constantDrift_add_orthogonalResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    let δ := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
      normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f
    let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
    let X := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) -
      normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
    let Y := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
      (physicalConstantOrthogonalComponent H N f)
    δ - Q δ =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f) •
        (X - Q X) + (Y - Q Y) := by
  dsimp only
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let c := inner ℝ u f
  let δ := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
    normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
  let X := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta u -
    normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) u
  let Y := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
    (physicalConstantOrthogonalComponent H N f)
  have hδ : δ = c • X + Y :=
    normalizedPhysicalOneSlabPairHaarReceiver_beta_minus_zero_eq_constantDrift_add_orthogonalReceiver
      H N hN beta hbeta f
  have hQadd : Q (c • X + Y) = Q (c • X) + Q Y :=
    pairHaarTransportedGroundStateSpatialLinkProjection_add
      H N hN beta hbeta e (c • X) Y
  have hQsmul : Q (c • X) = c • Q X :=
    pairHaarTransportedGroundStateSpatialLinkProjection_smul
      H N hN beta hbeta e c X
  change δ - Q δ = c • (X - Q X) + (Y - Q Y)
  calc
    δ - Q δ = (c • X + Y) - Q (c • X + Y) := by rw [hδ]
    _ = c • (X - Q X) + (Y - Q Y) := by
      rw [hQadd, hQsmul, smul_sub]
      abel

/-- Crucial strengthening in the constant-ORTHOGONAL sector: the
actual positive-beta full-link physical residual energy is EXACTLY
the receiver drift energy A_beta, with coefficient one rather than
the generic upper-bound factor two. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_fullResidual_eq_receiverDrift_of_orthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f = 0) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f)‖ ^ 2) =
      physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta f := by
  have hzero :=
    normalizedPhysicalOneSlabPairHaarReceiver_zero_eq_zero_of_constantOrthogonal
      H N hN f horth
  simp only [physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy,
    hzero, sub_zero]

/-- EXACT physical Gram Rayleigh form on the orthogonal COMBINED
sector: no factor 2 and no extra positive-beta vacuum term.
The individual physical f_i need not be constant-orthogonal. -/
theorem pairHaarSpatialLinkResidualGram_physicalFamily_rayleigh_eq_receiverDrift_of_combinedOrthogonal
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
            normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i))) a) =
      physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta
        (∑ i : ι, a i • f i) := by
  classical
  have hRay :=
    pairHaarSpatialLinkResidualGram_rayleigh_physicalInput
      H N hN beta hbeta f a
  have hExact :=
    normalizedPhysicalOneSlabPairHaarReceiver_beta_fullResidual_eq_receiverDrift_of_orthogonal
      H N hN beta hbeta (∑ i : ι, a i • f i) horth
  exact hRay.trans hExact

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
