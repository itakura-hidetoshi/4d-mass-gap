import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarExplicitFineRadius
import Mathlib.Tactic

/-!
# P4-Q2-V: what the certified Wilson fine-coupling radius does and does not control

P4-Q2-U introduced the physically grounded **sufficient** radius
  delta(H,r,b) = min(1, R(H,b) / (1 + r Q(H,b))),
where R(H,b) = sqrt(E_unit(H,b)) > 0 and
  Q(H,b) = sqrt(L_H) sqrt(gamma(H,b)) 2 exp(A_H) A_H >= 0.

This file isolates its depth/volume compatibility requirements:

* at fixed physical H,b, delta is antitone in finite Krylov depth r;
* if Q(H,b)>0, then for any epsilon>0 a finite threshold depth exists
  beyond which the certified delta is < epsilon;
* a positive candidate floor epsilon <= delta forces
  epsilon * r * Q(H,b) <= R(H,b).

The last inequality exposes the exact H-dependent missing ratio.
Importantly, this is an obstruction to depth-uniform *certification
by this physical step-error envelope*, NOT a no-go theorem about
the actual positive-fine Wilson Gram, the physical transfer, or a
Yang--Mills mass gap. Positive beta frozen/fine are not conflated.

No Dobrushin, substitute measure, or unproved new axiom is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

/-- A minimal scalar model of P4-Q2-U's physical radius.
The monotonicity result concerns the actual min-quotient expression,
not a statement about the truth of positive-Gram inequalities. -/
theorem p4Q2_min_linear_radius_antitone_depth
    (Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    {r s : ℕ} (hrs : r ≤ s) :
    min 1 (R / (1 + (s : ℝ) * Q)) ≤
      min 1 (R / (1 + (r : ℝ) * Q)) := by
  have hrsReal : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
  have hDenLe : 1 + (r : ℝ) * Q ≤ 1 + (s : ℝ) * Q := by
    have hh := mul_le_mul_of_nonneg_right hrsReal hQ
    linarith
  have hDenR : 0 < 1 + (r : ℝ) * Q := by positivity
  have hDenS : 0 < 1 + (s : ℝ) * Q := by positivity
  have hFraction :
      R / (1 + (s : ℝ) * Q) ≤ R / (1 + (r : ℝ) * Q) := by
    apply (div_le_div_iff₀ hDenS hDenR).mpr
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hDenLe)]
  exact le_min (min_le_left _ _) ((min_le_right _ _).trans hFraction)

/-- A fixed positive step cannot remain inside the P4-Q2-U sufficient
radius at arbitrarily large depth when the frozen-data error factor
Q is positive. This says nothing about the exact Gram for that step. -/
theorem p4Q2_min_linear_radius_eventually_below
    (Q R : ℝ) (hQ : 0 < Q)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r →
      min 1 (R / (1 + (r : ℝ) * Q)) < epsilon := by
  obtain ⟨N, hN⟩ := exists_nat_gt (R / (epsilon * Q))
  refine ⟨N, ?_⟩
  intro r hr
  have hNR : (N : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hScale : 0 < epsilon * Q := mul_pos hEpsilon hQ
  have hLarge : R < (r : ℝ) * (epsilon * Q) :=
    (div_lt_iff₀ hScale).mp (lt_of_lt_of_le hN hNR)
  have hDen : 0 < 1 + (r : ℝ) * Q := by positivity
  have hFraction : R / (1 + (r : ℝ) * Q) < epsilon := by
    apply (div_lt_iff₀ hDen).mpr
    calc
      R < (r : ℝ) * (epsilon * Q) := hLarge
      _ < epsilon * (1 + (r : ℝ) * Q) := by nlinarith
  exact lt_of_le_of_lt (min_le_right _ _) hFraction

/-- Any proposed nonnegative lower floor for the explicit sufficient
radius necessarily bounds r times the physical coefficient Q.
This is the exact compatibility inequality missing in an attempted
depth-uniform certificate. -/
theorem p4Q2_min_linear_radius_floor_forces_budget
    (Q R epsilon : ℝ) (hQ : 0 ≤ Q) (hEpsilon : 0 ≤ epsilon)
    (r : ℕ)
    (hFloor : epsilon ≤ min 1 (R / (1 + (r : ℝ) * Q))) :
    epsilon * ((r : ℝ) * Q) ≤ R := by
  have hDen : 0 < 1 + (r : ℝ) * Q := by positivity
  have hRatio : epsilon ≤ R / (1 + (r : ℝ) * Q) :=
    hFloor.trans (min_le_right _ _)
  have hCross : epsilon * (1 + (r : ℝ) * Q) ≤ R :=
    (le_div_iff₀ hDen).mp hRatio
  calc
    epsilon * ((r : ℝ) * Q) ≤
        epsilon * (1 + (r : ℝ) * Q) := by
      apply mul_le_mul_of_nonneg_left _ hEpsilon
      linarith
    _ ≤ R := hCross

/-- P4-Q2-U's original **physical** action-based explicit radius is
nonincreasing in Krylov depth at any fixed H, nonnegative K and
nonnegative receiver radius. -/
theorem physicalOriginalNormalizedTransferExplicitFineRadius_antitone_depth
    (H : ℕ) (K R : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R)
    {r s : ℕ} (hrs : r ≤ s) :
    physicalOriginalNormalizedTransferExplicitFineRadius H s K R ≤
      physicalOriginalNormalizedTransferExplicitFineRadius H r K R := by
  let Q := K * physicalOriginalNormalizedTransferExpActionLinearConstant H
  have hQ : 0 ≤ Q :=
    mul_nonneg hK (physicalOriginalNormalizedTransferExpActionLinearConstant_nonneg H)
  have h := p4Q2_min_linear_radius_antitone_depth Q R hQ hR hrs
  simpa only [physicalOriginalNormalizedTransferExplicitFineRadius,
    Q, mul_assoc] using h

local instance p4DepthVolumeGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4DepthVolumeCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4DepthVolumeSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4DepthVolumeMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4DepthVolumeBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4DepthVolumeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The actual SU(2) Wilson full-link energy and innovation coefficient
give an H- and frozen-beta-dependent radius that is antitone in depth.
There is no assumption of volume- or depth-independent physical data. -/
theorem physicalOriginalGlobalQuarterEnergyExplicitFineRadius_antitone_depth
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen)
    {r s : ℕ} (hrs : r ≤ s) :
    physicalOriginalGlobalQuarterEnergyExplicitFineRadius
      H s frozen (le_of_lt hFrozen) ≤
    physicalOriginalGlobalQuarterEnergyExplicitFineRadius
      H r frozen (le_of_lt hFrozen) := by
  let K : ℝ :=
    Real.sqrt (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen))
  let R : ℝ := Real.sqrt
    (physicalOriginalUnitReceiverFullLinkEnergy
      H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen))
  have hK : 0 ≤ K :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  change physicalOriginalNormalizedTransferExplicitFineRadius H s K R ≤
    physicalOriginalNormalizedTransferExplicitFineRadius H r K R
  exact physicalOriginalNormalizedTransferExplicitFineRadius_antitone_depth
    H K R hK hR hrs

/-- If the GENUINE fixed-volume/frozen innovation budget factor Q>0,
every fixed positive epsilon eventually exceeds the certified radius
as Krylov depth increases. This is solely a certificate limitation. -/
theorem physicalOriginalGlobalQuarterEnergyExplicitFineRadius_eventually_below
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen)
    (hQ :
      0 <
        (Real.sqrt (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
            H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen))) *
          physicalOriginalNormalizedTransferExpActionLinearConstant H)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r →
      physicalOriginalGlobalQuarterEnergyExplicitFineRadius
        H r frozen (le_of_lt hFrozen) < epsilon := by
  let K : ℝ :=
    Real.sqrt (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen))
  let Q : ℝ := K * physicalOriginalNormalizedTransferExpActionLinearConstant H
  let R : ℝ := Real.sqrt
    (physicalOriginalUnitReceiverFullLinkEnergy
      H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen))
  obtain ⟨N, hN⟩ :=
    p4Q2_min_linear_radius_eventually_below Q R hQ epsilon hEpsilon
  refine ⟨N, ?_⟩
  intro r hr
  have hBound := hN r hr
  change min 1 (R / (1 + (r : ℝ) * K *
    physicalOriginalNormalizedTransferExpActionLinearConstant H)) < epsilon
  simpa only [Q, mul_assoc] using hBound

/-- Any nonnegative lower bound on the certified fine radius forces
a quantitative relation between desired depth r and the true
physical H-dependent action, innovation and receiver budgets. -/
theorem physicalOriginalGlobalQuarterEnergyExplicitFineRadius_floor_forces_budget
    (H r : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen)
    (epsilon : ℝ) (hEpsilon : 0 ≤ epsilon)
    (hFloor : epsilon ≤
      physicalOriginalGlobalQuarterEnergyExplicitFineRadius
        H r frozen (le_of_lt hFrozen)) :
    epsilon * ((r : ℝ) *
      ((Real.sqrt (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
          H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen))) *
        physicalOriginalNormalizedTransferExpActionLinearConstant H)) ≤
      Real.sqrt (physicalOriginalUnitReceiverFullLinkEnergy
        H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)) := by
  let K : ℝ :=
    Real.sqrt (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen))
  let Q : ℝ := K * physicalOriginalNormalizedTransferExpActionLinearConstant H
  let R : ℝ := Real.sqrt
    (physicalOriginalUnitReceiverFullLinkEnergy
      H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen))
  have hQ : 0 ≤ Q :=
    mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (physicalOriginalNormalizedTransferExpActionLinearConstant_nonneg H)
  have hFloor' : epsilon ≤ min 1 (R / (1 + (r : ℝ) * Q)) := by
    convert hFloor using 1
    dsimp [physicalOriginalGlobalQuarterEnergyExplicitFineRadius,
      physicalOriginalNormalizedTransferExplicitFineRadius, Q, K, R]
    congr 1
    ring
  exact p4Q2_min_linear_radius_floor_forces_budget
    Q R epsilon hQ hEpsilon r hFloor'

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
