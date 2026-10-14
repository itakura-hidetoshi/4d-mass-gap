import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalIntegratedLinkMassRealHaarSandwichV5_FT
import Mathlib.Tactic

/-!
# P4-Q2-FW: exact criterion for volume-uniform TRUE Wilson RMS summability

FG/FH define original source- and link-resolved genuine Wilson conditional
RMS means m_e(f). FT proves their sums over any original physical finite
link patch S lie between exp(±16 beta) times the SAME literal signed
response's paired Haar comparison moments.

For any fixed gauge rank N>0, arbitrary family of actual gauge-invariant
physical source vectors f_H, selectable actual spatial link patches S_H,
and a nonnegative sequence of FROZEN physical Wilson couplings
0 <= beta_H <= B, we now prove the genuine volume-uniform boundedness
criterion:

  (exists C, forall H, sum_{e in S_H} m_e(H,f_H) <= C)
    IFF
  (exists D, forall H, sum_{e in S_H} HaarMoment_e(H,f_H) <= D).

The exact transfer factor already absorbed in the physical signed response
is unchanged. This is an equivalence of ACTUAL Wilson conditional RMS
versus analytic Haar comparison on the SAME response, not a substitution
of the inner interacting posterior.

The proof DOES NOT produce either bound; in particular no spatial
locality, all-link positive lower frame, cross-scale control, physical
energy after inverse-transfer rescaling, or continuum Yang--Mills mass
gap is asserted. For unbounded beta_H, no uniform equivalence is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 650000

private noncomputable instance p4Q2FW_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Original Wilson/FH physical RMS spatial mass is volume-uniformly
bounded on the chosen TRUE spatial-link patches exactly when the FT
Haar-signed-response mass is. We allow a variable beta_H, requiring
only a common explicit upper coupling bound. -/
theorem p4Q2FW_originalWilsonVolumeUniformRMSMass_iff_signedHaarMass
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ H : ℕ, 0 ≤ beta H)
    (B : ℝ) (hBetaBound : ∀ H : ℕ, beta H ≤ B)
    (f : ∀ H : ℕ,
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : ∀ H : ℕ, Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    (∃ C : ℝ, ∀ H : ℕ,
      p4Q2FH_originalWilsonSpatialRMSMass
        H N hN (beta H) (hbeta H) (f H) (S H) ≤ C) ↔
    (∃ D : ℝ, ∀ H : ℕ,
      p4Q2FT_originalWilsonSignedHaarSpatialMass
        H N hN (beta H) (hbeta H) (f H) (S H) ≤ D) := by
  let W : ℕ → ℝ := fun H =>
    p4Q2FH_originalWilsonSpatialRMSMass
      H N hN (beta H) (hbeta H) (f H) (S H)
  let A : ℕ → ℝ := fun H =>
    p4Q2FT_originalWilsonSignedHaarSpatialMass
      H N hN (beta H) (hbeta H) (f H) (S H)
  have hNonneg (H : ℕ) : 0 ≤ A H := by
    dsimp [A, p4Q2FT_originalWilsonSignedHaarSpatialMass]
    exact Finset.sum_nonneg (fun e _he =>
      p4Q2FT_originalWilsonSignedHaarOuterLinkMean_nonneg
        H N hN (beta H) (hbeta H) (f H) e)
  have hSandwich (H : ℕ) :
      Real.exp (-16 * beta H) * A H ≤ W H ∧
      W H ≤ Real.exp (16 * beta H) * A H :=
    p4Q2FT_originalWilsonSpatialMass_real_haar_sandwich
      H N hN (beta H) (hbeta H) (f H) (S H)
  have hExpLower (H : ℕ) :
      Real.exp (-16 * B) ≤ Real.exp (-16 * beta H) := by
    exact Real.exp_le_exp.mpr (by nlinarith [hBetaBound H])
  have hExpUpper (H : ℕ) :
      Real.exp (16 * beta H) ≤ Real.exp (16 * B) := by
    exact Real.exp_le_exp.mpr (by nlinarith [hBetaBound H])
  have hCancel :
      Real.exp (16 * B) * Real.exp (-16 * B) = 1 := by
    rw [← Real.exp_add]
    have hz : (16 : ℝ) * B + -16 * B = 0 := by ring
    rw [hz, Real.exp_zero]
  change (∃ C : ℝ, ∀ H : ℕ, W H ≤ C) ↔
    (∃ D : ℝ, ∀ H : ℕ, A H ≤ D)
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨Real.exp (16 * B) * C, ?_⟩
    intro H
    have hLo :
        Real.exp (-16 * B) * A H ≤ C := by
      calc
        Real.exp (-16 * B) * A H ≤
            Real.exp (-16 * beta H) * A H :=
          mul_le_mul_of_nonneg_right (hExpLower H) (hNonneg H)
        _ ≤ W H := (hSandwich H).1
        _ ≤ C := hC H
    have hScaled := mul_le_mul_of_nonneg_left hLo (Real.exp_pos (16 * B)).le
    simpa [mul_assoc, hCancel] using hScaled
  · rintro ⟨D, hD⟩
    refine ⟨Real.exp (16 * B) * D, ?_⟩
    intro H
    calc
      W H ≤ Real.exp (16 * beta H) * A H := (hSandwich H).2
      _ ≤ Real.exp (16 * B) * A H :=
        mul_le_mul_of_nonneg_right (hExpUpper H) (hNonneg H)
      _ ≤ Real.exp (16 * B) * D :=
        mul_le_mul_of_nonneg_left (hD H) (Real.exp_pos _).le

/-- The same exact volume-uniform criterion for the ENTIRE original
finite-volume spatial-link carrier, with no arbitrary selection of
a small patch or density surrogate. -/
theorem p4Q2FW_originalWilsonFullSpatialRMSVolumeUniform_iff_Haar
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ H : ℕ, 0 ≤ beta H)
    (B : ℝ) (hBetaBound : ∀ H : ℕ, beta H ≤ B)
    (f : ∀ H : ℕ,
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∃ C : ℝ, ∀ H : ℕ,
      p4Q2FH_originalWilsonSpatialRMSMass H N hN
        (beta H) (hbeta H) (f H)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≤ C) ↔
    (∃ D : ℝ, ∀ H : ℕ,
      p4Q2FT_originalWilsonSignedHaarSpatialMass H N hN
        (beta H) (hbeta H) (f H)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≤ D) := by
  exact p4Q2FW_originalWilsonVolumeUniformRMSMass_iff_signedHaarMass
    N hN beta hbeta B hBetaBound f
    (fun H => (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))

/-- The UNBOUNDED mass question is equivalently unbounded on the TRUE
Wilson side and its SAME-RESPONSE Haar moment side for bounded beta.
Thus any rigorous no-summability witness transfers in both directions. -/
theorem p4Q2FW_originalWilsonVolumeUniformUnbounded_iff_HaarUnbounded
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ H : ℕ, 0 ≤ beta H)
    (B : ℝ) (hBetaBound : ∀ H : ℕ, beta H ≤ B)
    (f : ∀ H : ℕ,
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : ∀ H : ℕ, Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    (¬ ∃ C : ℝ, ∀ H : ℕ,
      p4Q2FH_originalWilsonSpatialRMSMass
        H N hN (beta H) (hbeta H) (f H) (S H) ≤ C) ↔
    (¬ ∃ D : ℝ, ∀ H : ℕ,
      p4Q2FT_originalWilsonSignedHaarSpatialMass
        H N hN (beta H) (hbeta H) (f H) (S H) ≤ D) := by
  exact not_congr
    (p4Q2FW_originalWilsonVolumeUniformRMSMass_iff_signedHaarMass
      N hN beta hbeta B hBetaBound f S)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FW_originalWilsonVolumeUniformRMSMass_iff_signedHaarMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FW_originalWilsonFullSpatialRMSVolumeUniform_iff_Haar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FW_originalWilsonVolumeUniformUnbounded_iff_HaarUnbounded
