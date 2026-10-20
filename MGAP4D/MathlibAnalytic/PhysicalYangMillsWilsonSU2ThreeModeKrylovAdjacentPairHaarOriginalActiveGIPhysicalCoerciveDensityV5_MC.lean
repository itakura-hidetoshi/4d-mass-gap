import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIActivePlaquetteDensityV5_MB
import Mathlib.Tactic

/-!
# P4-Q2-MC — every genuinely active Wilson GI plaquette has physical Gauss-law coercivity

MB controls the cardinality of the actual original spatial Wilson
plaquettes whose transfer-compensated GI-minor square exceeds half the
actual finite-volume mean square energy. MC now transports this
threshold into the *original physical* two-source Gauss-law inequality,
pointwise for EVERY such active plaquette, rather than an invented
detector or a selected abstract rank.

At any genuine original interacting-posterior contexts with Q > 0 and
N > 0, every MB-active plaquette p has:
  DeltaBar_p^2 >= Q/(2N) > 0,
  kappa_original(p) >= (Q/(2N))/(10 E_b^2) > 0,
and the unchanged true Gauss-law source x U + y W_p U obeys
  kappa_original(p) (x^2+y^2) <= gap(e,z)^2 + gap(e',z')^2.

LY supplies original positive-energy contexts; MB supplies the
quantitatively positive fraction of such physically coercive
plaquettes at those SAME original Wilson contexts. This is a
finite-H theorem. In particular, positivity of Q/N and of the active
fraction is NOT yet uniform in H. No H1-C3 closure, continuum
construction or positive mass gap is claimed.

No Dobrushin route, independent Haar replacement, artificial
distribution/source/rank, extra analytic assumption, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MC_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MC_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MC_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MC_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MC_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "n" => (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
local notation "E" => p4Q2LW_originalHarnackContrastScale b
local notation "d" => p4Q2LW_originalCompensatedLocalGIMinor H b hb
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb
local notation "kappa" => p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb
local notation "active" => p4Q2MB_originalActiveGISpatialPlaquettes H b hb

/-- On EACH genuinely active spatial Wilson plaquette, the exact true
physical Gauss-law coefficient dominates its actual half-mean-square
minor threshold divided by the real 10 E_b^2 Frobenius ceiling.

The proof converts nonzero transfer-compensated GI minors back to the
nonzero original local GI minors using the strictly positive physical
transfer norm; it never changes the original Wilson source or posterior. -/
theorem p4Q2MC_originalEveryActiveGI_hasPhysicalCoercivity
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') (p : Plaq)
    (hp : p ∈ active e e' z z') :
    0 < kappa e e' z z' p ∧
    (Q e e' z z' / (2 * n)) / (10 * E^2) ≤
      kappa e e' z z' p ∧
    ∀ x y : ℝ,
      kappa e e' z z' p * (x^2 + y^2) ≤
        (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
        (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  classical
  have hThreshold :
      Q e e' z z' / (2 * n) ≤ (d e e' z z' p)^2 :=
    (Finset.mem_filter.mp hp).2
  have hThresholdPos : 0 < Q e e' z z' / (2 * n) :=
    div_pos hQ (mul_pos (by norm_num) hcount)
  have hCompSqPos : 0 < (d e e' z z' p)^2 :=
    lt_of_lt_of_le hThresholdPos hThreshold
  have hCompNonzero : d e e' z z' p ≠ 0 :=
    (sq_pos_iff).mp hCompSqPos
  have hOriginalNonzero :
      p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p ≠ 0 := by
    intro hZero
    apply hCompNonzero
    rw [p4Q2LW_originalCompensatedLocalGIMinor_eq_sq_mul_original,
      hZero, mul_zero]
  obtain ⟨hPhysicalPos, hPhysical⟩ :=
    p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
      H b hb e e' z z' p hOriginalNonzero
  have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hc : 0 < 10 * E^2 :=
    mul_pos (by norm_num) (sq_pos_of_pos hE)
  have hThresholdFloor :
      (Q e e' z z' / (2 * n)) / (10 * E^2) ≤
        (d e e' z z' p)^2 / (10 * E^2) :=
    (div_le_div_iff_of_pos_right hc).2 hThreshold
  have hOriginalFloor :=
    p4Q2LY_originalPhysicalLocalGI_ge_compensatedLocal_sq_floor
      H b hb hpos e e' z z' p hOriginalNonzero
  exact ⟨hPhysicalPos, hThresholdFloor.trans hOriginalFloor, hPhysical⟩

/-- Positive true Wilson square energy makes the MB-filtered original
spatial plaquette set nonempty, and the resulting REAL physical
Gauss-law source is coercive on an actual original plaquette. -/
theorem p4Q2MC_originalPositiveGI_hasPhysicalActivePlaquette
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') :
    ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      p ∈ active e e' z z' ∧
      0 < kappa e e' z z' p ∧
      (Q e e' z z' / (2 * n)) / (10 * E^2) ≤
        kappa e e' z z' p ∧
      ∀ x y : ℝ,
        kappa e e' z z' p * (x^2 + y^2) ≤
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  classical
  have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hDen : 0 < 2 * (4 * E^2)^2 := by positivity
  have hRatioPos : 0 < (Q e e' z z' / n) / (2 * (4 * E^2)^2) :=
    div_pos (div_pos hQ hcount) hDen
  have hDensity :=
    p4Q2MB_originalActiveGI_density_ge_energy_fraction
      H b hb hpos hcount e e' z z'
  have hCardRatio : 0 < ((active e e' z z').card : ℝ) / n :=
    lt_of_lt_of_le hRatioPos hDensity
  have hCardPos : 0 < (active e e' z z').card := by
    by_contra hNot
    have hZero : (active e e' z z').card = 0 :=
      Nat.eq_zero_of_not_pos hNot
    rw [hZero] at hCardRatio
    norm_num at hCardRatio
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hCardPos
  have hpOriginal : p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H := by
    change p ∈ (Finset.univ : Finset Plaq).toList
    simp
  obtain ⟨hKappa, hFloor, hPhysical⟩ :=
    p4Q2MC_originalEveryActiveGI_hasPhysicalCoercivity
      H b hb hpos hcount e e' z z' hQ p hp
  exact ⟨p, hpOriginal, hp, hKappa, hFloor, hPhysical⟩

/-- At LY's authentic nonzero original interacting-Wilson contexts,
a quantitatively positive density of the actual ORIGINAL spatial
plaquettes are themselves physical Gauss-law coercivity witnesses.
Neither the density nor the local floor is asserted uniform in H. -/
theorem p4Q2MC_originalPhysicalGI_exists_activeCoerciveDensity
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      0 < n ∧
      0 < Q e e' z z' / n ∧
      (Q e e' z z' / n) / (2 * (4 * E^2)^2) ≤
        (active e e' z z').card / n ∧
      (∃ p : Plaq,
        p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
        p ∈ active e e' z z' ∧
        0 < kappa e e' z z' p ∧
        (Q e e' z z' / (2 * n)) / (10 * E^2) ≤
          kappa e e' z z' p ∧
        ∀ x y : ℝ,
          kappa e e' z z' p * (x^2 + y^2) ≤
            (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
              H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
            (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
              H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2) := by
  obtain ⟨z, z', p₀, hp₀, hn, hQ, hMean, hKappa, hFloor, hOld, hPhysical⟩ :=
    p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor
      H b hb hpos e e' left₀ right₀
  have hActivity :=
    p4Q2MB_originalActiveGI_density_ge_energy_fraction
      H b hb hpos hn e e' z z'
  have hActivePhysical :=
    p4Q2MC_originalPositiveGI_hasPhysicalActivePlaquette
      H b hb hpos hn e e' z z' hQ
  exact ⟨z, z', hn, div_pos hQ hn, hActivity, hActivePhysical⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MC_originalEveryActiveGI_hasPhysicalCoercivity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MC_originalPositiveGI_hasPhysicalActivePlaquette
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MC_originalPhysicalGI_exists_activeCoerciveDensity
