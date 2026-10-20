import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullPhysicalGapAverageV5_ME
import Mathlib.Tactic

/-!
# P4-Q2-MF — original physical full-spatial gap energy: LINEAR GI-density floor

LY already proves an actual unscaled physical Gauss-law coercivity
coefficient at EVERY original SU(2) Wilson spatial plaquette whose
local genuine compensated two-context GI minor is nonzero:
  kappa_phys(p) >= DeltaBar_p^2 / (10 E_b^2).
The original physical two-posterior signed gap-square R_p(x,y) is
at least kappa_phys(p) * (x^2+y^2). If the same local minor vanishes,
both the desired minor-square lower bound and its physical gap
inequality remain valid by the genuine gap-square nonnegativity.

Instead of MB/MD/ME's active-half-mean threshold and its associated
quadratic loss in Q/N, sum the sharp TRUE local physical inequalities
over *all actual original Wilson spatial plaquettes*, directly:
  [Q_{H,b}/(10 E_b^2)] * (x^2+y^2) <= sum_p R_p(x,y),
where Q_{H,b} = sum_p DeltaBar_p^2 is the exact original physical
interacting-Wilson compensated GI energy of LY. For original N_H>0,
  [(Q_{H,b}/N_H)/(10 E_b^2)] * (x^2+y^2)
       <= (1/N_H) sum_p R_p(x,y).

This is LINEAR rather than quadratic in the real original GI-energy
density Q/N; no artificial observation, rank, independent Haar
posterior, substitute physical source, extra lower-bound hypothesis,
or Dobrushin assumption is introduced. The physical source is the
original p-dependent x U + y W_{H,p} U, and all posterior contexts are
the same authentic interacting-Wilson contexts.

The genuine LY witness makes the coefficient strictly positive at
every fixed finite H, simultaneously for all real x,y, but no
uniform-in-H positive lower bound for Q/N has been proved.
This is NOT endpoint H1-C3, continuum Yang-Mills, or a mass-gap proof.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MF_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MF_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MF_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MF_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MF_borelSpace :
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
local notation "R" =>
  p4Q2MD_originalPlaquettePhysicalTwoSourceGapSquare H b hb

/-- Each ORIGINAL spatial Wilson plaquette carries the genuine
linear local-minor energy floor for its true two-context physical
Gauss-law source, including plaquettes with zero local minor. -/
theorem p4Q2MF_originalPhysicalGap_ge_compensatedLocalMinorSq
    (hpos : 0 < b) (e e' : Link) (z z' : Cfg × Cfg)
    (p : Plaq) (x y : ℝ) :
    (d e e' z z' p)^2 / (10 * E^2) * (x^2 + y^2) ≤
      R e e' z z' p x y := by
  by_cases hd : d e e' z z' p = 0
  · simpa [hd] using
      (p4Q2ME_originalPhysicalPlaquetteGapSquare_nonneg
        H b hb e e' z z' p x y)
  · have hOriginal :
        p4Q2LO_originalLocalPlaquetteGIMinor
          H b hb e e' z z' p ≠ 0 := by
      intro hZero
      apply hd
      rw [p4Q2LW_originalCompensatedLocalGIMinor_eq_sq_mul_original,
        hZero, mul_zero]
    have hFloor :=
      p4Q2LY_originalPhysicalLocalGI_ge_compensatedLocal_sq_floor
        H b hb hpos e e' z z' p hOriginal
    obtain ⟨_, hPhysical⟩ :=
      p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
        H b hb e e' z z' p hOriginal
    have hSource : 0 ≤ x^2 + y^2 := by positivity
    exact (mul_le_mul_of_nonneg_right hFloor hSource).trans
      (hPhysical x y)

/-- Direct summation of the actual original p-dependent physical
Gauss-law two-source gaps gives a LINEAR original GI square-energy
floor, without any active-plaquette truncation or density loss. -/
theorem p4Q2MF_originalFullPhysicalGapSum_ge_linearGI
    (hpos : 0 < b) (e e' : Link) (z z' : Cfg × Cfg)
    (x y : ℝ) :
    Q e e' z z' / (10 * E^2) * (x^2 + y^2) ≤
      (∑ p : Plaq, R e e' z z' p x y) := by
  classical
  have hLocalSum :
      (∑ p : Plaq, ((d e e' z z' p)^2 / (10 * E^2)) *
        (x^2 + y^2)) ≤ (∑ p : Plaq, R e e' z z' p x y) :=
    Finset.sum_le_sum (fun p _ =>
      p4Q2MF_originalPhysicalGap_ge_compensatedLocalMinorSq
        H b hb hpos e e' z z' p x y)
  have hPullConstants :
      (∑ p : Plaq, ((d e e' z z' p)^2 / (10 * E^2)) *
        (x^2 + y^2)) =
      ((∑ p : Plaq, (d e e' z z' p)^2) /
        (10 * E^2)) * (x^2 + y^2) := by
    simp only [Finset.sum_mul, Finset.sum_div]
  change (∑ p : Plaq, (d e e' z z' p)^2) /
    (10 * E^2) * (x^2 + y^2) ≤
    (∑ p : Plaq, R e e' z z' p x y)
  exact hPullConstants ▸ hLocalSum

/-- The FULL original Wilson spatial physical-source gap-square
AVERAGE has a strictly stronger LINEAR rather than quadratic
finite-volume GI energy-density floor. -/
theorem p4Q2MF_originalFullPhysicalGapAverage_ge_linearGI
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg) (x y : ℝ) :
    (Q e e' z z' / n) / (10 * E^2) * (x^2 + y^2) ≤
      (∑ p : Plaq, R e e' z z' p x y) / n := by
  have hSum :=
    p4Q2MF_originalFullPhysicalGapSum_ge_linearGI
      H b hb hpos e e' z z' x y
  have hAverage :=
    (div_le_div_iff_of_pos_right hcount).2 hSum
  calc
    (Q e e' z z' / n) / (10 * E^2) * (x^2 + y^2) =
        (Q e e' z z' / (10 * E^2) * (x^2 + y^2)) / n := by
      ring
    _ ≤ (∑ p : Plaq, R e e' z z' p x y) / n := hAverage

/-- Strict positive original physical spatial gap response for every
nonzero REAL Gauss-law source coefficient pair whenever the genuine
Wilson compensated GI square energy is positive at the contexts. -/
theorem p4Q2MF_originalFullPhysicalGapAverage_pos
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') (x y : ℝ)
    (hSource : 0 < x^2 + y^2) :
    0 < (∑ p : Plaq, R e e' z z' p x y) / n := by
  have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hc : 0 < 10 * E^2 :=
    mul_pos (by norm_num) (sq_pos_of_pos hE)
  have hFloorPos :
      0 < (Q e e' z z' / n) / (10 * E^2) * (x^2 + y^2) :=
    mul_pos (div_pos (div_pos hQ hcount) hc) hSource
  exact lt_of_lt_of_le hFloorPos
    (p4Q2MF_originalFullPhysicalGapAverage_ge_linearGI
      H b hb hpos hcount e e' z z' x y)

/-- The authentic original LY interacting-Wilson witness pair gives
ONE explicit strictly positive finite-volume coefficient at the
SAME genuine contexts simultaneously for ALL real x,y, controlling
the TRUE spatial average of original p-dependent Gauss-law sources.
No uniform-in-H positive energy-density lower bound is asserted. -/
theorem p4Q2MF_originalPhysicalGI_exists_fullSpatialLinearFloor
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      0 < n ∧
      0 < Q e e' z z' / n ∧
      ∃ c : ℝ, 0 < c ∧ ∀ x y : ℝ,
        c * (x^2 + y^2) ≤
          (∑ p : Plaq, R e e' z z' p x y) / n := by
  obtain ⟨z, z', _, _, hn, hQ, _, _, _, _, _⟩ :=
    p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor
      H b hb hpos e e' left₀ right₀
  have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hc : 0 < 10 * E^2 :=
    mul_pos (by norm_num) (sq_pos_of_pos hE)
  have hMean : 0 < Q e e' z z' / n := div_pos hQ hn
  have hLinearPos :
      0 < (Q e e' z z' / n) / (10 * E^2) :=
    div_pos hMean hc
  refine ⟨z, z', hn, hMean, _, hLinearPos, ?_⟩
  intro x y
  exact p4Q2MF_originalFullPhysicalGapAverage_ge_linearGI
    H b hb hpos hn e e' z z' x y

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MF_originalPhysicalGap_ge_compensatedLocalMinorSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MF_originalFullPhysicalGapSum_ge_linearGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MF_originalFullPhysicalGapAverage_ge_linearGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MF_originalFullPhysicalGapAverage_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MF_originalPhysicalGI_exists_fullSpatialLinearFloor
