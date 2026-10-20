import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCompensatedGIUniformLocalMomentBoundV5_MA
import Mathlib.Tactic

/-!
# P4-Q2-MB — true Wilson GI energy controls genuinely active plaquette density

P4-Q2-LY/LZ prove the actual ORIGINAL Wilson two-context Gauss-law
GI local-minor square energy Q_{H,b} = ∑_p Δbar_p² is positive at genuine
Wilson posterior witness contexts, and MA gives the exact H-uniform
UPPER estimate Δbar_p² ≤ M_b := (4 E_b²)² = 16 E_b⁴.

Here a genuine spatial plaquette p is called *energy-active* at the
actual finite-H half-mean-square threshold
  τ_{H,b,e,e',z,z'} = Q_{H,b}(e,e',z,z')/(2 N_H)
iff its exact original compensated Wilson GI determinant obeys
  τ ≤ Δbar_p².

This active subset is NOT a synthetic detector/rank, test source,
external distribution or independent Haar posterior: it is literally
a Finset.filter of the original true spatial Wilson plaquette carrier.

For every finite H with N_H>0, MA's genuine local bound gives
  Q ≤ 2 M_b * #{active plaquettes}.
Consequently, when b>0,
  #{active}/N_H ≥ (Q/N_H)/(2 M_b).
At LY's ORIGINAL real positive-energy Wilson boundary contexts, the
right side is strictly positive, without imposing any new lower bound
or active fraction as an axiom.

The remaining open H1-C3 input is to show that *some authentic choice
of Wilson contexts* has Q/N_H bounded BELOW uniformly over H, or a
different argument supplying actual physical endpoint coercivity.
This finite-volume active-density implication itself does NOT show
any positive H-uniform lower bound. No Dobrushin, synthetic source,
independent posterior replacement, sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

/-- Generic finite-amplitude upper tail count, proved by a literal
partition of the actual carrier into true/false threshold predicates.
This is a finite counting inequality, not a probability replacement. -/
private theorem p4Q2MB_finite_sum_le_card_threshold_add_active
    {α : Type*} [Fintype α]
    (f : α → ℝ) (threshold ceiling : ℝ)
    (hthreshold : 0 ≤ threshold)
    (hceiling : ∀ p : α, f p ≤ ceiling) :
    (∑ p : α, f p) ≤
      (Fintype.card α : ℝ) * threshold +
      (((Finset.univ : Finset α).filter
        (fun p => threshold ≤ f p)).card : ℝ) * ceiling := by
  classical
  let s : Finset α := Finset.univ
  let active : Finset α := s.filter (fun p => threshold ≤ f p)
  let passive : Finset α := s.filter (fun p => ¬threshold ≤ f p)
  have hActive : (∑ p ∈ active, f p) ≤
      (active.card : ℝ) * ceiling := by
    have hSum := Finset.sum_le_card_nsmul active f ceiling
      (fun p hp => hceiling p)
    simpa only [nsmul_eq_mul] using hSum
  have hPassive : (∑ p ∈ passive, f p) ≤
      (passive.card : ℝ) * threshold := by
    have hSum := Finset.sum_le_card_nsmul passive f threshold
      (fun p hp => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hp).2))
    simpa only [nsmul_eq_mul] using hSum
  have hCard : (passive.card : ℝ) ≤ (Fintype.card α : ℝ) := by
    have hNat : passive.card ≤ Fintype.card α := by
      calc
        passive.card ≤ s.card := Finset.card_le_card
          (Finset.filter_subset _ _)
        _ = Fintype.card α := Finset.card_univ
    exact_mod_cast hNat
  have hCardTerm : (passive.card : ℝ) * threshold ≤
      (Fintype.card α : ℝ) * threshold :=
    mul_le_mul_of_nonneg_right hCard hthreshold
  have hSplit : (∑ p : α, f p) =
      (∑ p ∈ active, f p) + (∑ p ∈ passive, f p) := by
    simpa only [s, active, passive] using
      (Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset α)
        (fun p : α => threshold ≤ f p) f).symm
  calc
    (∑ p : α, f p) =
        (∑ p ∈ active, f p) + (∑ p ∈ passive, f p) := hSplit
    _ ≤ (active.card : ℝ) * ceiling +
        (passive.card : ℝ) * threshold :=
      add_le_add hActive hPassive
    _ ≤ (Fintype.card α : ℝ) * threshold +
        (active.card : ℝ) * ceiling := by
      linarith

end GroundStatePosteriorJoint

local instance p4Q2MB_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MB_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MB_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MB_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MB_borelSpace :
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

/-- True Wilson GI active spatial plaquettes, selected only by the
actual original squared two-context local GI determinant and its own
half-mean-square energy threshold. No artificial physical source. -/
noncomputable def p4Q2MB_originalActiveGISpatialPlaquettes
    (e e' : Link) (z z' : Cfg × Cfg) : Finset Plaq :=
  Finset.univ.filter (fun p =>
    Q e e' z z' / (2 * n) ≤ (d e e' z z' p)^2)

/-- The complete original Wilson GI local square energy cannot exceed
twice the actual TRUE active-plaquette count times MA's finite-H
uniform one-plaquette ceiling (4 E_b²)² = 16 E_b⁴.
The activity threshold depends on the physical energy density itself;
no volume-independent activity premise is introduced. -/
theorem p4Q2MB_originalGISquareEnergy_le_twice_active_count_amplitude
    (hcount : 0 < n) (e e' : Link) (z z' : Cfg × Cfg) :
    Q e e' z z' ≤
      2 * (4 * E^2)^2 *
        (p4Q2MB_originalActiveGISpatialPlaquettes
          H b hb e e' z z').card := by
  classical
  let ceiling : ℝ := (4 * E^2)^2
  let threshold : ℝ := Q e e' z z' / (2 * n)
  have hQ : 0 ≤ Q e e' z z' :=
    p4Q2LY_originalCompensatedLocalGISquareEnergy_nonneg H b hb e e' z z'
  have hT : 0 ≤ threshold := by
    dsimp [threshold]
    exact div_nonneg hQ
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hcount.le)
  have hUpper : ∀ p : Plaq, (d e e' z z' p)^2 ≤ ceiling := by
    intro p
    exact p4Q2MA_originalCompensatedLocalGIMinor_sq_le_four_contrastSq_sq
      H b hb e e' z z' p
  have hGeneric :=
    p4Q2MB_finite_sum_le_card_threshold_add_active
      (fun p : Plaq => (d e e' z z' p)^2)
      threshold ceiling hT hUpper
  have hCard : n = (Fintype.card Plaq : ℝ) := by
    exact_mod_cast p4Q2LQ_originalSpatialPlaquetteCount_eq_card H
  have hActual : Q e e' z z' ≤
      n * threshold +
        (p4Q2MB_originalActiveGISpatialPlaquettes
          H b hb e e' z z').card * ceiling := by
    simpa [p4Q2LY_originalCompensatedLocalGISquareEnergy,
      p4Q2MB_originalActiveGISpatialPlaquettes, threshold,
      hCard] using hGeneric
  have hHalf : n * threshold = Q e e' z z' / 2 := by
    dsimp [threshold]
    field_simp [ne_of_gt hcount]
    ring
  change Q e e' z z' ≤
    2 * ceiling *
      ((p4Q2MB_originalActiveGISpatialPlaquettes
        H b hb e e' z z').card : ℝ)
  nlinarith [hActual, hHalf]

/-- For positive original Wilson coupling, a fraction at least
(original energy density)/(2 * original squared amplitude ceiling)
of all actual spatial plaquettes have squared GI response at least
half the mean squared GI response.

This converts physical energy retention into physical spatial
delocalization of the response, but does not prove uniform retention. -/
theorem p4Q2MB_originalActiveGI_density_ge_energy_fraction
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg) :
    (Q e e' z z' / n) / (2 * (4 * E^2)^2) ≤
      (p4Q2MB_originalActiveGISpatialPlaquettes
        H b hb e e' z z').card / n := by
  let ceiling : ℝ := (4 * E^2)^2
  let cardReal : ℝ :=
    (p4Q2MB_originalActiveGISpatialPlaquettes
      H b hb e e' z z').card
  have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hCeiling : 0 < ceiling := by
    change 0 < (4 * E^2)^2
    positivity
  have hDen : 0 < 2 * ceiling := mul_pos (by norm_num) hCeiling
  have hBound := p4Q2MB_originalGISquareEnergy_le_twice_active_count_amplitude
    H b hb hcount e e' z z'
  have hRaw : Q e e' z z' / (2 * ceiling) ≤ cardReal :=
    (div_le_iff₀ hDen).2 (by
      change Q e e' z z' ≤ cardReal * (2 * ceiling)
      convert hBound using 1 <;> ring)
  have hAvg : (Q e e' z z' / (2 * ceiling)) / n ≤
      cardReal / n :=
    (div_le_div_iff_of_pos_right hcount).2 hRaw
  change (Q e e' z z' / n) / (2 * ceiling) ≤ cardReal / n
  calc
    (Q e e' z z' / n) / (2 * ceiling) =
        (Q e e' z z' / (2 * ceiling)) / n := by
      field_simp [ne_of_gt hcount, ne_of_gt hDen]
    _ ≤ cardReal / n := hAvg

/-- LY's original genuine interacting-posterior two-context witness
has strictly positive actual mean-square GI energy. At these unchanged
Wilson contexts it also has a quantitatively positive density of
genuine energy-active spatial plaquettes, and the unscaled original
Gauss-law two-source physical coercivity inequality is retained. -/
theorem p4Q2MB_originalPhysicalGI_exists_activePlaquette_density
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      0 < n ∧
      0 < Q e e' z z' / n ∧
      (Q e e' z z' / n) / (2 * (4 * E^2)^2) ≤
        (p4Q2MB_originalActiveGISpatialPlaquettes
          H b hb e e' z z').card / n ∧
      0 < kappa e e' z z' p ∧
      ∀ x y : ℝ,
        kappa e e' z z' p * (x^2 + y^2) ≤
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  obtain ⟨z, z', p, hp, hn, hQ, hAvg, hκ, hFloor, hOld, hBound⟩ :=
    p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor
      H b hb hpos e e' left₀ right₀
  have hEnergyPos : 0 < Q e e' z z' / n := div_pos hQ hn
  have hActivity :=
    p4Q2MB_originalActiveGI_density_ge_energy_fraction
      H b hb hpos hn e e' z z'
  exact ⟨z, z', p, hp, hn, hEnergyPos, hActivity, hκ, hBound⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MB_originalGISquareEnergy_le_twice_active_count_amplitude
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MB_originalActiveGI_density_ge_energy_fraction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MB_originalPhysicalGI_exists_activePlaquette_density
