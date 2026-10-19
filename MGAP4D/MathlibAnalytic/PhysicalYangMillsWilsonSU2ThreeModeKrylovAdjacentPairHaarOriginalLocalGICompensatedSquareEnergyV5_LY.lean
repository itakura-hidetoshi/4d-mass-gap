import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalTransferNormOneGITrueFloorV5_LX
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# P4-Q2-LY — cancellation-free square energy of genuine local Wilson GI minors

LX proves a true physical Gauss-law local GI lower bound at a selected
plaquette using the SQUARED SIGNED GLOBAL determinant / N_H².
The signed sum may conceal large mutually cancelling local contributions.

We introduce no new measure, rank premise, detector, physical source, or
posterior. At the very SAME pair of ORIGINAL interacting Wilson boundary
contexts and genuine spatial links, take the finite sum of squares of
the actual transfer-compensated original plaquette GI determinants:
  Q_{H,b,e,e',z,z'} = ∑_{p∈OriginalPlaquettes(H)} Δbar_p².
This is a nonnegative, cancellation-free, actual finite-H physical
response quantity, not a hypothetical spatial observability assumption.

An original LP nonzero local minor provides a real plaquette p₀ and
the same genuine contexts. Take an ACTUAL max-square plaquette p*, where
  Δbar_{p*}² ≥ Q/N_H > 0.

LW's exact compensated Frobenius bound ≤ 10 E_b² and LX's true physical
κ_p ≥ compensated κbar_p give
  κ_{p*} ≥ Q/(10 N_H E_b²) > 0,
for the exact unscaled Gauss-law source x U + y W_{H,p*} U.

The pinned mathlib Chebyshev/Cauchy-Schwarz inequality, together with
the previously PROVED original global=local signed-sum equality, yields
  (Δbar_total)² ≤ N_H Q,
so this square-energy floor controls the previous signed-total floor,
without asserting that Δbar_total/N_H itself stays nonzero uniformly.

All statements hold at finite H and fixed b>0; Q/N_H may still vanish
as H increases (e.g. diluted or weak response). H1-C3, continuum YM
and the positive mass gap remain UNPROVED.
No independent-Haar posterior replacement, synthetic source/rank,
Dobrushin hypothesis, sorry/admit, or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

/-- The maximum squared genuine minor dominates the genuine finite
plaquette square-sum average, without requiring consistent minor signs.
A witness already known to be nonzero makes the selected maximum
strictly positive. -/
private theorem p4Q2LY_finite_exists_max_sq
    {α : Type*} [Fintype α] (f : α → ℝ) (p₀ : α)
    (h₀ : f p₀ ≠ 0) :
    ∃ p : α, 0 < (f p)^2 ∧
      (∑ q : α, (f q)^2) ≤ (Fintype.card α : ℝ) * (f p)^2 := by
  classical
  obtain ⟨p, hp, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset α)
      (fun q => (f q)^2) ⟨p₀, Finset.mem_univ p₀⟩
  refine ⟨p, ?_, ?_⟩
  · exact lt_of_lt_of_le (sq_pos_of_ne_zero h₀)
      (hmax p₀ (Finset.mem_univ p₀))
  · have hSum :=
      Finset.sum_le_card_nsmul (Finset.univ : Finset α)
        (fun q => (f q)^2) ((f p)^2)
        (fun q hq => hmax q hq)
    simpa only [Finset.card_univ, nsmul_eq_mul] using hSum

end GroundStatePosteriorJoint

local instance p4Q2LY_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LY_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LY_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LY_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LY_borelSpace :
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
local notation "D" => p4Q2LW_originalCompensatedSpatialGIMinor H b hb
local notation "d" => p4Q2LW_originalCompensatedLocalGIMinor H b hb
local notation "kappa" => p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb

/-- The original transfer-compensated local GI determinant square-sum
on the entire TRUE finite spatial SU(2) plaquette carrier. -/
noncomputable def p4Q2LY_originalCompensatedLocalGISquareEnergy
    (e e' : Link) (z z' : Cfg × Cfg) : ℝ :=
  ∑ p : Plaq, (d e e' z z' p)^2

local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb

/-- The original compensated global determinant is literally the sum
of the same original compensated local plaquette minors. -/
theorem p4Q2LY_originalCompensatedGlobalMinor_eq_sum_local
    (e e' : Link) (z z' : Cfg × Cfg) :
    D e e' z z' = ∑ p : Plaq, d e e' z z' p := by
  rw [p4Q2LW_originalCompensatedSpatialGIMinor_eq_sq_mul_original,
      p4Q2LO_originalSpatialGIMinor_eq_sum_local]
  change
    (p4Q2LW_originalPhysicalTransferNorm H b hb)^2 *
      (((Finset.univ : Finset Plaq).toList.map fun p =>
        p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p).sum) =
      ∑ p : Plaq, d e e' z z' p
  rw [Finset.sum_map_toList]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact (p4Q2LW_originalCompensatedLocalGIMinor_eq_sq_mul_original
    H b hb e e' z z' p).symm

/-- Nonnegative true local compensated determinant square energy,
without any assumption on the SIGNS of the local minor responses. -/
theorem p4Q2LY_originalCompensatedLocalGISquareEnergy_nonneg
    (e e' : Link) (z z' : Cfg × Cfg) :
    0 ≤ Q e e' z z' := by
  unfold p4Q2LY_originalCompensatedLocalGISquareEnergy
  exact Finset.sum_nonneg fun p hp => sq_nonneg _

/-- Pinned mathlib Cauchy-Schwarz/Chebyshev for genuine plaquettes:
the square of the signed original global GI minor is at most
the actual plaquette count times the cancellation-free square energy. -/
theorem p4Q2LY_originalCompensatedGlobalMinor_sq_le_count_mul_energy
    (e e' : Link) (z z' : Cfg × Cfg) :
    (D e e' z z')^2 ≤ n * Q e e' z z' := by
  rw [p4Q2LY_originalCompensatedGlobalMinor_eq_sum_local]
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset Plaq))
    (f := fun p : Plaq => d e e' z z' p)
  simpa [p4Q2LY_originalCompensatedLocalGISquareEnergy,
    p4Q2LQ_originalSpatialPlaquetteCount_eq_card] using hCS

/-- A TRUE nonzero compensated local Wilson GI minor yields a
strictly positive ORIGINAL PHYSICAL κ and explicit sharp local
minor-square lower bound, using LW/LX's Frobenius and transfer estimates. -/
theorem p4Q2LY_originalPhysicalLocalGI_ge_compensatedLocal_sq_floor
    (hpos : 0 < b) (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq)
    (hlocal : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0) :
    (d e e' z z' p)^2 / (10 * E^2) ≤ kappa e e' z z' p := by
  let F : ℝ := p4Q2LW_originalCompensatedLocalGIFrobeniusSq
    H b hb e e' z z' p
  let c : ℝ := 10 * E^2
  have ht : 0 < p4Q2LW_originalPhysicalTransferNorm H b hb :=
    p4Q2LW_originalPhysicalTransferNorm_pos H b hb
  have hFOrig :=
    p4Q2LQ_originalLocalGIFrobeniusSq_pos_of_minor_ne
      H b hb e e' z z' p hlocal
  have hF : 0 < F := by
    change 0 < p4Q2LW_originalCompensatedLocalGIFrobeniusSq H b hb e e' z z' p
    rw [p4Q2LW_originalCompensatedLocalGIFrobeniusSq_eq_sq_mul_original]
    exact mul_pos (sq_pos_of_pos ht) hFOrig
  have hFc : F ≤ c :=
    p4Q2LW_originalCompensatedLocalGIFrobeniusSq_le_ten_contrastSq
      H b hb e e' z z' p
  have hc : 0 < c := by
    change 0 < 10 * E^2
    exact mul_pos (by norm_num) (sq_pos_of_pos
      (p4Q2LW_originalHarnackContrastScale_pos b hpos))
  have hDiv : (d e e' z z' p)^2 / c ≤
      p4Q2LW_originalCompensatedLocalGICoefficient
        H b hb e e' z z' p := by
    change (d e e' z z' p)^2 / c ≤ (d e e' z z' p)^2 / F
    exact (div_le_div_iff₀ hc hF).2
      (mul_le_mul_of_nonneg_left hFc (sq_nonneg _))
  exact hDiv.trans
    (p4Q2LX_originalCompensatedLocalGICoefficient_le_truePhysical
      H b hb e e' z z' p hlocal)

/-- The new cancellation-free square-energy lower bound is always at
least LX's previous signed-global determinant floor at the SAME pair
of original Wilson contexts. No positivity assumption on a local
GI determinant is required for this pure global inequality. -/
theorem p4Q2LY_originalSignedGlobalFloor_le_squareEnergyFloor
    (hcount : 0 < n) (hpos : 0 < b)
    (e e' : Link) (z z' : Cfg × Cfg) :
    (D e e' z z')^2 / (n^2 * (10 * E^2)) ≤
      Q e e' z z' / (n * (10 * E^2)) := by
  let c : ℝ := 10 * E^2
  have hc : 0 < c := by
    change 0 < 10 * E^2
    exact mul_pos (by norm_num) (sq_pos_of_pos
      (p4Q2LW_originalHarnackContrastScale_pos b hpos))
  have hn2 : 0 < n^2 := sq_pos_of_pos hcount
  have hCS := p4Q2LY_originalCompensatedGlobalMinor_sq_le_count_mul_energy
    H b hb e e' z z'
  have hBase : (D e e' z z')^2 / n^2 ≤ Q e e' z z' / n := by
    apply (div_le_div_iff₀ hn2 hcount).2
    calc
      (D e e' z z')^2 * n ≤
          (n * Q e e' z z') * n :=
        mul_le_mul_of_nonneg_right hCS hcount.le
      _ = (Q e e' z z') * n^2 := by ring
  calc
    (D e e' z z')^2 / (n^2 * c) =
        ((D e e' z z')^2 / n^2) / c := by field_simp [ne_of_gt hcount, ne_of_gt hc]
    _ ≤ (Q e e' z z' / n) / c :=
      (div_le_div_iff_of_pos_right hc).2 hBase
    _ = Q e e' z z' / (n * c) := by field_simp [ne_of_gt hcount, ne_of_gt hc]

/-- Finite-volume true Wilson local square-energy witness:
at the LM/LP-established REAL interacting-posterior contexts, select
an ACTUAL genuine plaquette maximizing the square of its compensated
GI minor. Its original unscaled physical coercivity coefficient
dominates the noncancelling square-energy average; all physical
Gauss-law sources and original posterior expectation gaps are retained. -/
theorem p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      0 < n ∧
      0 < Q e e' z z' ∧
      Q e e' z z' / n ≤ (d e e' z z' p)^2 ∧
      0 < kappa e e' z z' p ∧
      Q e e' z z' / (n * (10 * E^2)) ≤
        kappa e e' z z' p ∧
      (D e e' z z')^2 / (n^2 * (10 * E^2)) ≤
        Q e e' z z' / (n * (10 * E^2)) ∧
      ∀ x y : ℝ,
        kappa e e' z z' p * (x^2 + y^2) ≤
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  classical
  obtain ⟨z, z', p₀, hp₀, hn, hp₀Pos, hAvg⟩ :=
    p4Q2LP_originalLocalPlaquetteMinor_exists_averaged
      H b hpos e e' left₀ right₀
  have hLocal₀ :
      p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p₀ ≠ 0 :=
    (abs_pos.mp hp₀Pos)
  have ht : 0 < p4Q2LW_originalPhysicalTransferNorm H b hb :=
    p4Q2LW_originalPhysicalTransferNorm_pos H b hb
  have hComp₀ : d e e' z z' p₀ ≠ 0 := by
    rw [p4Q2LW_originalCompensatedLocalGIMinor_eq_sq_mul_original]
    exact mul_ne_zero (pow_ne_zero 2 ht.ne') hLocal₀
  obtain ⟨p, hMaxPos, hMaxBound⟩ :=
    p4Q2LY_finite_exists_max_sq
      (fun q : Plaq => d e e' z z' q) p₀ hComp₀
  have hNCount : n = (Fintype.card Plaq : ℝ) := by
    exact_mod_cast p4Q2LQ_originalSpatialPlaquetteCount_eq_card H
  have hMaxBound' :
      Q e e' z z' ≤ n * (d e e' z z' p)^2 := by
    simpa [p4Q2LY_originalCompensatedLocalGISquareEnergy, hNCount]
      using hMaxBound
  have hMean : Q e e' z z' / n ≤ (d e e' z z' p)^2 :=
    (div_le_iff₀ hn).2 (by simpa only [mul_comm] using hMaxBound')
  have hSingle : (d e e' z z' p)^2 ≤ Q e e' z z' := by
    unfold p4Q2LY_originalCompensatedLocalGISquareEnergy
    exact Finset.single_le_sum (fun q hq => sq_nonneg _)
      (Finset.mem_univ p)
  have hQPos : 0 < Q e e' z z' := lt_of_lt_of_le hMaxPos hSingle
  have hp : p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H := by
    change p ∈ (Finset.univ : Finset Plaq).toList
    simp
  have hComp : d e e' z z' p ≠ 0 :=
    (sq_pos_iff).mp hMaxPos
  have hLocal : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0 := by
    intro hZero
    apply hComp
    rw [p4Q2LW_originalCompensatedLocalGIMinor_eq_sq_mul_original,
      hZero, mul_zero]
  obtain ⟨hκ, hBound⟩ :=
    p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
      H b hb e e' z z' p hLocal
  have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hc : 0 < 10 * E^2 := mul_pos (by norm_num) (sq_pos_of_pos hE)
  have hFloorLocal :=
    p4Q2LY_originalPhysicalLocalGI_ge_compensatedLocal_sq_floor
      H b hb hpos e e' z z' p hLocal
  have hFloor : Q e e' z z' / (n * (10 * E^2)) ≤
      kappa e e' z z' p := by
    have hDiv : Q e e' z z' / (n * (10 * E^2)) ≤
        (d e e' z z' p)^2 / (10 * E^2) := by
      calc
        Q e e' z z' / (n * (10 * E^2)) =
            (Q e e' z z' / n) / (10 * E^2) := by
              field_simp [ne_of_gt hn, ne_of_gt hc]
        _ ≤ (d e e' z z' p)^2 / (10 * E^2) :=
          (div_le_div_iff_of_pos_right hc).2 hMean
    exact hDiv.trans hFloorLocal
  have hCSFloor := p4Q2LY_originalSignedGlobalFloor_le_squareEnergyFloor
    H b hb hn hpos e e' z z'
  exact ⟨z, z', p, hp, hn, hQPos, hMean, hκ, hFloor, hCSFloor, hBound⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LY_originalCompensatedGlobalMinor_eq_sum_local
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LY_originalCompensatedLocalGISquareEnergy_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LY_originalCompensatedGlobalMinor_sq_le_count_mul_energy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LY_originalPhysicalLocalGI_ge_compensatedLocal_sq_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LY_originalSignedGlobalFloor_le_squareEnergyFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor
