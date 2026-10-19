import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLocalGICompensatedSquareEnergyV5_LY
import Mathlib.Tactic

/-!
# P4-Q2-LZ — exact original Wilson GI local-square-energy variance decomposition

LY proves a cancellation-free local physical-GI lower bound using
  Q = Σ_{p∈genuinePlaquettes} Δbar_p²
rather than only the square of the signed total Δbar_total=Σ_p Δbar_p.

The present theorem identifies, WITHOUT any new detector, physical
source, posterior distribution or rank hypothesis, the exact
finite-volume Euclidean variance decomposition:
  Q/N = (Δbar_total/N)² +
        (1/N) Σ_p (Δbar_p - Δbar_total/N)².

Everything here is an ACTUAL two-context interacting-Wilson GI
matrix element on the ORIGINAL genuine spatial plaquette carrier.
The second term is an exact, nonnegative, cancellation/heterogeneity
component; it is strictly positive if at least one genuine local
GI minor differs from the mean. This separates the signed-global
minor LOSS from decay/dilution of the mean square energy.

Combining with LY, at its identical original real Wilson contexts
and max-square local plaquette p*,
  κ_phys,p* ≥ [ (Δbar_total/N)² + Var(Δbar_p) ] /
               (10 [exp(8b)(exp(16b)-exp(-16b))]²)
while keeping the unchanged original Gauss-law two-source inequality.

Neither variance nor Q/N is proved bounded BELOW uniformly over
lattice H. This is finite-H bookkeeping of a real obstruction,
not H1-C3, continuum Yang–Mills or a mass-gap proof.
No independent-Haar posterior replacement, Dobrushin, synthetic
sources/rank, sorry/admit, or new axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

/-- Pure real finite-set center-of-mass second-moment identity:
the sum of centered squared values equals the raw squared sum minus
twice the mean cross term plus the squared center's cardinality. -/
private theorem p4Q2LZ_sum_centered_sq
    {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    (∑ p : α, (f p - c)^2) =
      (∑ p : α, (f p)^2) -
        2 * c * (∑ p : α, f p) +
          (Fintype.card α : ℝ) * c^2 := by
  classical
  calc
    (∑ p : α, (f p - c)^2) =
        ∑ p : α, ((f p)^2 - (2 * c) * f p + c^2) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = (∑ p : α, (f p)^2) -
          2 * c * (∑ p : α, f p) +
            (Fintype.card α : ℝ) * c^2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- Exact raw-square = mean-square + finite centered variance identity,
with no rank, sign, or positivity constraint on the entries themselves. -/
private theorem p4Q2LZ_finite_mean_variance_identity
    {α : Type*} [Fintype α] (f : α → ℝ)
    (hcard : 0 < (Fintype.card α : ℝ)) :
    (∑ p : α, (f p)^2) / (Fintype.card α : ℝ) =
      ((∑ p : α, f p) / (Fintype.card α : ℝ))^2 +
      (∑ p : α,
        (f p - (∑ q : α, f q) / (Fintype.card α : ℝ))^2) /
          (Fintype.card α : ℝ) := by
  let n : ℝ := (Fintype.card α : ℝ)
  let S : ℝ := ∑ p : α, f p
  let Q : ℝ := ∑ p : α, (f p)^2
  have hn : n ≠ 0 := ne_of_gt hcard
  have hcenter :
      (∑ p : α, (f p - S / n)^2) =
        Q - 2 * (S / n) * S + n * (S / n)^2 := by
    simpa only [S, Q, n] using p4Q2LZ_sum_centered_sq f (S / n)
  change Q / n = (S / n)^2 +
    (∑ p : α, (f p - S / n)^2) / n
  rw [hcenter]
  field_simp [hn]
  ring

end GroundStatePosteriorJoint

local instance p4Q2LZ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LZ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LZ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LZ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LZ_borelSpace :
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
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb
local notation "kappa" => p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb

/-- Mean of ACTUAL compensated original Wilson GI determinants over
the genuine spatial plaquettes at fixed two original Wilson contexts. -/
noncomputable def p4Q2LZ_originalCompensatedLocalGIMean
    (e e' : Link) (z z' : Cfg × Cfg) : ℝ :=
  D e e' z z' / n

local notation "mean" => p4Q2LZ_originalCompensatedLocalGIMean H b hb

/-- Exact original local compensated GI determinant variance,
not a stochastic posterior variance: it is a finite canonical
plaquette-square energy at two genuinely interacting Wilson contexts. -/
noncomputable def p4Q2LZ_originalCompensatedLocalGIVariance
    (e e' : Link) (z z' : Cfg × Cfg) : ℝ :=
  (∑ p : Plaq, (d e e' z z' p - mean e e' z z')^2) / n

local notation "V" => p4Q2LZ_originalCompensatedLocalGIVariance H b hb

/-- Finite geometric variance cannot be negative when the actual
plaquette carrier's cardinality is positive. -/
theorem p4Q2LZ_originalCompensatedLocalGIVariance_nonneg
    (hcount : 0 < n) (e e' : Link) (z z' : Cfg × Cfg) :
    0 ≤ V e e' z z' := by
  unfold p4Q2LZ_originalCompensatedLocalGIVariance
  exact div_nonneg
    (Finset.sum_nonneg fun p hp => sq_nonneg _) hcount.le

/-- A single actual plaquette whose original Wilson GI minor
differs from the true spatial-plaquette mean makes the
cancellation/heterogeneity variance STRICTLY positive. -/
theorem p4Q2LZ_originalCompensatedLocalGIVariance_pos_of_heterogeneous
    (hcount : 0 < n) (e e' : Link) (z z' : Cfg × Cfg)
    (p : Plaq) (hdiff : d e e' z z' p ≠ mean e e' z z') :
    0 < V e e' z z' := by
  have hp : 0 < (d e e' z z' p - mean e e' z z')^2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hdiff)
  have hsum : (d e e' z z' p - mean e e' z z')^2 ≤
      ∑ q : Plaq, (d e e' z z' q - mean e e' z z')^2 := by
    have h : (d e e' z z' p - mean e e' z z')^2 ≤
        ∑ q ∈ (Finset.univ : Finset Plaq),
          (d e e' z z' q - mean e e' z z')^2 :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset Plaq))
        (f := fun q : Plaq => (d e e' z z' q - mean e e' z z')^2)
        (fun q hq => sq_nonneg _)
        (Finset.mem_univ p)
    simpa only [Finset.sum_univ] using h
  change 0 < (∑ q : Plaq,
    (d e e' z z' q - mean e e' z z')^2) / n
  exact div_pos (lt_of_lt_of_le hp hsum) hcount

/-- Exact cancellation-free two-context original GI determinant
energy density equals squared signed-global mean PLUS the actual
nonnegative spatial local-minor variance, with NO new hypothesis
beyond the original nonempty genuine plaquette list. -/
theorem p4Q2LZ_originalCompensatedLocalSquareEnergy_eq_meanSq_add_variance
    (hcount : 0 < n) (e e' : Link) (z z' : Cfg × Cfg) :
    Q e e' z z' / n =
      (mean e e' z z')^2 + V e e' z z' := by
  classical
  have hCard : n = (Fintype.card Plaq : ℝ) := by
    exact_mod_cast p4Q2LQ_originalSpatialPlaquetteCount_eq_card H
  have hnCard : 0 < (Fintype.card Plaq : ℝ) := by
    simpa only [hCard] using hcount
  have hFinite :=
    p4Q2LZ_finite_mean_variance_identity
      (fun p : Plaq => d e e' z z' p) hnCard
  simpa [p4Q2LY_originalCompensatedLocalGISquareEnergy,
    p4Q2LZ_originalCompensatedLocalGIMean,
    p4Q2LZ_originalCompensatedLocalGIVariance,
    p4Q2LY_originalCompensatedGlobalMinor_eq_sum_local,
    hCard] using hFinite

/-- The LY cancellation-free square-energy bound is *strictly*
larger than the signed-global minor-mean square whenever genuine
spatial local-minor heterogeneity has positive variance. -/
theorem p4Q2LZ_originalSquareEnergy_meanSq_strict_of_heterogeneous
    (hcount : 0 < n) (e e' : Link) (z z' : Cfg × Cfg)
    (p : Plaq) (hdiff : d e e' z z' p ≠ mean e e' z z') :
    (mean e e' z z')^2 < Q e e' z z' / n := by
  have hVar : 0 < V e e' z z' :=
    p4Q2LZ_originalCompensatedLocalGIVariance_pos_of_heterogeneous
      H b hb hcount e e' z z' p hdiff
  rw [p4Q2LZ_originalCompensatedLocalSquareEnergy_eq_meanSq_add_variance
    H b hb hcount e e' z z']
  linarith

/-- The original LY finite-volume local GI physical coefficient
floor has an exact, not assumed, mean-squared PLUS heterogeneity
decomposition at the original interacting Wilson contexts. -/
theorem p4Q2LZ_originalLocalGI_squareEnergyFloor_eq_meanVarianceFloor
    (hcount : 0 < n) (hpos : 0 < b)
    (e e' : Link) (z z' : Cfg × Cfg) :
    Q e e' z z' / (n * (10 * E^2)) =
      ((mean e e' z z')^2 + V e e' z z') / (10 * E^2) := by
  have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hc : 0 < 10 * E^2 :=
    mul_pos (by norm_num) (sq_pos_of_pos hE)
  calc
    Q e e' z z' / (n * (10 * E^2)) =
        (Q e e' z z' / n) / (10 * E^2) := by
          field_simp [ne_of_gt hcount, ne_of_gt hc]
    _ = ((mean e e' z z')^2 + V e e' z z') / (10 * E^2) := by
      rw [p4Q2LZ_originalCompensatedLocalSquareEnergy_eq_meanSq_add_variance
        H b hb hcount e e' z z']

/-- The SAME original LM/LP/LX/LY real Wilson contexts and true local
max-square plaquette have this explicit decomposed lower bound on
their ORIGINAL unscaled Gauss-law physical two-source GI coefficient.
No synthetic sources, Dobrushin, or H-uniform lower assumption. -/
theorem p4Q2LZ_originalPhysicalLocalGI_exists_meanVariance_floor
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      0 < n ∧
      0 < kappa e e' z z' p ∧
      0 ≤ V e e' z z' ∧
      ((mean e e' z z')^2 + V e e' z z') / (10 * E^2) ≤
        kappa e e' z z' p ∧
      ∀ x y : ℝ,
        kappa e e' z z' p * (x^2 + y^2) ≤
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  obtain ⟨z, z', p, hp, hn, hQ, hAverage, hκ, hFloor, hOld, hBound⟩ :=
    p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor
      H b hb hpos e e' left₀ right₀
  have hV : 0 ≤ V e e' z z' :=
    p4Q2LZ_originalCompensatedLocalGIVariance_nonneg H b hb hn e e' z z'
  have hEq :=
    p4Q2LZ_originalLocalGI_squareEnergyFloor_eq_meanVarianceFloor
      H b hb hn hpos e e' z z'
  have hDecomposed :
      ((mean e e' z z')^2 + V e e' z z') / (10 * E^2) ≤
        kappa e e' z z' p := by
    rw [← hEq]
    exact hFloor
  exact ⟨z, z', p, hp, hn, hκ, hV, hDecomposed, hBound⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LZ_originalCompensatedLocalGIVariance_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LZ_originalCompensatedLocalGIVariance_pos_of_heterogeneous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LZ_originalCompensatedLocalSquareEnergy_eq_meanSq_add_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LZ_originalSquareEnergy_meanSq_strict_of_heterogeneous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LZ_originalLocalGI_squareEnergyFloor_eq_meanVarianceFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LZ_originalPhysicalLocalGI_exists_meanVariance_floor
