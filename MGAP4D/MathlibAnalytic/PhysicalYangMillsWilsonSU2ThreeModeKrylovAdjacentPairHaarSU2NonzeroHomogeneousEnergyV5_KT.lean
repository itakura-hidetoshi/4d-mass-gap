import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSU2MonomialMomentCompletenessV5_KS
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSU2HomogeneousWilsonHaarMomentGramV5_KP
import Mathlib.Tactic

/-!
# P4-Q2-KT — the ORIGINAL SU(2) Wilson homogeneous Haar energies jointly
# separate every nonzero real continuous source, with positive finite Taylor energy

KS proves that ANY nonzero real continuous source on the actual SU(2)
group has a genuine nonzero finite-degree original matrix-coordinate
monomial Haar moment. KP proves that each degree-n homogeneous original
real matrix-feature Wilson double-Haar quadratic form is exactly a
finite sum of the SQUARES of all those degree-n moments.

We combine them to prove, WITHOUT adding assumptions:
* one nonzero coordinate moment forces STRICT positivity of the matching
  actual Wilson homogeneous Haar energy;
* for every nonzero continuous source SOME homogeneous energy is positive;
* if all homogeneous energies vanish, the source is identically zero;
* for every positive coupling, a finite positive-coefficient Wilson Taylor
  polynomial already has STRICTLY positive Haar quadratic energy.

This is a finite homogeneous and finite Taylor statement. Moving the
finite Taylor energies to the FULL genuine SU(2) Wilson exponential
quadratic form still requires KR's uniform Banach-series convergence
and continuity of genuine double-Haar integration. It is NOT yet
the pointwise original physical GI second-context nonzero theorem,
H1-C3, or a continuum four-dimensional Yang–Mills mass gap.
No independent-Haar posterior, artificial detector rank, sorry or new axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KT_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KT_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KT_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KT_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KT_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section SU2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Coord" => ((Fin 2 × Fin 2) × Bool)
local notation "nu" => normalizedCompactHaar Gauge
local notation "Mono" => p4Q2KN_originalSU2MatrixCoordinateMonomial
local notation "Energy" => p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy

/-- A nonzero moment of an ACTUAL SU(2) real matrix-coordinate monomial
forces strict positivity of the corresponding true homogeneous
original Wilson feature double-Haar quadratic form. -/
theorem p4Q2KT_originalSU2HomogeneousWilsonHaarEnergy_pos_of_monomialMoment_ne
    (ψ : C(Gauge, ℝ)) (n : ℕ) (a : Fin n → Coord)
    (hMoment : (∫ g : Gauge, ψ g * Mono n a g ∂nu) ≠ 0) :
    0 < Energy ψ n := by
  rw [p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy_eq_coordinateMomentSquares]
  have hPositive : 0 < (∫ g : Gauge, ψ g * Mono n a g ∂nu) ^ 2 :=
    sq_pos_of_ne_zero hMoment
  have hLe :
      (∫ g : Gauge, ψ g * Mono n a g ∂nu) ^ 2 ≤
        ∑ k : Fin n → Coord,
          (∫ g : Gauge, ψ g * Mono n k g ∂nu) ^ 2 :=
    Finset.single_le_sum
      (f := fun k : Fin n → Coord =>
        (∫ g : Gauge, ψ g * Mono n k g ∂nu) ^ 2)
      (s := Finset.univ) (fun k hk => sq_nonneg _)
      (Finset.mem_univ a)
  exact lt_of_lt_of_le hPositive hLe

/-- For EVERY nonzero continuous SU(2) signed source there is at
least one finite degree whose ORIGINAL Wilson homogeneous Haar
quadratic energy is STRICTLY positive. The degree is constructed
from KS's nonzero monomial moment, not assumed. -/
theorem p4Q2KT_originalSU2_exists_positive_homogeneousWilsonEnergy
    (ψ : C(Gauge, ℝ)) (hψ : ψ ≠ 0) :
    ∃ n : ℕ, 0 < Energy ψ n := by
  obtain ⟨n, a, ha⟩ :=
    p4Q2KS_originalSU2Haar_exists_nonzero_monomialMoment ψ hψ
  exact ⟨n,
    p4Q2KT_originalSU2HomogeneousWilsonHaarEnergy_pos_of_monomialMoment_ne
      ψ n a ha⟩

/-- The complete family of original nonnegative homogeneous Wilson
Haar quadratic forms is jointly source separating. If every degree
vanishes, the continuous source vanishes pointwise. -/
theorem p4Q2KT_originalSU2_all_homogeneousWilsonEnergies_zero_imp_source_zero
    (ψ : C(Gauge, ℝ))
    (hzero : ∀ n : ℕ, Energy ψ n = 0) :
    ψ = 0 := by
  by_contra hψ
  obtain ⟨n, hn⟩ :=
    p4Q2KT_originalSU2_exists_positive_homogeneousWilsonEnergy ψ hψ
  exact (ne_of_gt hn) (hzero n)

/-- At EVERY fixed positive Wilson parameter, the ORIGINAL Taylor
coefficient of each homogeneous energy is nonnegative. -/
theorem p4Q2KT_originalSU2_positiveWilsonTaylorEnergyTerm_nonneg
    (ψ : C(Gauge, ℝ)) (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    0 ≤ (b ^ n / (Nat.factorial n : ℝ)) * Energy ψ n := by
  exact mul_nonneg
    (div_nonneg (pow_nonneg hb n) (by positivity))
    (p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy_nonneg ψ n)

/-- Already at some FINITE Taylor truncation, with every coefficient
being the ACTUAL positive Wilson inverse-factorial term, the Haar
quadratic energy of any nonzero continuous signed source is STRICTLY
positive. The full exponential limit is a separate (next) theorem. -/
theorem p4Q2KT_originalSU2_exists_positive_finiteWilsonTaylorEnergy
    (ψ : C(Gauge, ℝ)) (hψ : ψ ≠ 0)
    (b : ℝ) (hb : 0 < b) :
    ∃ N : ℕ,
      0 < ∑ n ∈ Finset.range (N + 1),
        (b ^ n / (Nat.factorial n : ℝ)) * Energy ψ n := by
  obtain ⟨N, hEN⟩ :=
    p4Q2KT_originalSU2_exists_positive_homogeneousWilsonEnergy ψ hψ
  refine ⟨N, ?_⟩
  have hCoefficient : 0 < b ^ N / (Nat.factorial N : ℝ) :=
    div_pos (pow_pos hb N) (by positivity)
  have hTerm : 0 < (b ^ N / (Nat.factorial N : ℝ)) * Energy ψ N :=
    mul_pos hCoefficient hEN
  have hLe :
      (b ^ N / (Nat.factorial N : ℝ)) * Energy ψ N ≤
        ∑ n ∈ Finset.range (N + 1),
          (b ^ n / (Nat.factorial n : ℝ)) * Energy ψ n :=
    Finset.single_le_sum
      (f := fun n : ℕ =>
        (b ^ n / (Nat.factorial n : ℝ)) * Energy ψ n)
      (s := Finset.range (N + 1))
      (fun n hn =>
        p4Q2KT_originalSU2_positiveWilsonTaylorEnergyTerm_nonneg
          ψ b hb.le n)
      (Finset.mem_range.mpr (Nat.lt_succ_self N))
  exact lt_of_lt_of_le hTerm hLe

end SU2
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KT_originalSU2HomogeneousWilsonHaarEnergy_pos_of_monomialMoment_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KT_originalSU2_exists_positive_homogeneousWilsonEnergy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KT_originalSU2_all_homogeneousWilsonEnergies_zero_imp_source_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KT_originalSU2_positiveWilsonTaylorEnergyTerm_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KT_originalSU2_exists_positive_finiteWilsonTaylorEnergy
