import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCharacterPowerCoordinateExpansionV5_NV
import Mathlib.Tactic

/-!
# P4-Q2-NW — genuine Wilson–Perron signed double energy at every finite Fock degree

NV proved an EXACT expansion of every power of the ORIGINAL temporal
SU(2) Wilson character into all ordered finite products of the genuine
real-eight matrix coordinates J. NU proved the ORIGINAL signed two-Wilson-
posterior Perron-minus-Dirac source has a strictly positive finite degree
coordinate-energy E_n for at least one n, without any assumed rank.

NW crosses the signed integration boundary at EACH FINITE DEGREE:

  S_n(x) = L_g(chi(x,g)^n)
         = 2^(-n) Σ_q m_q(x) L(m_q),

  B_n = L_x(S_n(x)) = 2^(-n) Σ_q L(m_q)^2 >= 0,

where L(f)=∫f(g)rho(g)dHaar(g)-c f(y) is the same NJ authentic bounded
Wilson–Perron signed functional. In particular, S_n is a genuinely
CONTINUOUS function on the actual full SU(2), and the outer integral
is integrable by compactness and the original rho continuity.

The complete finite-degree Wilson Taylor double energy is a sum of
strictly positive b^n/n! weights of these genuine signed double
pairings. Some sufficiently large finite truncation is STRICTLY
positive for every original beta>0 signed source, by NU/NV.

Still OPEN: convergence of finite Taylor double energies to the
ACTUAL full exponential Wilson double energy (a uniform Banach-series/
bounded signed bilinear operator assertion). Hence NO unconditional
positive full Gaussian signed energy or kernel-span density is claimed.
No artificial signed measure, physical source, posterior or Perron
modification, Dobrushin, sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NW_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NW_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NW_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NW_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NW_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Index" => (Fin 2 × Fin 2) × Bool
local notation "chi" => p4Q2NG_originalSU2TemporalCharacter
local notation "mon" => p4Q2NU_originalRealEightCoordinateProduct

/-- GENUINE SU2 signed n-th character transform in continuous-function
form. Finite scalar and coordinate sums make continuity explicit. -/
noncomputable def p4Q2NW_originalSignedPowerMomentSection
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (n : ℕ) : C(Gauge, ℝ) :=
  (1 / 2 : ℝ)^n •
    (∑ q : Fin n → Index,
      (L (mon n q)) • mon n q)

/-- The polynomial section is exactly application of the SAME bounded
signed functional to the original Wilson character power, at every
x in actual SU(2). No integration interchange is used. -/
theorem p4Q2NW_originalSignedPowerMomentSection_apply
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (n : ℕ) (x : Gauge) :
    p4Q2NW_originalSignedPowerMomentSection L n x =
      L ((p4Q2NL_originalTemporalCharacterContinuous x)^n) := by
  let m : (Fin n → Index) → C(Gauge, ℝ) := mon n
  have hSection :
      (p4Q2NL_originalTemporalCharacterContinuous x)^n =
        (1 / 2 : ℝ)^n •
          (∑ q : Fin n → Index, (m q x) • m q) := by
    ext g
    change (chi x g)^n =
      ((1 / 2 : ℝ)^n • (∑ q : Fin n → Index, (m q x) • m q)) g
    rw [p4Q2NV_originalTemporalCharacter_power_eq_coordinateGram n x g]
    simp only [ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul]
    rfl
  change ((1 / 2 : ℝ)^n •
      (∑ q : Fin n → Index, (L (m q)) • m q)) x =
      L ((p4Q2NL_originalTemporalCharacterContinuous x)^n)
  rw [hSection]
  simp only [ContinuousMap.smul_apply, ContinuousMap.sum_apply,
    map_smul, map_sum, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- Finite degree real signed double Gram pairing equals the actual
positive sum of squares of the original SU(2) coordinate moments. -/
theorem p4Q2NW_originalSignedPowerMomentSection_pairEnergy
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (n : ℕ) :
    L (p4Q2NW_originalSignedPowerMomentSection L n) =
      (1 / 2 : ℝ)^n *
        p4Q2NU_originalSignedCoordinateEnergy L n := by
  unfold p4Q2NW_originalSignedPowerMomentSection
    p4Q2NU_originalSignedCoordinateEnergy
    p4Q2NU_originalSignedCoordinateMoment
  simp only [map_smul, map_sum, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- The ORIGINAL double signed Wilson–Perron character power pairing:
the outer signed rho-minus-Dirac action on the authentic INNER signed
Haar character power transform, computed via the finite polynomial
section above. It is an actual iterated real Haar integral. -/
noncomputable def p4Q2NW_originalWilsonPerronSignedPowerDoubleEnergy
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) (n : ℕ) : ℝ :=
  let L := p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c
  let S := p4Q2NW_originalSignedPowerMomentSection L n
  (∫ x : Gauge,
    S x * p4Q2NG_originalSpatialPerronSignedContrast H b hb e z x
      ∂normalizedCompactHaar Gauge) - c * S y

/-- Authentic INNER Wilson character-power integration, including
the original Haar rho density and the same real Dirac subtraction.
The finite SU2 coordinate expression is not a substitute source. -/
theorem p4Q2NW_originalWilsonPerronSignedPowerMomentSection_apply
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) (n : ℕ) (x : Gauge) :
    p4Q2NW_originalSignedPowerMomentSection
      (p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c) n x =
        (∫ g : Gauge,
          (chi x g)^n *
            p4Q2NG_originalSpatialPerronSignedContrast H b hb e z g
            ∂normalizedCompactHaar Gauge) -
          c * (chi x y)^n := by
  rw [p4Q2NW_originalSignedPowerMomentSection_apply,
    p4Q2NJ_originalSignedDiracDefectCLM_apply]
  rfl

/-- The actual OUTER Haar product in the genuine power double energy
is integrable, because NW's inner signed character section is an
honest continuous function and NI proved original rho continuous. -/
theorem p4Q2NW_originalWilsonPerronSignedPowerOuter_integrable
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) (n : ℕ) :
    Integrable (fun x : Gauge =>
      p4Q2NW_originalSignedPowerMomentSection
          (p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c) n x *
        p4Q2NG_originalSpatialPerronSignedContrast H b hb e z x)
      (normalizedCompactHaar Gauge) := by
  have hCont : Continuous (fun x : Gauge =>
      p4Q2NW_originalSignedPowerMomentSection
          (p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c) n x *
        p4Q2NG_originalSpatialPerronSignedContrast H b hb e z x) :=
    (p4Q2NW_originalSignedPowerMomentSection
      (p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c) n).continuous.mul
        (p4Q2NI_originalSpatialPerronSignedContrast_continuous
          H b hb e z)
  exact hCont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Exact finite-degree TWO-FOLD genuine signed Haar character power
identity: the double signed rho-minus-Dirac kernel pairing equals the
strictly nonnegative sum of squares of the same NU genuine moments.
No Bochner/Fubini or infinite-series interchange is required. -/
theorem p4Q2NW_originalWilsonPerronSignedPowerDoubleEnergy_eq
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) (n : ℕ) :
    p4Q2NW_originalWilsonPerronSignedPowerDoubleEnergy
        H b hb e z y c n =
      (1 / 2 : ℝ)^n *
        p4Q2NU_originalWilsonPerronSignedCoordinateEnergy
          H b hb e z y c n := by
  change
    p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c
      (p4Q2NW_originalSignedPowerMomentSection
        (p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c) n) =
      (1 / 2 : ℝ)^n *
        p4Q2NU_originalWilsonPerronSignedCoordinateEnergy
          H b hb e z y c n
  rw [p4Q2NW_originalSignedPowerMomentSection_pairEnergy]
  rw [p4Q2NU_originalWilsonPerron_signedCoordinateEnergy_eq]

/-- All original signed Wilson character-power double energies are
NONNEGATIVE, without a genuine signed-measure positivity hypothesis. -/
theorem p4Q2NW_originalWilsonPerronSignedPowerDoubleEnergy_nonneg
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) (n : ℕ) :
    0 ≤ p4Q2NW_originalWilsonPerronSignedPowerDoubleEnergy
      H b hb e z y c n := by
  rw [p4Q2NW_originalWilsonPerronSignedPowerDoubleEnergy_eq]
  exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n)
    (p4Q2NU_originalSignedCoordinateEnergy_nonneg
      (p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c) n |>.trans_eq
        (p4Q2NU_originalWilsonPerron_signedCoordinateEnergy_eq
          H b hb e z y c n).symm)

/-- Finite Taylor signed double energy of the TRUE temporal Wilson
character, using the actual two posterior difference and Perron
factor, with no replacement density. -/
noncomputable def p4Q2NW_originalWilsonPerronSignedTaylorDoubleEnergy
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) (degree : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (degree + 1),
    (b ^ n / (n.factorial : ℝ)) *
      p4Q2NW_originalWilsonPerronSignedPowerDoubleEnergy
        H b hb e z y c n

/-- Exact finite Fock signed Taylor equality: each real SU2 original
signed Wilson temporal power has been integrated twice via the
ACTUAL rho-minus-Dirac functional, yielding positive square moments. -/
theorem p4Q2NW_originalWilsonPerronSignedTaylorDoubleEnergy_eq_coordinateSum
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) (degree : ℕ) :
    p4Q2NW_originalWilsonPerronSignedTaylorDoubleEnergy
        H b hb e z y c degree =
      ∑ n ∈ Finset.range (degree + 1),
        ((b / 2)^n / (n.factorial : ℝ)) *
          p4Q2NU_originalWilsonPerronSignedCoordinateEnergy
            H b hb e z y c n := by
  unfold p4Q2NW_originalWilsonPerronSignedTaylorDoubleEnergy
  apply Finset.sum_congr rfl
  intro n hn
  rw [p4Q2NW_originalWilsonPerronSignedPowerDoubleEnergy_eq]
  simp only [div_eq_mul_inv]
  ring

/-- All finite truncated original signed temporal Wilson double
energies are nonnegative for actual positive Wilson coupling. -/
theorem p4Q2NW_originalWilsonPerronSignedTaylorDoubleEnergy_nonneg
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) (degree : ℕ) :
    0 ≤ p4Q2NW_originalWilsonPerronSignedTaylorDoubleEnergy
      H b hb e z y c degree := by
  rw [p4Q2NW_originalWilsonPerronSignedTaylorDoubleEnergy_eq_coordinateSum]
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg
    (div_nonneg (pow_nonneg (div_nonneg hb (by norm_num)) n) (by positivity))
    (by
      rw [p4Q2NU_originalWilsonPerron_signedCoordinateEnergy_eq]
      exact p4Q2NU_originalSignedCoordinateEnergy_nonneg
        (p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c) n)

/-- There exists an ACTUAL finite Taylor cutoff with strictly
POSITIVE true Wilson–Perron signed double energy, without assuming any
nonzero physical moment. Infinite exponential convergence still OPEN. -/
theorem p4Q2NW_originalWilsonPerronSignedTaylorDoubleEnergy_exists_pos
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b) (bpos : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) :
    ∃ degree : ℕ,
      0 < p4Q2NW_originalWilsonPerronSignedTaylorDoubleEnergy
        H b hb e z y c degree := by
  obtain ⟨n, hn⟩ :=
    p4Q2NV_originalWilsonPerron_someWeightedSignedCoordinateEnergy_pos
      H b hb bpos e z y c
  refine ⟨n, ?_⟩
  rw [p4Q2NW_originalWilsonPerronSignedTaylorDoubleEnergy_eq_coordinateSum]
  have hBound :
      ((b / 2)^n / (n.factorial : ℝ)) *
          p4Q2NU_originalWilsonPerronSignedCoordinateEnergy H b hb e z y c n ≤
        ∑ m ∈ Finset.range (n + 1),
          ((b / 2)^m / (m.factorial : ℝ)) *
            p4Q2NU_originalWilsonPerronSignedCoordinateEnergy
              H b hb e z y c m := by
    apply Finset.single_le_sum
      (fun m hm =>
        mul_nonneg (p4Q2NV_originalTemporalCoordinateTaylorCoefficient_pos
          b bpos m).le
          (by
            rw [p4Q2NU_originalWilsonPerron_signedCoordinateEnergy_eq]
            exact p4Q2NU_originalSignedCoordinateEnergy_nonneg
              (p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c) m))
    exact Finset.mem_range.mpr (Nat.lt_succ_self n)
  exact lt_of_lt_of_le hn hBound

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NW_originalSignedPowerMomentSection_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NW_originalSignedPowerMomentSection_pairEnergy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NW_originalWilsonPerronSignedPowerMomentSection_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NW_originalWilsonPerronSignedPowerOuter_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NW_originalWilsonPerronSignedPowerDoubleEnergy_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NW_originalWilsonPerronSignedPowerDoubleEnergy_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NW_originalWilsonPerronSignedTaylorDoubleEnergy_eq_coordinateSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NW_originalWilsonPerronSignedTaylorDoubleEnergy_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NW_originalWilsonPerronSignedTaylorDoubleEnergy_exists_pos
