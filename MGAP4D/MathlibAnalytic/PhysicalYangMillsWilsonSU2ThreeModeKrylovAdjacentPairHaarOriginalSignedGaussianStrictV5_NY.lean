import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedPairBanachV5_NX
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
# P4-Q2-NY — full original SU(2) Gaussian signed energy, no truncated limit assumption

NX constructed a genuine bounded double action T_L on
C(SU(2) × SU(2),R) for the SAME original Wilson–Perron signed
functional L, and established a Banach exponential HasSum. NV/NW
show that the genuine n-th Wilson temporal character double pairing
equals 2^(-n) times a positive real-eight coordinate energy E_n.
NU/NT/NO/NI prove some E_n is STRICTLY positive for every genuinely
nonzero original Wilson–Perron signed rho-minus-Dirac functional.

NY closes the previously open analytic obstruction by proving:
  (i) T_L(chi_pair^n)=2^(-n) E_n(L);
 (ii) T_L(exp(b chi_pair))= sum_n (b/2)^n/n! E_n(L);
(iii) for every b>0 and L != 0, the EXACT complete exponential
      Wilson Gaussian double signed energy is STRICTLY positive.
This proves no artificial rank or characteristic-kernel hypothesis:
T_L is the original signed Haar-minus-Dirac double action, and
NormedSpace.exp_series_hasSum_exp' gives uniform Banach convergence.

The exact pair exponential equals the ORIGINAL genuine SU2 temporal
Wilson kernel k_b(x,g)=exp(b chi(x,g)). Nonzero positive energy therefore
forces at least one genuine fixed-b kernel section with L(k_b,x)!=0,
for EVERY nonzero bounded signed functional L. The original signed
Wilson–Perron functional is unconditionally nonzero by NI/NJ, hence
the genuine NJ/NC signed receiver Haar variance is STRICTLY POSITIVE
without assuming fixed-b section-span density.

These are local finite-volume claims, not a GI covariance, uniform
coercivity U0, endpoint source, continuum H1-C3 or 4d mass gap.
Both original interacting Wilson posterior laws, the Gauss-law source,
Perron half-density and spatial Wilson factors remain unchanged.
No Dobrushin, sorry, admit, new axiom or physical hypothesis.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NY_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NY_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NY_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NY_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NY_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "chi" => p4Q2NG_originalSU2TemporalCharacter
local notation "PairChi" => p4Q2NX_originalTemporalPairCharacter
local notation "Double" => p4Q2NX_originalSignedDoubleCLM
local notation "E" => p4Q2NU_originalSignedCoordinateEnergy

/-- The exact degree-n ORIGINAL SU2 relative temporal character has
double signed value 2^(-n) times the NU real-eight coordinate energy.
This identifies the genuine finite NW Haar double action with NX. -/
theorem p4Q2NY_originalSignedDouble_characterPower_eq_coordinateEnergy
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (n : ℕ) :
    Double L (PairChi ^ n) = (1 / 2 : ℝ)^n * E L n := by
  rw [p4Q2NX_originalSignedDoubleCLM_apply]
  have hSection :
      p4Q2NX_originalSignedPairSection L (PairChi ^ n) =
        p4Q2NW_originalSignedPowerMomentSection L n := by
    ext x
    rw [p4Q2NX_originalSignedPairSection_apply,
      p4Q2NW_originalSignedPowerMomentSection_apply]
    congr 1
  rw [hSection]
  exact p4Q2NW_originalSignedPowerMomentSection_pairEnergy L n

/-- Algebraic power of the genuine pair Wilson character commutes
with scalar multiplication by a real positive coupling. -/
theorem p4Q2NY_originalPairCharacter_smul_pow
    (b : ℝ) (n : ℕ) :
    (b • PairChi)^n = b^n • PairChi^n := by
  ext p
  simp only [ContinuousMap.pow_apply, ContinuousMap.smul_apply, smul_eq_mul, mul_pow]

/-- Each actual EXPONENTIAL Taylor term under the DOUBLE signed
functional is precisely the positive weighted signed coordinate
moment energy, at every natural degree. -/
theorem p4Q2NY_originalSignedDouble_expTerm_eq_weightedEnergy
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (b : ℝ) (n : ℕ) :
    Double L (((n.factorial : ℝ)⁻¹) • (b • PairChi)^n) =
      ((b / 2)^n / (n.factorial : ℝ)) * E L n := by
  rw [p4Q2NY_originalPairCharacter_smul_pow]
  simp only [map_smul, smul_eq_mul]
  rw [p4Q2NY_originalSignedDouble_characterPower_eq_coordinateEnergy]
  simp only [div_eq_mul_inv]
  ring

/-- Positive n-th scalar Fock energy with no synthetic coefficient or
posterior; all terms are genuine original Wilson Taylor terms. -/
noncomputable def p4Q2NY_originalSignedGaussianEnergyTerm
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (b : ℝ) (n : ℕ) : ℝ :=
  ((b / 2)^n / (n.factorial : ℝ)) * E L n

/-- MAIN convergence bridge: the original genuine signed Wilson
Gaussian double energy is EXACTLY the convergent sum over all true
real-eight Fock coordinate energy modes, with strictly positive
coefficients b^n/(2^n n!). Uniform convergence and interchange are
proved by mapping NX's Banach HasSum through a bounded CLM. -/
theorem p4Q2NY_originalSignedGaussianEnergy_hasSum
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (b : ℝ) :
    HasSum
      (p4Q2NY_originalSignedGaussianEnergyTerm L b)
      (Double L (NormedSpace.exp (b • PairChi))) := by
  have h :=
    p4Q2NX_originalSignedDouble_BanachExp_hasSum L b
  have hTerm :
      (fun n : ℕ =>
        Double L (((n.factorial : ℝ)⁻¹) • (b • PairChi)^n)) =
        p4Q2NY_originalSignedGaussianEnergyTerm L b := by
    funext n
    exact p4Q2NY_originalSignedDouble_expTerm_eq_weightedEnergy L b n
  rw [← hTerm]
  exact h

theorem p4Q2NY_originalSignedGaussianEnergyTerm_nonneg
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (b : ℝ) (hb : 0 < b) (n : ℕ) :
    0 ≤ p4Q2NY_originalSignedGaussianEnergyTerm L b n := by
  unfold p4Q2NY_originalSignedGaussianEnergyTerm
  exact mul_nonneg
    (p4Q2NV_originalTemporalCoordinateTaylorCoefficient_pos b hb n).le
    (p4Q2NU_originalSignedCoordinateEnergy_nonneg L n)

/-- Genuine full exponential kernel signed energy: every NONZERO
continuous signed L is detected by at least one finite coordinate
monomial (NT/NU), so one positive Fock term survives in the full sum.
NO fixed-beta Gaussian injectivity assumption is inserted. -/
theorem p4Q2NY_originalSignedGaussianDoubleEnergy_pos
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (hL : L ≠ 0)
    (b : ℝ) (hb : 0 < b) :
    0 < Double L (NormedSpace.exp (b • PairChi)) := by
  obtain ⟨n, hn⟩ :=
    p4Q2NU_nonzeroSignedFunctional_has_positiveCoordinateDegree L hL
  have hPositiveTerm :
      0 < p4Q2NY_originalSignedGaussianEnergyTerm L b n :=
    mul_pos (p4Q2NV_originalTemporalCoordinateTaylorCoefficient_pos
      b hb n) hn
  have hLimit :=
    (p4Q2NY_originalSignedGaussianEnergy_hasSum L b).tendsto_sum_nat
  have hEventually : ∀ᶠ degree : ℕ in atTop,
      p4Q2NY_originalSignedGaussianEnergyTerm L b n ≤
        ∑ m ∈ Finset.range degree,
          p4Q2NY_originalSignedGaussianEnergyTerm L b m := by
    filter_upwards [Filter.eventually_ge_atTop (n + 1)] with degree hd
    apply Finset.single_le_sum
      (fun m hm =>
        p4Q2NY_originalSignedGaussianEnergyTerm_nonneg L b hb m)
    exact Finset.mem_range.mpr (Nat.lt_of_succ_le hd)
  exact lt_of_lt_of_le hPositiveTerm
    (ge_of_tendsto hLimit hEventually)

/-- The actual original SU(2) temporal Wilson exponential is the
evaluation of the two-variable Banach exponential at (x,g), with
NO alternative kernel or discarded Wilson normalization. -/
theorem p4Q2NY_originalPairBanachExp_eq_trueTemporalWilson
    (b : ℝ) (x g : Gauge) :
    (NormedSpace.exp (b • PairChi)) (x, g) =
      p4Q2NJ_originalSU2WilsonTemporalSection b x g := by
  rw [NormedSpace.exp_continuousMap_eq]
  change NormedSpace.exp (b * chi x g) = Real.exp (b * chi x g)
  rw [Real.exp_eq_exp_ℝ]

/-- All nonzero bounded signed functionals on true SU(2), not only
finite atomic distributions, detect at least one section of the
ORIGINAL temporal Wilson kernel for EVERY b>0. This is a direct
noncancellation conclusion from the all-order positive double
energy, stronger than all-finite Gram PSD. -/
theorem p4Q2NY_originalPositiveWilsonSection_detects_nonzeroSigned
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (hL : L ≠ 0)
    (b : ℝ) (hb : 0 < b) :
    ∃ x : Gauge, L (p4Q2NJ_originalSU2WilsonTemporalSection b x) ≠ 0 := by
  have hEnergy :
      0 < Double L (NormedSpace.exp (b • PairChi)) :=
    p4Q2NY_originalSignedGaussianDoubleEnergy_pos L hL b hb
  by_contra hNone
  have hVan (x : Gauge) :
      L (p4Q2NJ_originalSU2WilsonTemporalSection b x) = 0 := by
    by_contra hx
    exact hNone ⟨x, hx⟩
  have hSectionZero :
      p4Q2NX_originalSignedPairSection L
        (NormedSpace.exp (b • PairChi)) = 0 := by
    ext x
    rw [p4Q2NX_originalSignedPairSection_apply]
    have hRow :
        (NormedSpace.exp (b • PairChi)).curry x =
          p4Q2NJ_originalSU2WilsonTemporalSection b x := by
      ext g
      exact p4Q2NY_originalPairBanachExp_eq_trueTemporalWilson b x g
    rw [hRow, hVan]
    simp
  rw [p4Q2NX_originalSignedDoubleCLM_apply, hSectionZero] at hEnergy
  simp at hEnergy

/-- The ORIGINAL Wilson–Perron signed Haar minus Dirac functional
has STRICTLY positive actual temporal Gaussian double energy,
because NI/NJ proved its NONZERO-ness without assumed rank. -/
theorem p4Q2NY_originalWilsonPerronSignedGaussianDoubleEnergy_pos
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b) (bpos : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) :
    0 < Double (p4Q2NJ_originalSignedDiracDefectCLM
        H b hb e z y c)
      (NormedSpace.exp (b • PairChi)) :=
  p4Q2NY_originalSignedGaussianDoubleEnergy_pos
    (p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c)
    (p4Q2NJ_originalSignedDiracDefectCLM_ne_zero
      H b hb bpos e z y c) b bpos

/-- The ACTUAL signed Wilson–Perron receiver has strictly positive
finite-volume Haar variance, unconditionally at every b>0.
This does NOT imply original physical GI covariance or U0. -/
theorem p4Q2NY_originalWilsonPerronSignedReceiverHaarVariance_pos
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b) (bpos : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    0 < p4Q2NC_originalSignedReceiverLinkHaarVariance H b hb e z := by
  apply (p4Q2NJ_originalSignedReceiverHaarVariance_pos_iff_sectionWitness
    H b hb e z).2
  exact p4Q2NY_originalPositiveWilsonSection_detects_nonzeroSigned
    (p4Q2NJ_originalSignedDiracDefectCLM H b hb e z
      (z.2 e) (p4Q2NC_originalSignedReceiverLinkScore H b hb e z 1))
    (p4Q2NJ_originalSignedDiracDefectCLM_ne_zero H b hb bpos e z
      (z.2 e) (p4Q2NC_originalSignedReceiverLinkScore H b hb e z 1))
    b bpos

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NY_originalSignedDouble_characterPower_eq_coordinateEnergy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NY_originalPairCharacter_smul_pow
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NY_originalSignedDouble_expTerm_eq_weightedEnergy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NY_originalSignedGaussianEnergy_hasSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NY_originalSignedGaussianEnergyTerm_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NY_originalSignedGaussianDoubleEnergy_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NY_originalPairBanachExp_eq_trueTemporalWilson
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NY_originalPositiveWilsonSection_detects_nonzeroSigned
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NY_originalWilsonPerronSignedGaussianDoubleEnergy_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NY_originalWilsonPerronSignedReceiverHaarVariance_pos
