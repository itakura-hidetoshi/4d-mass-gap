import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorCoordinatePolynomialDetectionV5_KM
import Mathlib.Tactic

/-!
# P4-Q2-KO — finite, original SU(2) Haar double Gram = sum of moment squares

The exact compact normalized Haar measure of the SAME SU(2) group used
for the true Wilson posterior conditional densities is a legitimate
REFERENCE measure. It is not a substitute conditional posterior.

For every finite collection of continuous real SU(2) test functions
F_i, Fubini/finite linearity proves:
   ∫∫ (∑_i F_i(g) F_i(h)) dν(h)dν(g) = ∑_i (∫ F_i dν)^2 ≥ 0.
If the double Gram vanishes, EVERY constituent Haar moment vanishes.

These lemmas are the analytic Hilbert-Gram mechanism for applying
the exact finite coordinate-monomial expansion proved separately in
KN to EACH homogeneous Wilson exponential-kernel Taylor term.

No assumption on genuine GI receiver rank, independent-Haar posterior,
sorry/admit, new axiom, H1-C3 or continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KO_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KO_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KO_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KO_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KO_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section SU2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "nu" => normalizedCompactHaar Gauge

/-- Finite Gram integration is an EXACT finite sum of genuine SU(2)
reference-Haar squared moments, for arbitrary continuous test functions.
No measure replacement, no a.e. point evaluation and no unproved
interchange of infinite series with integrals. -/
theorem p4Q2KO_originalSU2HaarFiniteDoubleGram_eq_sumMomentsSq
    {ι : Type*} [Fintype ι] (F : ι → C(Gauge, ℝ)) :
    (∫ g : Gauge, ∫ h : Gauge,
      (∑ i : ι, F i g * F i h) ∂nu ∂nu) =
    ∑ i : ι, (∫ g : Gauge, F i g ∂nu) ^ 2 := by
  classical
  have hFI (i : ι) : Integrable (fun g : Gauge => F i g) nu :=
    (F i).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInner (g : Gauge) :
      (∫ h : Gauge, (∑ i : ι, F i g * F i h) ∂nu) =
        ∑ i : ι, F i g * (∫ h : Gauge, F i h ∂nu) := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul]
    · intro i hi
      exact (hFI i).const_mul _
  calc
    (∫ g : Gauge, ∫ h : Gauge,
        (∑ i : ι, F i g * F i h) ∂nu ∂nu) =
      ∫ g : Gauge, (∑ i : ι,
        F i g * (∫ h : Gauge, F i h ∂nu)) ∂nu := by
          apply integral_congr_ae
          filter_upwards with g
          exact hInner g
    _ = ∑ i : ι, (∫ g : Gauge, F i g ∂nu) ^ 2 := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_mul_const]
        ring
      · intro i hi
        exact (hFI i).mul_const _

/-- Nonnegativity of ANY finite original SU(2) Haar double Gram
follows from its literal sum-of-squares identity. -/
theorem p4Q2KO_originalSU2HaarFiniteDoubleGram_nonneg
    {ι : Type*} [Fintype ι] (F : ι → C(Gauge, ℝ)) :
    0 ≤ (∫ g : Gauge, ∫ h : Gauge,
      (∑ i : ι, F i g * F i h) ∂nu ∂nu) := by
  rw [p4Q2KO_originalSU2HaarFiniteDoubleGram_eq_sumMomentsSq]
  exact Finset.sum_nonneg (fun i hi => sq_nonneg _)

/-- If a finite SU(2) Haar double Gram is zero, EVERY genuine
coordinate moment in that finite Gram is zero, not merely their sum. -/
theorem p4Q2KO_originalSU2HaarFiniteDoubleGram_zero_forces_all_moments_zero
    {ι : Type*} [Fintype ι] (F : ι → C(Gauge, ℝ))
    (hzero : (∫ g : Gauge, ∫ h : Gauge,
      (∑ i : ι, F i g * F i h) ∂nu ∂nu) = 0) :
    ∀ i : ι, (∫ g : Gauge, F i g ∂nu) = 0 := by
  classical
  rw [p4Q2KO_originalSU2HaarFiniteDoubleGram_eq_sumMomentsSq] at hzero
  intro i
  have hle :
      (∫ g : Gauge, F i g ∂nu) ^ 2 ≤
        ∑ j : ι, (∫ g : Gauge, F j g ∂nu) ^ 2 :=
    Finset.single_le_sum (fun j hj => sq_nonneg _) (Finset.mem_univ i)
  rw [hzero] at hle
  nlinarith [sq_nonneg (∫ g : Gauge, F i g ∂nu)]

end SU2
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KO_originalSU2HaarFiniteDoubleGram_eq_sumMomentsSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KO_originalSU2HaarFiniteDoubleGram_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KO_originalSU2HaarFiniteDoubleGram_zero_forces_all_moments_zero
