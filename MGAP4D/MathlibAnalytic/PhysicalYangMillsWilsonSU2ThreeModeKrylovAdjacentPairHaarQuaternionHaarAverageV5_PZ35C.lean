import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionSU2V5_PZ35B
import MGAP4D.MathlibAnalytic.CompactGaugeWilsonGaugeInvariance
import Mathlib.Tactic

/-!
# P4-Q2-PZ35C — four ACTUAL SU(2) left translations of compact Haar

The finite quaternion family of PZ35B is now verified to consist of
genuine SU(2) elements. This stage transports their left multiplication
through the SAME compact normalized SU(2) Haar used by the original Wilson
lattice action, proving exact four-term average invariance for ANY
continuous real test function.

Applied to the original Wilson-character pair, the only still-missing
finite-dimensional step is its pointwise four-term orbit sum identity.
That pointwise relation remains an explicitly visible hypothesis here;
this module does NOT assert Schur orthogonality or the fourth Haar moment.

No finite-group Haar replacement, new axiom, sorry/admit/native_decide,
independent posterior, Dobrushin shortcut or mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "q" => p4Q2PZ35B_quaternionFamily
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2

local instance p4Q2PZ35C_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance p4Q2PZ35C_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2

local instance p4Q2PZ35C_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2

local instance p4Q2PZ35C_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2

local instance p4Q2PZ35C_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PZ35C_probability :
    IsProbabilityMeasure μ := by
  unfold normalizedCompactHaar
  infer_instance

/-- Actual normalized compact SU(2) Haar left invariance, for every
continuous real test f and EVERY true SU(2) element a. -/
theorem p4Q2PZ35C_originalSU2Haar_integral_left_translate
    (f : G → ℝ) (hf : Continuous f) (a : G) :
    (∫ u : G, f (a * u) ∂μ) = (∫ u : G, f u ∂μ) := by
  have hp :
      MeasurePreserving (fun u : G => a * u) μ μ := by
    simpa only [mul_one] using
      (normalizedCompactHaar_measurePreserving_mul_left_right G a (1 : G))
  have hMeas :
      AEStronglyMeasurable f (Measure.map (fun u : G => a * u) μ) := by
    rw [hp.map_eq]
    exact hf.measurable.aestronglyMeasurable
  calc
    (∫ u : G, f (a * u) ∂μ) =
        (∫ u : G, f u ∂Measure.map (fun u : G => a * u) μ) :=
      (MeasureTheory.integral_map hp.measurable.aemeasurable hMeas).symm
    _ = (∫ u : G, f u ∂μ) := by
      rw [hp.map_eq]

/-- EXACT fourfold Haar averaging over four points that were proved
to be literal elements of SU(2), with NO change to Haar law.
This is not the Haar measure of the four-point quaternion subgroup. -/
theorem p4Q2PZ35C_originalSU2Haar_fourQuaternionAverage
    (f : G → ℝ) (hf : Continuous f) :
    (∫ u : G, (∑ j : Fin 4, f (q j * u)) ∂μ) =
      4 * (∫ u : G, f u ∂μ) := by
  have hInt (j : Fin 4) :
      Integrable (fun u : G => f (q j * u)) μ := by
    have hc : Continuous (fun u : G => f (q j * u)) :=
      hf.comp (continuous_const.mul continuous_id)
    exact hc.integrable_of_hasCompactSupport
  calc
    (∫ u : G, (∑ j : Fin 4, f (q j * u)) ∂μ) =
        ∑ j : Fin 4, (∫ u : G, f (q j * u) ∂μ) := by
      rw [integral_finset_sum _ (fun j _hj => hInt j)]
    _ = ∑ _j : Fin 4, (∫ u : G, f u ∂μ) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact p4Q2PZ35C_originalSU2Haar_integral_left_translate
        f hf (q j)
    _ = 4 * (∫ u : G, f u ∂μ) := by
      simp only [Fin.sum_univ_four]
      ring

/-- The ORIGINAL SU(2) real fundamental character (1 - Wilson energy),
without substituting a finite-group character. -/
noncomputable def p4Q2PZ35C_originalOneLinkCharacter (u : G) : ℝ :=
  1 - E u

/-- The actual one-link SU(2) Wilson character-correlation integrand. -/
noncomputable def p4Q2PZ35C_originalOneLinkCharacterPair (b u : G) : ℝ :=
  p4Q2PZ35C_originalOneLinkCharacter u *
    p4Q2PZ35C_originalOneLinkCharacter (u⁻¹ * b)

theorem p4Q2PZ35C_originalOneLinkCharacterPair_continuous (b : G) :
    Continuous (p4Q2PZ35C_originalOneLinkCharacterPair b) := by
  have hc : Continuous (p4Q2PZ35C_originalOneLinkCharacter) :=
    continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
  change Continuous (fun u : G =>
    p4Q2PZ35C_originalOneLinkCharacter u *
      p4Q2PZ35C_originalOneLinkCharacter (u⁻¹ * b))
  exact hc.mul (hc.comp (continuous_id.inv.mul continuous_const))

/-- The exact quaternion-average Haar identity applied to the
unmodified Wilson character-correlation of the original SU(2) model. -/
theorem p4Q2PZ35C_originalOneLinkCharacterPair_fourHaarAverage (b : G) :
    (∫ u : G, (∑ j : Fin 4,
      p4Q2PZ35C_originalOneLinkCharacterPair b (q j * u)) ∂μ) =
        4 * (∫ u : G,
          p4Q2PZ35C_originalOneLinkCharacterPair b u ∂μ) :=
  p4Q2PZ35C_originalSU2Haar_fourQuaternionAverage
    (p4Q2PZ35C_originalOneLinkCharacterPair b)
    (p4Q2PZ35C_originalOneLinkCharacterPair_continuous b)

/-- Transparent remaining finite-dimensional pointwise gate:
if the exact quaternion orbit sum is proved to equal the ORIGINAL
real Wilson character, its genuine SU(2) Haar character correlation
is 1/4 of that character, with no separate Schur axiom. -/
theorem p4Q2PZ35C_originalOneLinkHaar_quarter_of_quaternionOrbit
    (b : G)
    (hOrbit : ∀ u : G,
      (∑ j : Fin 4,
        p4Q2PZ35C_originalOneLinkCharacterPair b (q j * u)) =
        p4Q2PZ35C_originalOneLinkCharacter b) :
    (∫ u : G,
      p4Q2PZ35C_originalOneLinkCharacterPair b u ∂μ) =
        (1 / 4 : ℝ) * p4Q2PZ35C_originalOneLinkCharacter b := by
  have hAvg :=
    p4Q2PZ35C_originalOneLinkCharacterPair_fourHaarAverage b
  have hConst :
      (∫ u : G, (∑ j : Fin 4,
        p4Q2PZ35C_originalOneLinkCharacterPair b (q j * u)) ∂μ) =
        p4Q2PZ35C_originalOneLinkCharacter b := by
    calc
      (∫ u : G, (∑ j : Fin 4,
        p4Q2PZ35C_originalOneLinkCharacterPair b (q j * u)) ∂μ) =
          (∫ _u : G, p4Q2PZ35C_originalOneLinkCharacter b ∂μ) := by
        apply integral_congr_ae
        filter_upwards with u
        exact hOrbit u
      _ = p4Q2PZ35C_originalOneLinkCharacter b := by simp
  rw [hConst] at hAvg
  linarith

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35C_originalSU2Haar_integral_left_translate
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35C_originalSU2Haar_fourQuaternionAverage
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35C_originalOneLinkCharacterPair_continuous
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35C_originalOneLinkCharacterPair_fourHaarAverage
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35C_originalOneLinkHaar_quarter_of_quaternionOrbit
