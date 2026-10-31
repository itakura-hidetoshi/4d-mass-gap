import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyInfiniteRange
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionWilsonHaarOrientationsV5_PZ35D5
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABV — explicit original SU(2) energy caps with Haar mass

The four genuine quaternion translates satisfy a pointwise sum-of-squares
identity for the original Wilson character. At least one translated
character has absolute value at least 1/2. Including the genuine central
minus identity gives eight original SU(2) left translates covering the
low-energy cap preimages. Normalized compact Haar invariance therefore
gives mass at least 1/8 for that cap and its antipodal high-energy cap.
Their ordered product has the explicit original pair-Haar mass 1/64.

The pi rotation is proved to be the same central minus identity, so its
inverse complements the actual Wilson energy. There is no finite-group
Haar replacement, extra cap-mass assumption, physical-response alignment
claim, global signed-integral claim, or mass-gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "q" => p4Q2PZ35B_quaternionFamily
local notation "z" => p4Q2PZ35D4_centralMinusOne
local notation "rot" => specialUnitaryTwoRotation Real.pi
local notation "μ" => normalizedCompactHaar G

local instance p4Q2PZ37ABV_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABV_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABV_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABV_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABV_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABV_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- The original explicit pi rotation is the genuine central minus identity. -/
theorem p4Q2PZ37ABV_pi_eq_centralMinusOne : rot = z := by
  apply Subtype.ext
  change specialUnitaryTwoRotationMatrix Real.pi = (z : Mat)
  rw [p4Q2PZ35D4_centralMinusOne_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [specialUnitaryTwoRotationMatrix]

/-- The actual central minus identity has order two. -/
theorem p4Q2PZ37ABV_centralMinusOne_mul_self : z * z = (1 : G) := by
  apply Subtype.ext
  change (z : Mat) * (z : Mat) = (1 : Mat)
  simp [p4Q2PZ35D4_centralMinusOne_coe]

/-- Inversion fixes the genuine central minus identity. -/
theorem p4Q2PZ37ABV_centralMinusOne_inv : z⁻¹ = z := by
  calc
    z⁻¹ = z⁻¹ * (z * z) := by
      rw [p4Q2PZ37ABV_centralMinusOne_mul_self, mul_one]
    _ = z := by group

/-- The original pi rotation is its own inverse. -/
theorem p4Q2PZ37ABV_pi_inv : rot⁻¹ = rot := by
  simp only [p4Q2PZ37ABV_pi_eq_centralMinusOne,
    p4Q2PZ37ABV_centralMinusOne_inv]

/-- Multiplication by the original central minus identity complements energy. -/
theorem p4Q2PZ37ABV_central_mul_energy (g : G) :
    E (z * g) = 2 - E g := by
  have h := p4Q2PZ35D4_originalCharacter_centralFlip g
  unfold p4Q2PZ35C_originalOneLinkCharacter at h
  linarith

/-- The exact antipodal energy identity for ABU's original pi-rotated row. -/
theorem p4Q2PZ37ABV_piInv_mul_energy (g : G) :
    E (rot⁻¹ * g) = 2 - E g := by
  rw [p4Q2PZ37ABV_pi_eq_centralMinusOne,
    p4Q2PZ37ABV_centralMinusOne_inv]
  exact p4Q2PZ37ABV_central_mul_energy g

/-- The original low-energy cap; no coupling, volume or source enters. -/
noncomputable def p4Q2PZ37ABV_lowEnergyCap : Set G :=
  {g | E g ≤ (1 / 2 : ℝ)}

/-- The original antipodal high-energy cap. -/
noncomputable def p4Q2PZ37ABV_highEnergyCap : Set G :=
  {g | (3 / 2 : ℝ) ≤ E g}

/-- The ordered low/high energy pair region in genuine SU(2) product Haar. -/
noncomputable def p4Q2PZ37ABV_pairCap : Set (G × G) :=
  p4Q2PZ37ABV_lowEnergyCap ×ˢ p4Q2PZ37ABV_highEnergyCap

theorem p4Q2PZ37ABV_lowEnergyCap_measurable :
    MeasurableSet p4Q2PZ37ABV_lowEnergyCap := by
  exact measurableSet_le
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).measurable
    measurable_const

theorem p4Q2PZ37ABV_highEnergyCap_measurable :
    MeasurableSet p4Q2PZ37ABV_highEnergyCap := by
  exact measurableSet_le measurable_const
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).measurable

theorem p4Q2PZ37ABV_pairCap_measurable :
    MeasurableSet p4Q2PZ37ABV_pairCap :=
  p4Q2PZ37ABV_lowEnergyCap_measurable.prod
    p4Q2PZ37ABV_highEnergyCap_measurable

/-- The existing genuine quaternion trace orbit is a sum of four squares. -/
theorem p4Q2PZ37ABV_quaternion_character_squares (g : G) :
    (∑ j : Fin 4, χ (q j * g) ^ 2) = 1 := by
  have hOne : χ (1 : G) = 1 := by
    unfold p4Q2PZ35C_originalOneLinkCharacter
    rw [specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num)]
    norm_num
  have h := p4Q2PZ35D4_originalRealCharacterOrbit (1 : G) g
  simp only [mul_one, p4Q2PZ35D5_originalCharacter_inv] at h
  simpa only [pow_two, hOne] using h

/-- One of the four actual translated characters reaches an antipodal cap. -/
theorem p4Q2PZ37ABV_quaternion_hits_signed_cap (g : G) :
    ∃ j : Fin 4,
      (1 / 2 : ℝ) ≤ χ (q j * g) ∨ χ (q j * g) ≤ -(1 / 2 : ℝ) := by
  by_contra h
  simp only [not_exists, not_or, not_le] at h
  have hs (j : Fin 4) : χ (q j * g) ^ 2 < (1 / 4 : ℝ) := by
    have hp := mul_pos (sub_pos.mpr (h j).1) (sub_pos.mpr (h j).2)
    nlinarith
  have hsum := p4Q2PZ37ABV_quaternion_character_squares g
  simp only [Fin.sum_univ_four] at hsum
  linarith [hs 0, hs 1, hs 2, hs 3]

/-- Eight genuine SU(2) elements, used only as Haar-preserving translations. -/
noncomputable def p4Q2PZ37ABV_capTranslate (i : Fin 4 × Bool) : G :=
  if i.2 then z * q i.1 else q i.1

/-- Eight preimages of the actual low-energy cap cover the original SU(2). -/
theorem p4Q2PZ37ABV_eight_cap_cover :
    (⋃ i : Fin 4 × Bool,
      (fun g : G => p4Q2PZ37ABV_capTranslate i * g) ⁻¹'
        p4Q2PZ37ABV_lowEnergyCap) = Set.univ := by
  ext g
  simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_univ, iff_true]
  obtain ⟨j, hj | hj⟩ := p4Q2PZ37ABV_quaternion_hits_signed_cap g
  · refine ⟨(j, false), ?_⟩
    change E (q j * g) ≤ (1 / 2 : ℝ)
    unfold p4Q2PZ35C_originalOneLinkCharacter at hj
    linarith
  · refine ⟨(j, true), ?_⟩
    change E ((z * q j) * g) ≤ (1 / 2 : ℝ)
    rw [mul_assoc, p4Q2PZ37ABV_central_mul_energy]
    unfold p4Q2PZ35C_originalOneLinkCharacter at hj
    linarith

private theorem p4Q2PZ37ABV_haar_left_preimage
    (a : G) (s : Set G) (hs : MeasurableSet s) :
    μ ((fun g : G => a * g) ⁻¹' s) = μ s := by
  have hp : MeasurePreserving (fun g : G => a * g) μ μ := by
    simpa only [mul_one] using
      (normalizedCompactHaar_measurePreserving_mul_left_right G a (1 : G))
  exact hp.measure_preimage hs.nullMeasurableSet

/-- Explicit low-cap Haar mass from the eight-translate cover of the same Haar. -/
theorem p4Q2PZ37ABV_lowEnergyCap_real_mass_lower :
    (1 / 8 : ℝ) ≤ μ.real p4Q2PZ37ABV_lowEnergyCap := by
  have hpre (i : Fin 4 × Bool) :
      μ ((fun g : G => p4Q2PZ37ABV_capTranslate i * g) ⁻¹'
        p4Q2PZ37ABV_lowEnergyCap) = μ p4Q2PZ37ABV_lowEnergyCap :=
    p4Q2PZ37ABV_haar_left_preimage _ _
      p4Q2PZ37ABV_lowEnergyCap_measurable
  have hmass : (1 : ℝ≥0∞) ≤ 8 * μ p4Q2PZ37ABV_lowEnergyCap := by
    have h := measure_iUnion_fintype_le μ
      (fun i : Fin 4 × Bool =>
        (fun g : G => p4Q2PZ37ABV_capTranslate i * g) ⁻¹'
          p4Q2PZ37ABV_lowEnergyCap)
    rw [p4Q2PZ37ABV_eight_cap_cover] at h
    simp_rw [hpre] at h
    simpa [nsmul_eq_mul] using h
  have hfinite : 8 * μ p4Q2PZ37ABV_lowEnergyCap ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono hfinite hmass
  norm_num [ENNReal.toReal_mul] at hr
  change (1 / 8 : ℝ) ≤ (μ p4Q2PZ37ABV_lowEnergyCap).toReal
  linarith

/-- Central translation identifies the two actual antipodal cap masses. -/
theorem p4Q2PZ37ABV_highEnergyCap_mass_eq :
    μ p4Q2PZ37ABV_highEnergyCap = μ p4Q2PZ37ABV_lowEnergyCap := by
  have hset : p4Q2PZ37ABV_highEnergyCap =
      (fun g : G => z * g) ⁻¹' p4Q2PZ37ABV_lowEnergyCap := by
    ext g
    change (3 / 2 : ℝ) ≤ E g ↔ E (z * g) ≤ (1 / 2 : ℝ)
    rw [p4Q2PZ37ABV_central_mul_energy]
    constructor <;> intro hg <;> linarith
  rw [hset]
  exact p4Q2PZ37ABV_haar_left_preimage z _
    p4Q2PZ37ABV_lowEnergyCap_measurable

/-- The antipodal high-energy cap has the same explicit original Haar floor. -/
theorem p4Q2PZ37ABV_highEnergyCap_real_mass_lower :
    (1 / 8 : ℝ) ≤ μ.real p4Q2PZ37ABV_highEnergyCap := by
  simpa only [measureReal_def, p4Q2PZ37ABV_highEnergyCap_mass_eq] using
    p4Q2PZ37ABV_lowEnergyCap_real_mass_lower

/-- The actual ordered cap pair has at least 1/64 of original product Haar. -/
theorem p4Q2PZ37ABV_pairCap_real_mass_lower :
    (1 / 64 : ℝ) ≤ (μ.prod μ).real p4Q2PZ37ABV_pairCap := by
  rw [p4Q2PZ37ABV_pairCap, measureReal_prod_prod]
  calc
    (1 / 64 : ℝ) = (1 / 8 : ℝ) * (1 / 8 : ℝ) := by norm_num
    _ ≤ μ.real p4Q2PZ37ABV_lowEnergyCap * μ.real p4Q2PZ37ABV_highEnergyCap :=
      mul_le_mul p4Q2PZ37ABV_lowEnergyCap_real_mass_lower
        p4Q2PZ37ABV_highEnergyCap_real_mass_lower (by norm_num)
        (le_trans (by norm_num) p4Q2PZ37ABV_lowEnergyCap_real_mass_lower)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_pi_eq_centralMinusOne
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_centralMinusOne_mul_self
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_centralMinusOne_inv
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_pi_inv
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_central_mul_energy
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_piInv_mul_energy
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_lowEnergyCap_measurable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_highEnergyCap_measurable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_pairCap_measurable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_quaternion_character_squares
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_quaternion_hits_signed_cap
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_eight_cap_cover
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_lowEnergyCap_real_mass_lower
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_highEnergyCap_mass_eq
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_highEnergyCap_real_mass_lower
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_pairCap_real_mass_lower
