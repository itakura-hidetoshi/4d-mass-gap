import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRationalActionV5_PZ37AGL
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteWilsonClassFunction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialPlaquetteOverlapBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicNondegenerateShifts
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGN — exact original spatial Wilson Haar mean

Every original spatial plaquette uses four distinct physical links, including
at H=0: the even side length is 2(H+1), so a positive unit shift is nontrivial.
Restriction to these four links preserves the actual product Haar measure.
The already proved cyclic four-edge Haar word, and conjugation invariance of
the original Wilson energy, give Haar expectation ONE for each plaquette.

Consequently the genuine Hilbert centering scalar is exactly the literal
spatial plaquette-list length, not an independently supplied mean interval:

  m_H = integral W_H dmu_H = p_H.

The original continuous centered source is therefore (W_H-p_H)/2 and has
the sharper pointwise bound p_H/2. At every original rational-coordinate
configuration AGL supplies its exact rational value. These statements concern
the continuous representative; no arbitrary Haar-L2 point value is identified
with it. The existing original source, Haar law, action, and root are unchanged.

No signed-transfer separation, two-threshold shell, volume-uniform coercivity,
Hamiltonian spectral gap, or continuum Yang--Mills mass gap is asserted here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G

local instance p4Q2PZ37AGN_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGN_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGN_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGN_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGN_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AGN_probability : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G
local instance p4Q2PZ37AGN_leftInvariant : Measure.IsMulLeftInvariant mu := by
  unfold normalizedCompactHaar
  infer_instance

/-- A genuine original spatial unit shift never fixes its starting vertex,
also on the smallest even lattice. -/
theorem p4Q2PZ37AGN_spatialShift_ne_self
    (H : ℕ) (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (d : PeriodicHypercubicEvenSpatialDirection) :
    periodicHypercubicEvenSpatialSliceShift H v d ≠ v := by
  intro h
  have hside : 2 ≤ PeriodicHypercubicEvenSideLength H := by
    unfold PeriodicHypercubicEvenSideLength
    omega
  exact periodicHypercubicShift_ne_self
    (PeriodicHypercubicEvenSideLength H) hside v.1 d.1
    (congrArg Subtype.val h)

/-- The four ORIGINAL intrinsic boundary links are distinct; no independent
link model or nondegeneracy premise is introduced. -/
theorem p4Q2PZ37AGN_spatialBoundary_injective
    (H : ℕ) (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    Function.Injective (pz37zaSpatialPlaquetteBoundary H p) := by
  have haxes : p.2.1.1 ≠ p.2.1.2 := by
    intro h
    exact (ne_of_lt p.2.2) (congrArg Subtype.val h)
  have hmu := p4Q2PZ37AGN_spatialShift_ne_self H p.1 p.2.1.1
  have hnu := p4Q2PZ37AGN_spatialShift_ne_self H p.1 p.2.1.2
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [pz37zaSpatialPlaquetteBoundary, haxes, haxes.symm,
      hmu, hmu.symm, hnu, hnu.symm] at hij ⊢

/-- The existing actual four-link boundary as a finite coordinate embedding. -/
def p4Q2PZ37AGN_spatialBoundary_embedding
    (H : ℕ) (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    Fin 4 ↪ PeriodicHypercubicEvenSpatialSliceLink H where
  toFun := pz37zaSpatialPlaquetteBoundary H p
  inj' := p4Q2PZ37AGN_spatialBoundary_injective H p

/-- The original single SU(2) Wilson energy has true Haar mean one. -/
theorem p4Q2PZ37AGN_originalOneLinkEnergy_mean_one :
    (∫ g : G, specialUnitaryWilsonPlaquetteEnergy 2 g ∂mu) = 1 := by
  have hInt : Integrable (specialUnitaryWilsonPlaquetteEnergy 2) mu :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hMean := p4Q2PZ37AFS_originalCharacter_mean_zero
  change (∫ g : G, (1 : ℝ) - specialUnitaryWilsonPlaquetteEnergy 2 g ∂mu) = 0
    at hMean
  rw [integral_sub (integrable_const (1 : ℝ)) hInt] at hMean
  have hOne : (∫ _g : G, (1 : ℝ) ∂mu) = 1 := by simp
  rw [hOne] at hMean
  linarith only [hMean]

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "mH" => p4Q2PZ37AFZ_originalWilsonMean H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H

local instance p4Q2PZ37AGN_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AGN_plaquettes : Fintype Plq := Fintype.ofFinite _
local instance p4Q2PZ37AGN_spatialProbability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Cyclic conjugate of the original oriented plaquette word on its actual
four spatial links; used solely for the exact Haar transport. -/
def p4Q2PZ37AGN_originalPlaquetteCyclicHolonomy (p : Plq) (A : Cfg) : G :=
  haarFinFourCyclicPlaquetteWord
    (fun k => A (p4Q2PZ37AGN_spatialBoundary_embedding H p k))

/-- Four-link restriction followed by the verified cyclic Haar word pushes
the ORIGINAL spatial product Haar exactly to original one-link Haar. -/
theorem p4Q2PZ37AGN_originalPlaquetteCyclic_measurePreserving (p : Plq) :
    MeasurePreserving (p4Q2PZ37AGN_originalPlaquetteCyclicHolonomy H p) muH mu := by
  have hEdges := measurePreserving_finiteProductProbabilityEmbeddingRestriction
    mu (p4Q2PZ37AGN_spatialBoundary_embedding H p)
  have hWord := measurePreserving_haarFinFourCyclicPlaquetteWord mu
  simpa [p4Q2PZ37AGN_originalPlaquetteCyclicHolonomy,
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure,
    Function.comp_def] using hWord.comp hEdges

/-- Conjugation changes no original Wilson energy. The oriented physical
plaquette itself is retained throughout the expectation calculation. -/
theorem p4Q2PZ37AGN_originalPlaquette_energy_eq_cyclic (p : Plq) (A : Cfg) :
    specialUnitaryWilsonPlaquetteEnergy 2
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) =
      specialUnitaryWilsonPlaquetteEnergy 2
        (p4Q2PZ37AGN_originalPlaquetteCyclicHolonomy H p A) := by
  change specialUnitaryWilsonPlaquetteEnergy 2
      (orientedFourEdgePlaquetteWord
        (fun k => A (p4Q2PZ37AGN_spatialBoundary_embedding H p k))) = _
  exact specialUnitaryWilsonPlaquetteEnergy_orientedFourEdge_eq_cyclic
    (fun k => A (p4Q2PZ37AGN_spatialBoundary_embedding H p k))

/-- Genuine original plaquette energies are integrable in spatial Haar. -/
theorem p4Q2PZ37AGN_originalPlaquetteEnergy_integrable (p : Plq) :
    Integrable (fun A : Cfg => specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p)) muH := by
  have hOne : Integrable (specialUnitaryWilsonPlaquetteEnergy 2) mu :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- The established Haar transport avoids expanding the full dependent
  -- lattice topology during elaboration of four nested coordinate maps.
  have hMP := p4Q2PZ37AGN_originalPlaquetteCyclic_measurePreserving H p
  have hCyclic : Integrable (fun A : Cfg => specialUnitaryWilsonPlaquetteEnergy 2
      (p4Q2PZ37AGN_originalPlaquetteCyclicHolonomy H p A)) muH := by
    simpa only [Function.comp_def] using
      (MeasurePreserving.integrable_comp_of_integrable
        (μ := muH) (ν := mu)
        (f := p4Q2PZ37AGN_originalPlaquetteCyclicHolonomy H p)
        (g := specialUnitaryWilsonPlaquetteEnergy 2) hMP hOne)
  apply hCyclic.congr
  exact Filter.Eventually.of_forall
    (fun A => (p4Q2PZ37AGN_originalPlaquette_energy_eq_cyclic H p A).symm)

/-- Every original spatial plaquette, at every finite H, has exact Haar
energy expectation one. Shared links between different plaquettes require
no independence premise, because expectation is linear. -/
theorem p4Q2PZ37AGN_originalPlaquetteEnergy_mean_one (p : Plq) :
    (∫ A : Cfg, specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) ∂muH) = 1 := by
  have hMP := p4Q2PZ37AGN_originalPlaquetteCyclic_measurePreserving H p
  have hMeas : AEStronglyMeasurable (specialUnitaryWilsonPlaquetteEnergy 2)
      (Measure.map (p4Q2PZ37AGN_originalPlaquetteCyclicHolonomy H p) muH) := by
    rw [hMP.map_eq]
    exact (continuous_specialUnitaryWilsonPlaquetteEnergy 2).aestronglyMeasurable
  calc
    (∫ A : Cfg, specialUnitaryWilsonPlaquetteEnergy 2
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) ∂muH) =
      (∫ A : Cfg, specialUnitaryWilsonPlaquetteEnergy 2
        (p4Q2PZ37AGN_originalPlaquetteCyclicHolonomy H p A) ∂muH) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall
          (p4Q2PZ37AGN_originalPlaquette_energy_eq_cyclic H p)
    _ = (∫ g : G, specialUnitaryWilsonPlaquetteEnergy 2 g
        ∂Measure.map (p4Q2PZ37AGN_originalPlaquetteCyclicHolonomy H p) muH) :=
      (integral_map hMP.measurable.aemeasurable hMeas).symm
    _ = (∫ g : G, specialUnitaryWilsonPlaquetteEnergy 2 g ∂mu) := by
      rw [hMP.map_eq]
    _ = 1 := p4Q2PZ37AGN_originalOneLinkEnergy_mean_one

/-- The SAME original physical Hilbert centering scalar equals the literal
spatial plaquette-list length; the mean is no longer an unknown numerical input. -/
theorem p4Q2PZ37AGN_originalWilsonMean_exact : mH = pH := by
  rw [p4Q2PZ37AFZ_originalWilsonMean_eq_integral H]
  change (∫ A : Cfg, W A ∂muH) = pH
  calc
    (∫ A : Cfg, W A ∂muH) =
      (∫ A : Cfg, ∑ p : Plq, specialUnitaryWilsonPlaquetteEnergy 2
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) ∂muH) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall
          (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_eq_finset_sum H 2)
    _ = ∑ p : Plq, ∫ A : Cfg, specialUnitaryWilsonPlaquetteEnergy 2
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) ∂muH :=
      integral_finset_sum Finset.univ
        (fun p _ => p4Q2PZ37AGN_originalPlaquetteEnergy_integrable H p)
    _ = ∑ _p : Plq, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact p4Q2PZ37AGN_originalPlaquetteEnergy_mean_one H p
    _ = pH := by
      -- Nat.card forgets the locally chosen Fintype.ofFinite instance.
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        p4Q2PZ37AFZ_plaquetteCount,
        periodicHypercubicEvenSpatialSlicePlaquetteList,
        Finset.length_toList, Fintype.card_eq_nat_card]

/-- The exact mean is a zero-width rational enclosure of the original scalar. -/
def p4Q2PZ37AGN_originalWilsonMeanSingleton : p4Q2PZ37AFV_verifiedInterval mH where
  lower := (periodicHypercubicEvenSpatialSlicePlaquetteList H).length
  upper := (periodicHypercubicEvenSpatialSlicePlaquetteList H).length
  hLower := by
    rw [p4Q2PZ37AGN_originalWilsonMean_exact H]
    simp [p4Q2PZ37AFZ_plaquetteCount]
  hUpper := by
    rw [p4Q2PZ37AGN_originalWilsonMean_exact H]
    simp [p4Q2PZ37AFZ_plaquetteCount]

/-- Pointwise identity for the genuine continuous representative, not an
arbitrary chosen value of its Haar-L2 equivalence class. -/
theorem p4Q2PZ37AGN_originalCenteredContinuous_eq (A : Cfg) :
    fCont A = (W A - pH) / 2 := by
  change (1 / 2 : ℝ) * (W A - mH * 1) = (W A - pH) / 2
  rw [p4Q2PZ37AGN_originalWilsonMean_exact H]
  ring

/-- Exact centering halves the old unconditional source envelope. -/
theorem p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount (A : Cfg) :
    |fCont A| ≤ pH / 2 := by
  rw [p4Q2PZ37AGN_originalCenteredContinuous_eq H A]
  have hLo : 0 ≤ W A :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg
      H 2 (by norm_num) A
  have hHi : W A ≤ 2 * pH :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_le_two_mul_length
      H 2 (by norm_num) A
  apply abs_le.mpr
  constructor <;> linarith only [hLo, hHi]

/-- AGL's exact rational spatial action now gives exact rational centering. -/
def p4Q2PZ37AGN_centeredActionRational (A : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e)) : ℚ :=
  (p4Q2PZ37AGL_spatialActionRational H A a -
    (periodicHypercubicEvenSpatialSlicePlaquetteList H).length) / 2

theorem p4Q2PZ37AGN_originalCenteredContinuous_rational (A : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e)) :
    fCont A = (p4Q2PZ37AGN_centeredActionRational H A a : ℝ) := by
  rw [p4Q2PZ37AGN_originalCenteredContinuous_eq H A,
    p4Q2PZ37AGL_originalSpatialAction_exact H A a]
  simp [p4Q2PZ37AGN_centeredActionRational, p4Q2PZ37AFZ_plaquetteCount]

/-- Verified singleton of the same original continuous source at every
rational-coordinate configuration, including all AFQ center assignments. -/
def p4Q2PZ37AGN_originalCenteredSourceSingleton (A : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e)) :
    p4Q2PZ37AFV_verifiedInterval (fCont A) where
  lower := p4Q2PZ37AGN_centeredActionRational H A a
  upper := p4Q2PZ37AGN_centeredActionRational H A a
  hLower := (p4Q2PZ37AGN_originalCenteredContinuous_rational H A a).ge
  hUpper := (p4Q2PZ37AGN_originalCenteredContinuous_rational H A a).le

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGN_spatialShift_ne_self
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGN_spatialBoundary_injective
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGN_spatialBoundary_embedding
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGN_originalOneLinkEnergy_mean_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalPlaquetteCyclic_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalPlaquette_energy_eq_cyclic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalPlaquetteEnergy_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalPlaquetteEnergy_mean_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalWilsonMean_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalWilsonMeanSingleton
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalCenteredContinuous_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalCenteredContinuous_rational
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalCenteredSourceSingleton
