import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalHaarCenteredPhysicalSourceNormV5_MZ
import MGAP4D.MathlibAnalytic.CompactGaugeWilsonGaugeInvariance
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedReceiverOneLinkOscillationV5_MP
import Mathlib.Tactic

/-!
# P4-Q2-NA — original physical SU(2) Wilson plaquette: one-link Haar fiber

MZ transports the genuine plaquette source-Haar fluctuation into the
Gauss-law physical Hilbert norm. For the original positive interacting
Wilson kernel, a volume-independent Harnack constant is already proved
for ONE actual source-side spatial link in MP.

NA proves that for EVERY original spatial plaquette p and arbitrary
background spatial configuration A, refreshing only its FIRST actual
SU(2) link by normalized Haar makes its original Wilson holonomy
Haar, and its real Wilson energy variance exactly the fixed
positive universal V_SU2 of MY. This is proved by explicit original
four-edge geometric distinctness, the ORIGINAL oriented Wilson
holonomy, and the true compact SU(2) Haar right-translation theorem.
It is not an artificial scalar observable or replacement for any of
the TWO original interacting Wilson posterior laws.

This is a local disintegration input for the next step: combining
the original source-link Harnack bound exp(8 b) with the exact fiber
variance and product-Haar Fubini to bound the genuinely
K_b-weighted conditional variance uniformly in the lattice volume.

Nothing here assumes spatial mixing, signed receiver positivity,
new physical source/detector, Dobrushin, a lower rank, H1-C3 closure,
or continuum Yang-Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NA_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NA_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NA_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NA_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NA_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalOneLinkGeometry
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "mu" => normalizedCompactHaar Gauge
local notation "w" => p4Q2LO_originalLocalPlaquetteContinuous H

/-- The THREE unchanged genuine spatial links contributing the right
factor after the FIRST plaquette SU(2) link is varied. -/
noncomputable def p4Q2NA_originalPlaquetteFirstLinkRightFactor
    (p : Plaq) (A : Cfg) : Gauge :=
  A (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.1,p.2.1.2) *
    (A (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.2,p.2.1.1))⁻¹ *
    (A (p.1,p.2.1.2))⁻¹

/-- The actual physical Wilson energy becomes WilsonEnergy(g*q) when
the FIRST actual plaquette link is updated to g; all remaining
three positive links are genuinely distinct, even at side length 2. -/
theorem p4Q2NA_originalPlaquette_firstLink_energy_eq_affine
    (p : Plaq) (A : Cfg) (g : Gauge) :
    w p (Function.update A (p.1,p.2.1.1) g) =
      specialUnitaryWilsonPlaquetteEnergy 2
        (g * p4Q2NA_originalPlaquetteFirstLinkRightFactor H p A) := by
  let v := p.1
  let ax1 := p.2.1.1
  let ax2 := p.2.1.2
  let e0 : Link := (v,ax1)
  let e1 : Link := (periodicHypercubicEvenSpatialSliceShift H v ax1,ax2)
  let e2 : Link := (periodicHypercubicEvenSpatialSliceShift H v ax2,ax1)
  let e3 : Link := (v,ax2)
  have hne := p4Q2MV_originalSpatialPlaquette_firstLink_otherThree_ne H p
  dsimp only at hne
  rcases hne with ⟨h1,h2,h3⟩
  have hf0 : (Function.update A e0 g) e0 = g := by
    simp [Function.update]
  have hf1 : (Function.update A e0 g) e1 = A e1 := by
    simp [Function.update, e1, e0, v, ax1, ax2, h1]
  have hf2 : (Function.update A e0 g) e2 = A e2 := by
    simp [Function.update, e2, e0, v, ax1, ax2, h2]
  have hf3 : (Function.update A e0 g) e3 = A e3 := by
    simp [Function.update, e3, e0, v, ax1, ax2, h3]
  change specialUnitaryWilsonPlaquetteEnergy 2
      ((Function.update A e0 g) e0 *
        (Function.update A e0 g) e1 *
        ((Function.update A e0 g) e2)⁻¹ *
        ((Function.update A e0 g) e3)⁻¹) =
    specialUnitaryWilsonPlaquetteEnergy 2
      (g * (A e1 * (A e2)⁻¹ * (A e3)⁻¹))
  rw [hf0, hf1, hf2, hf3]
  congr 1
  group

/-- The original SU(2) Haar law of a single refreshed genuine plaquette
link: all other links may be frozen arbitrarily. Hence unlike the
interacting posterior this fiber identity is independent of H and p. -/
theorem p4Q2NA_originalPlaquette_oneLinkHaar_energyTest_transport
    (p : Plaq) (A : Cfg) (test : C(ℝ,ℝ)) :
    (∫ g : Gauge,
      test (w p (Function.update A (p.1,p.2.1.1) g)) ∂mu) =
      ∫ h : Gauge,
        test (specialUnitaryWilsonPlaquetteEnergy 2 h) ∂mu := by
  let q : Gauge := p4Q2NA_originalPlaquetteFirstLinkRightFactor H p A
  have hmp : MeasurePreserving (fun g : Gauge => g * q) mu mu := by
    simpa only [one_mul] using
      (normalizedCompactHaar_measurePreserving_mul_left_right
        Gauge (1 : Gauge) q)
  let f : Gauge → ℝ := fun h => test (specialUnitaryWilsonPlaquetteEnergy 2 h)
  have hf : StronglyMeasurable f :=
    (test.continuous.comp
      (continuous_specialUnitaryWilsonPlaquetteEnergy 2)).stronglyMeasurable
  have hchange :=
    integral_map_of_stronglyMeasurable
      (μ := mu) (φ := fun g : Gauge => g * q)
      hmp.measurable hf
  rw [hmp.map_eq] at hchange
  calc
    (∫ g : Gauge,
      test (w p (Function.update A (p.1,p.2.1.1) g)) ∂mu) =
        ∫ g : Gauge,
          f (g * q) ∂mu := by
            apply integral_congr_ae
            filter_upwards with g
            rw [p4Q2NA_originalPlaquette_firstLink_energy_eq_affine H p A g]
    _ = ∫ h : Gauge, f h ∂mu := hchange.symm

/-- The ORIGINAL one-link Haar-refresh centered Wilson energy of ANY
genuine physical plaquette has EXACTLY the same variance as MY's
single-SU(2) class function, for every surrounding configuration. -/
theorem p4Q2NA_originalPlaquette_oneLinkHaarVariance_eq_universal
    (p : Plaq) (A : Cfg) :
    (∫ g : Gauge,
      (w p (Function.update A (p.1,p.2.1.1) g) -
        p4Q2MY_singleSU2HaarWilsonMean)^2 ∂mu) =
      p4Q2MY_singleSU2HaarWilsonVariance := by
  let test : C(ℝ,ℝ) :=
    ⟨fun x => (x-p4Q2MY_singleSU2HaarWilsonMean)^2,
      ((continuous_id.sub continuous_const).pow 2)⟩
  simpa only [test, ContinuousMap.coe_mk,
    p4Q2MY_singleSU2HaarWilsonVariance] using
    (p4Q2NA_originalPlaquette_oneLinkHaar_energyTest_transport H p A test)

/-- Strictly positive H-independent Haar-refresh Wilson fluctuation,
even with EVERY other genuine original SU(2) spatial link frozen. -/
theorem p4Q2NA_originalPlaquette_oneLinkHaarVariance_uniform_pos
    (p : Plaq) (A : Cfg) :
    0 <
      ∫ g : Gauge,
        (w p (Function.update A (p.1,p.2.1.1) g) -
          p4Q2MY_singleSU2HaarWilsonMean)^2 ∂mu := by
  rw [p4Q2NA_originalPlaquette_oneLinkHaarVariance_eq_universal H p A]
  exact p4Q2MY_singleSU2HaarWilsonVariance_pos

end OriginalOneLinkGeometry
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NA_originalPlaquette_firstLink_energy_eq_affine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NA_originalPlaquette_oneLinkHaar_energyTest_transport
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NA_originalPlaquette_oneLinkHaarVariance_eq_universal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NA_originalPlaquette_oneLinkHaarVariance_uniform_pos
