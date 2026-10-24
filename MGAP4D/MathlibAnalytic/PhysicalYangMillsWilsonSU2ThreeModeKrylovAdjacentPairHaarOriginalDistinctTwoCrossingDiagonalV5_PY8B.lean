import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalDiagonalPlaquetteGaugeWardV5_PY8
import Mathlib.Tactic

/-!
# P4-Q2-PY8B — exact diagonal χ_p² and distinct temporal crossing Haar Ward

For two different actual temporal links e≠f, the normalized SU(2)
real trace τ_e(A,B)=1−E((A_e)⁻¹B_e) changes sign under the source-link
center -I flip at e. The true squared spatial plaquette real character
χ_p(A)² is EVEN under center flips at EVERY original link.

PY7C consequently proves the original Haar pairings
∫χ_p² τ_e, ∫χ_p² τ_f, ∫χ_p² τ_e τ_f ALL vanish, without
assuming independent Wilson posteriors. Since E_e E_f =
(1−τ_e)(1−τ_f), the full diagonal χ_p²-weighted two-DISTINCT-link
temporal crossing energy integral equals ∫χ_p², independent of B.
The equal-link case is already PY8's genuine gauge Ward.
No sorry, new axiom, rank or arbitrary spectral surrogate.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY8B_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY8B_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY8B_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY8B_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY8B_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalDistinctTwoCrossingDiagonal
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H

/-- Both distinct original temporal crossing factors leave exactly
the spatial χ_p² Haar mean: the linear and double trace terms are
killed by genuine center flips, with e≠f explicitly checked. -/
theorem p4Q2PY8_originalPlaquetteSquare_distinctCrossingPair_Haar_eq_const
    (p : Plaq) (e f : Link) (hef : e ≠ f) (B : Cfg) :
    (∫ A : Cfg, (χ p A)^2 *
      (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) =
      (∫ A : Cfg, (χ p A)^2 ∂haar) := by
  let obs0 : Cfg → ℝ := fun A => (χ p A)^2
  let obs1 : Cfg → ℝ := fun A =>
    obs0 A * (1 - E ((A e)⁻¹ * B e))
  let obs2 : Cfg → ℝ := fun A =>
    obs0 A * (1 - E ((A f)⁻¹ * B f))
  let obs12 : Cfg → ℝ := fun A =>
    obs0 A * ((1 - E ((A e)⁻¹ * B e)) *
      (1 - E ((A f)⁻¹ * B f)))
  have hChi : Continuous (fun A : Cfg => χ p A) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H p
  have hE (d : Link) :
      Continuous (fun A : Cfg => E ((A d)⁻¹ * B d)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply d).inv.mul continuous_const)
  have hc0 : Continuous obs0 := hChi.pow 2
  have hc1 : Continuous obs1 :=
    hc0.mul (continuous_const.sub (hE e))
  have hc2 : Continuous obs2 :=
    hc0.mul (continuous_const.sub (hE f))
  have hc12 : Continuous obs12 :=
    hc0.mul ((continuous_const.sub (hE e)).mul
      (continuous_const.sub (hE f)))
  have hi0 : Integrable obs0 haar :=
    hc0.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable obs1 haar :=
    hc1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable obs2 haar :=
    hc2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi12 : Integrable obs12 haar :=
    hc12.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hInt1 : (∫ A : Cfg, obs1 A ∂haar) = 0 :=
    p4Q2PY7_originalPlaquetteSquare_oneTemporalTrace_Haar_zero H p e B
  have hInt2 : (∫ A : Cfg, obs2 A ∂haar) = 0 :=
    p4Q2PY7_originalPlaquetteSquare_oneTemporalTrace_Haar_zero H p f B
  have hInt12 : (∫ A : Cfg, obs12 A ∂haar) = 0 :=
    p4Q2PY7_originalPlaquetteSquare_twoDistinctTemporalTraces_Haar_zero
      H p e f hef B
  have hSub1 :
      (∫ A : Cfg, obs0 A - obs1 A ∂haar) =
        (∫ A : Cfg, obs0 A ∂haar) -
          (∫ A : Cfg, obs1 A ∂haar) := by
    simpa only [Pi.sub_apply] using (integral_sub hi0 hi1)
  have hSub2 :
      (∫ A : Cfg, (obs0 A - obs1 A) - obs2 A ∂haar) =
        (∫ A : Cfg, obs0 A - obs1 A ∂haar) -
          (∫ A : Cfg, obs2 A ∂haar) := by
    simpa only [Pi.sub_apply] using (integral_sub (hi0.sub hi1) hi2)
  have hAdd :
      (∫ A : Cfg, ((obs0 A - obs1 A) - obs2 A) + obs12 A ∂haar) =
        (∫ A : Cfg, (obs0 A - obs1 A) - obs2 A ∂haar) +
          (∫ A : Cfg, obs12 A ∂haar) := by
    simpa only [Pi.add_apply] using
      (integral_add ((hi0.sub hi1).sub hi2) hi12)
  have hPoint (A : Cfg) :
      (χ p A)^2 *
        (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) =
      ((obs0 A - obs1 A) - obs2 A) + obs12 A := by
    dsimp [obs0, obs1, obs2, obs12]
    ring
  calc
    (∫ A : Cfg, (χ p A)^2 *
        (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) =
      (∫ A : Cfg, ((obs0 A - obs1 A) - obs2 A) + obs12 A ∂haar) := by
        apply integral_congr_ae
        filter_upwards with A
        exact hPoint A
    _ = (∫ A : Cfg, obs0 A ∂haar) -
        (∫ A : Cfg, obs1 A ∂haar) -
        (∫ A : Cfg, obs2 A ∂haar) +
        (∫ A : Cfg, obs12 A ∂haar) := by
      rw [hAdd, hSub2, hSub1]
    _ = (∫ A : Cfg, (χ p A)^2 ∂haar) := by
      rw [hInt1, hInt2, hInt12]
      simp [obs0]

/-- The genuine χ_p²-weighted distinct-link temporal energy product
Haar pairing is exactly unchanged for ANY two original right
spatial configurations, without posterior factorization. -/
theorem p4Q2PY8_originalPlaquetteSquare_distinctCrossingPair_Haar_invariant
    (p : Plaq) (e f : Link) (hef : e ≠ f) (B : Cfg) :
    (∫ A : Cfg, (χ p A)^2 *
      (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) =
    (∫ A : Cfg, (χ p A)^2 *
      (E ((A e)⁻¹) * E ((A f)⁻¹)) ∂haar) := by
  calc
    (∫ A : Cfg, (χ p A)^2 *
      (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) =
      (∫ A : Cfg, (χ p A)^2 ∂haar) :=
        p4Q2PY8_originalPlaquetteSquare_distinctCrossingPair_Haar_eq_const
          H p e f hef B
    _ = (∫ A : Cfg, (χ p A)^2 *
      (E ((A e)⁻¹) * E ((A f)⁻¹)) ∂haar) := by
      simpa only [Pi.one_apply, mul_one] using
        (p4Q2PY8_originalPlaquetteSquare_distinctCrossingPair_Haar_eq_const
          H p e f hef (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))).symm

end OriginalDistinctTwoCrossingDiagonal
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY8_originalPlaquetteSquare_distinctCrossingPair_Haar_eq_const
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY8_originalPlaquetteSquare_distinctCrossingPair_Haar_invariant
