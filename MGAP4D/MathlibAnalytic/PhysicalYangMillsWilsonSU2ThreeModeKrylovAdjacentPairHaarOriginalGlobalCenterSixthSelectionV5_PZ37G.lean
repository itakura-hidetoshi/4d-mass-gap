import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSeventhPhysicalVandermondeV5_PZ37F
import Mathlib.Tactic

/-!
# P4-Q2-PZ37G — true original global SU(2) centre selection

The genuine central element z=-I simultaneously flips ALL spatial links.
Each original spatial plaquette has exactly four oriented links, so its
SU(2) holonomy and original Wilson half-action are unchanged.
The full temporal crossing Wilson energy transforms as C -> 2*N_H-C,
where N_H is the literal length of the original finite link list.

The ORIGINAL normalized product Haar measure is preserved. Thus every
spatial-Wilson-weighted ODD moment of C-N_H vanishes, at every even period
including H=0. This is a physical centre-symmetry result, not a new
posterior, surrogate measure, or assertion that the sixth obstruction
itself vanishes.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "z" => specialUnitaryTwoNegativeIdentity
local instance p4Q2PZ37G_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37G_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37G_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37G_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37G_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37G_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37G_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section GlobalCenterHaar
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Hol" => periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H
local notation "N" => ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ)

/-- The actual simultaneous central SU(2) multiplication on every original
spatial link, not a gauge-fixed or independent replacement configuration. -/
def p4Q2PZ37G_originalGlobalCenterFlip (A : Cfg) : Cfg :=
  fun e => z * A e

local notation "Flip" => p4Q2PZ37G_originalGlobalCenterFlip H

private theorem p4Q2PZ37G_center_square_one : z * z = (1 : G) := by
  calc
    z * z = z * z⁻¹ := by rw [p4Q2PV_originalSU2Center_inverse]
    _ = 1 := mul_inv_cancel z

private theorem p4Q2PZ37G_center_double_cancel (u v : G) :
    (u*z)*(v*z) = u*v := by
  calc
    (u*z)*(v*z) = ((u*z)*v)*z := by group
    _ = ((u*v)*z)*z := by rw [p4Q2PV_originalSU2Center_move_right]
    _ = (u*v)*(z*z) := by group
    _ = u*v := by rw [p4Q2PZ37G_center_square_one, mul_one]

/-- The four-link ORIGINAL spatial plaquette holonomy is unchanged by
flipping every spatial link by the genuine central -I. -/
theorem p4Q2PZ37G_originalGlobalFlip_plaquetteHolonomy
    (p : Plaq) (A : Cfg) :
    Hol (Flip A) p = Hol A p := by
  change
    (z*A (e0 p))*(z*A (e1 p))*
        (z*A (e2 p))⁻¹*(z*A (e3 p))⁻¹ =
      A (e0 p)*A (e1 p)*(A (e2 p))⁻¹*(A (e3 p))⁻¹
  rw [p4Q2PV_originalSU2Center_commutes (A (e0 p)),
    p4Q2PV_originalSU2Center_commutes (A (e1 p)),
    p4Q2PV_originalSU2Center_commutes (A (e2 p)),
    p4Q2PV_originalSU2Center_commutes (A (e3 p))]
  rw [p4Q2PV_originalSU2Center_inverse_mul,
    p4Q2PV_originalSU2Center_inverse_mul]
  calc
    (A (e0 p)*z)*(A (e1 p)*z)*
        ((A (e2 p))⁻¹*z)*((A (e3 p))⁻¹*z) =
      ((A (e0 p)*z)*(A (e1 p)*z))*
        (((A (e2 p))⁻¹*z)*((A (e3 p))⁻¹*z)) := by group
    _ = (A (e0 p)*A (e1 p))*
        ((A (e2 p))⁻¹*(A (e3 p))⁻¹) := by
          rw [p4Q2PZ37G_center_double_cancel,
            p4Q2PZ37G_center_double_cancel]
    _ = A (e0 p)*A (e1 p)*(A (e2 p))⁻¹*(A (e3 p))⁻¹ := by group

/-- Genuine spatial Wilson action, including EVERY original plaquette,
is center-even. No plaquette or finite period is omitted. -/
theorem p4Q2PZ37G_originalGlobalFlip_halfAction (A : Cfg) :
    w (Flip A) = w A := by
  unfold p4Q2PS_originalHalfSpatialAction
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction
  simp only [p4Q2PZ37G_originalGlobalFlip_plaquetteHolonomy]

/-- All temporal crossing plaquette energies reflect about their true
Haar-centre constant: Cross(Flip A,B) = 2*N_H - Cross(A,B). -/
theorem p4Q2PZ37G_originalGlobalFlip_crossing
    (A B : Cfg) :
    Cross (Flip A) B = 2*N-Cross A B := by
  have hE (e : Link) :
      E (((Flip A) e)⁻¹ * B e) =
        2 - E ((A e)⁻¹ * B e) := by
    have h := p4Q2PY7_originalTemporalLinkTrace_centerOdd H e A B
    rw [p4Q2PU_originalSingleLinkCenterFlip_at H e A] at h
    rw [← p4Q2PV_originalSU2Center_commutes (A e)] at h
    change 1-E (((Flip A) e)⁻¹ * B e) =
        -(1-E ((A e)⁻¹ * B e)) at h
    linarith
  have hSum (es : List Link) :
      (es.map fun e => E (((Flip A) e)⁻¹ * B e)).sum =
        2*(es.length : ℝ) -
          (es.map fun e => E ((A e)⁻¹ * B e)).sum := by
    induction es with
    | nil => simp
    | cons e es ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [hE e, ih]
        push_cast
        ring
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  exact hSum (periodicHypercubicEvenSpatialSliceLinkList H)

/-- The same ORIGINAL normalized spatial product Haar measure is invariant
under simultaneous central multiplication of every spatial link. -/
theorem p4Q2PZ37G_originalGlobalFlip_Haar_measurePreserving :
    MeasurePreserving Flip haar haar := by
  change MeasurePreserving
    (fun A : Cfg => fun e : Link => z*A e) haar haar
  exact p4Q2IX_actualSpatialHaar_leftTranslate_measurePreserving
    H (fun _ : Link => z)

private theorem p4Q2PZ37G_neg_odd_pow (t : ℝ) (k : ℕ) :
    (-t)^(2*k+1) = -(t^(2*k+1)) := by
  calc
    (-t)^(2*k+1) = ((-t)^2)^k * (-t) := by
      rw [pow_add, pow_mul, pow_one]
    _ = -((t^2)^k*t) := by
      rw [show (-t)^2=t^2 by ring]
      ring
    _ = -(t^(2*k+1)) := by
      rw [pow_add, pow_mul, pow_one]

/-- ORIGINAL finite-volume Haar odd-moment selection for EVERY spatial
Wilson power i and EVERY odd centred temporal-crossing degree 2k+1.
The source observable remains the true original w(X), Cross(X,B).
No unproved Haar moment or sixth-vanishing condition is used. -/
theorem p4Q2PZ37G_originalWeightedCenteredCrossing_oddHaar_zero
    (i k : ℕ) (B : Cfg) :
    (∫ X : Cfg, (w X)^i*(Cross X B-N)^(2*k+1) ∂haar) = 0 := by
  let f : Cfg → ℝ := fun X => (w X)^i*(Cross X B-N)^(2*k+1)
  have hw := p4Q2PZ36C_half_continuous H
  have hc := p4Q2PZ36C_cross_continuous H B
  have hf : Continuous f := (hw.pow i).mul ((hc.sub continuous_const).pow (2*k+1))
  have hOdd (X : Cfg) : f (Flip X) = -f X := by
    dsimp [f]
    rw [p4Q2PZ37G_originalGlobalFlip_halfAction H X,
      p4Q2PZ37G_originalGlobalFlip_crossing H X B]
    have hcenter : (2*N-Cross X B)-N = -(Cross X B-N) := by ring
    rw [hcenter, p4Q2PZ37G_neg_odd_pow]
    ring
  have hPres := p4Q2PZ37G_originalGlobalFlip_Haar_measurePreserving H
  have hmap : Measure.map Flip haar = haar := hPres.map_eq
  have hStrong : AEStronglyMeasurable f (Measure.map Flip haar) := by
    rw [hmap]
    exact hf.measurable.aestronglyMeasurable
  have hInvariance :
      (∫ X : Cfg, f X ∂haar) = (∫ X : Cfg, f (Flip X) ∂haar) := by
    calc
      (∫ X : Cfg, f X ∂haar) =
          (∫ X : Cfg, f X ∂Measure.map Flip haar) := by rw [hmap]
      _ = (∫ X : Cfg, f (Flip X) ∂haar) :=
        MeasureTheory.integral_map hPres.measurable.aemeasurable hStrong
  have hNegative :
      (∫ X : Cfg, f (Flip X) ∂haar) =
        -(∫ X : Cfg, f X ∂haar) := by
    calc
      (∫ X : Cfg, f (Flip X) ∂haar) =
          (∫ X : Cfg, -f X ∂haar) := by
            apply integral_congr_ae
            filter_upwards with X
            exact hOdd X
      _ = -(∫ X : Cfg, f X ∂haar) := by rw [integral_neg]
  change (∫ X : Cfg, f X ∂haar) = 0
  linarith

end GlobalCenterHaar
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37G_originalGlobalFlip_plaquetteHolonomy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37G_originalGlobalFlip_halfAction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37G_originalGlobalFlip_crossing
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37G_originalGlobalFlip_Haar_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37G_originalWeightedCenteredCrossing_oddHaar_zero
