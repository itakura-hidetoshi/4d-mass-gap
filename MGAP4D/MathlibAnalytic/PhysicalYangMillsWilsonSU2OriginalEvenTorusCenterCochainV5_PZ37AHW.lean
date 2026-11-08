import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCubicHaarMomentEnclosureV5_PZ37AHV
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorEdgeMatching
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPlaquetteCenterTraceV5_PV
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHW — concrete even-torus spatial SU(2) center-flux cochain

The preceding AHV conditional M3=0 lemma requires an ACTUAL original
product-Haar-preserving center-odd spatial configuration map.

For original finite periodic spatial links (x,j), define the explicit
Z/2 1-cochain tau_j(x)=sum_{i<j} parity(x_i), using the already proved
even-torus parity homomorphism (which is well-defined at all H).

For any spatial plaquette i<j, its four real original oriented
links (e0,e1,e2,e3) satisfy
  tau(e0) + tau(e1) + tau(e2) + tau(e3) = 1 in ZMod 2.

Construct the genuine rank-two SU(2) center sign 1 or -I from this
cochain and an explicit transformation of the original configuration
which right-multiplies each original spatial link by its true center
element. The original normalized product Haar is unchanged because
each coordinate is Haar-right-translated by a fixed SU(2) group element.

The plaquette sign, original ZW source flip, and M3=0 require that
the center-flux cochain be transported through the actual ordered
four-edge holonomy; those are separate typed lemmas in this leaf.

No new axiom, no assumed twist existence, no independent posterior,
no changes to original physical one-slab Wilson action or Haar model,
no claim of transfer sign, uniform coercivity or YM gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHW_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHW_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHW_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHW_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHW_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Vertex" => PeriodicHypercubicEvenSpatialSliceVertex H
local notation "Dir" => PeriodicHypercubicEvenSpatialDirection
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "μ" => normalizedCompactHaar G
local notation "z" => specialUnitaryTwoNegativeIdentity
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H

local instance p4Q2PZ37AHW_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AHW_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The explicit ZMod 2 center flux 1-cochain on the ACTUAL original
even-periodic spatial-slice positive links. -/
def p4Q2PZ37AHW_originalCenterCochain (e : Link) : ZMod 2 :=
  ∑ i : Fin 4, if i < e.2.1 then
    periodicHypercubicEvenCoordinateParity H e.1.1 i else 0

local notation "τ" => p4Q2PZ37AHW_originalCenterCochain H

/-- A one-step spatial translation changes the center cochain by 1
precisely when the shift direction precedes the link direction. -/
theorem p4Q2PZ37AHW_originalCenterCochain_shift
    (v : Vertex) (mu nu : Dir) :
    τ (periodicHypercubicEvenSpatialSliceShift H v mu, nu) =
      τ (v, nu) + if mu.1 < nu.1 then 1 else 0 := by
  classical
  unfold p4Q2PZ37AHW_originalCenterCochain
  simp_rw [periodicHypercubicEvenSpatialSliceShift_coe,
    periodicHypercubicEvenCoordinateParity_shift]
  calc
    (∑ i : Fin 4,
      if i < nu.1 then
        periodicHypercubicEvenCoordinateParity H v.1 i +
          (if i = mu.1 then (1 : ZMod 2) else 0)
      else 0) =
        (∑ i : Fin 4,
          if i < nu.1 then periodicHypercubicEvenCoordinateParity H v.1 i else 0) +
        (∑ i : Fin 4,
          if i < nu.1 then (if i = mu.1 then (1 : ZMod 2) else 0) else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases h : i < nu.1 <;> simp [h]
    _ = (∑ i : Fin 4,
          if i < nu.1 then periodicHypercubicEvenCoordinateParity H v.1 i else 0) +
          (if mu.1 < nu.1 then 1 else 0) := by
        congr 1
        have hReindex :
            (∑ i : Fin 4,
              if i < nu.1 then
                (if i = mu.1 then (1 : ZMod 2) else 0) else 0) =
              ∑ i : Fin 4,
                if i = mu.1 then
                  (if mu.1 < nu.1 then (1 : ZMod 2) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro i _hi
          by_cases hi : i = mu.1
          · subst i
            simp
          · simp [hi]
        rw [hReindex]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The true original four-link oriented plaquette has ODD center flux
in the genuine ZMod 2 cochain; all H including the period-two torus. -/
theorem p4Q2PZ37AHW_originalCenterCochain_plaquette
    (p : Plaq) :
    τ (e0 p) + τ (e1 p) + τ (e2 p) + τ (e3 p) = 1 := by
  have hlt : p.2.1.1.1 < p.2.1.2.1 := p.2.2
  have hgt : ¬ p.2.1.2.1 < p.2.1.1.1 := not_lt.mpr hlt.le
  have h1 :=
    p4Q2PZ37AHW_originalCenterCochain_shift
      H p.1 p.2.1.1 p.2.1.2
  have h2 :=
    p4Q2PZ37AHW_originalCenterCochain_shift
      H p.1 p.2.1.2 p.2.1.1
  simp only [hlt, hgt, ↓reduceIte, add_zero] at h1 h2
  change τ (e1 p) = τ (e3 p) + 1 at h1
  change τ (e2 p) = τ (e0 p) at h2
  rw [h1, h2]
  have hcancel (a : ZMod 2) : a + a = 0 := by
    have h2zero : (2 : ZMod 2) = 0 := by decide
    calc
      a + a = (2 : ZMod 2) * a := by ring
      _ = 0 := by rw [h2zero]; ring
  calc
    τ (e0 p) + (τ (e3 p) + 1) + τ (e0 p) + τ (e3 p) =
      (τ (e0 p) + τ (e0 p)) + (τ (e3 p) + τ (e3 p)) + 1 := by abel
    _ = 1 := by rw [hcancel, hcancel]; ring

/-- The authentic SU(2) negative identity squares to group identity. -/
theorem p4Q2PZ37AHW_originalCenter_square :
    z * z = (1 : G) := by
  calc
    z * z = z * z⁻¹ := by rw [p4Q2PV_originalSU2Center_inverse]
    _ = 1 := mul_inv_cancel z

/-- Lift each genuine cochain bit to the ACTUAL central SU(2) element. -/
def p4Q2PZ37AHW_originalCenterSign (a : ZMod 2) : G :=
  if a = 0 then 1 else z

local notation "s" => p4Q2PZ37AHW_originalCenterSign

theorem p4Q2PZ37AHW_originalCenterSign_zero :
    s 0 = (1 : G) := by simp [p4Q2PZ37AHW_originalCenterSign]

theorem p4Q2PZ37AHW_originalCenterSign_one :
    s 1 = z := by
  simp [p4Q2PZ37AHW_originalCenterSign]

theorem p4Q2PZ37AHW_originalCenterSign_add (a b : ZMod 2) :
    s (a + b) = s a * s b := by
  have hOne : (1 : ZMod 2) ≠ 0 := by decide
  have hAdd : (1 : ZMod 2) + 1 = 0 := by decide
  fin_cases a <;> fin_cases b <;>
    simp only [p4Q2PZ37AHW_originalCenterSign,
      zero_add, add_zero, hAdd, if_pos rfl, if_neg hOne,
      one_mul, mul_one, p4Q2PZ37AHW_originalCenter_square]

theorem p4Q2PZ37AHW_originalCenterSign_inv (a : ZMod 2) :
    (s a)⁻¹ = s a := by
  have hOne : (1 : ZMod 2) ≠ 0 := by decide
  fin_cases a <;>
    simp only [p4Q2PZ37AHW_originalCenterSign,
      if_pos rfl, if_neg hOne, inv_one,
      p4Q2PV_originalSU2Center_inverse]

theorem p4Q2PZ37AHW_originalCenterSign_commutes (a : ZMod 2) (u : G) :
    s a * u = u * s a := by
  fin_cases a <;>
    simp [p4Q2PZ37AHW_originalCenterSign,
      p4Q2PV_originalSU2Center_commutes]

/-- The actual original spatial link SU(2) variables are center-twisted
by their explicit even-torus cochain; no substitute configuration. -/
def p4Q2PZ37AHW_originalCenterTwist (A : Cfg) : Cfg :=
  fun e => A e * s (τ e)

local notation "T" => p4Q2PZ37AHW_originalCenterTwist H

/-- Every actual coordinate's fixed original center translation preserves
the UNCHANGED normalized SU(2) Haar measure. -/
theorem p4Q2PZ37AHW_originalCenterTwist_coordinate_measurePreserving
    (e : Link) :
    MeasurePreserving (fun u : G => u * s (τ e)) μ μ := by
  simpa using
    (normalizedCompactHaar_measurePreserving_mul_left_right
      G (1 : G) (s (τ e)))

/-- The explicit original all-link twist preserves the original SU(2)
spatial finite product Haar, NOT an independent artificial posterior. -/
theorem p4Q2PZ37AHW_originalCenterTwist_Haar_measurePreserving :
    MeasurePreserving T muH muH := by
  refine ⟨?_, ?_⟩
  · unfold p4Q2PZ37AHW_originalCenterTwist
    refine measurable_pi_lambda _ ?_
    intro e
    exact
      (p4Q2PZ37AHW_originalCenterTwist_coordinate_measurePreserving H e).measurable.comp
        (measurable_pi_apply e)
  · unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    let f : Link → G → G := fun e u => u * s (τ e)
    have hf : ∀ e, AEMeasurable (f e) μ :=
      fun e =>
        (p4Q2PZ37AHW_originalCenterTwist_coordinate_measurePreserving
          H e).measurable.aemeasurable
    letI : ∀ e, SigmaFinite (Measure.map (f e) μ) := fun e => by
      rw [(p4Q2PZ37AHW_originalCenterTwist_coordinate_measurePreserving H e).map_eq]
      infer_instance
    rw [show T = (fun A e => f e (A e)) by rfl]
    rw [Measure.pi_map_pi hf]
    congr 1
    funext e
    exact
      (p4Q2PZ37AHW_originalCenterTwist_coordinate_measurePreserving H e).map_eq

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW_originalCenterCochain_shift
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW_originalCenterCochain_plaquette
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW_originalCenter_square
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW_originalCenterSign_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW_originalCenterSign_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW_originalCenterSign_add
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW_originalCenterSign_inv
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW_originalCenterSign_commutes
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW_originalCenterTwist_coordinate_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHW_originalCenterTwist_Haar_measurePreserving
