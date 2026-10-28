import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorSpatialHaarTransportV5_PZ37AAQ
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabKernel
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAR — true finite Wilson one-slab spatial-translation covariance

Continue exact AAP link orbits and the AAQ ORIGINAL spatial/pair Haar transport.
The true positive spatial Wilson plaquettes have their own bijective
spatial translations; this file proves their exact 4-link holonomy
covariance by transporting the ORIGINAL spatial link variables.

Consequently the ACTUAL spatial Wilson action and the ACTUAL temporal
crossing action are invariant under simultaneous spatial reindexing,
so the original complete symmetric one-slab action and its true
Wilson Boltzmann kernel are covariant.

These are unconditional GEOMETRIC/FINITE-ACTION theorems on the genuine
original model. They are the first required input for subsequently proving
spatial invariance of the physical positive continuous Perron vacuum,
the original interacting one-link posterior densities, and the unchanged
centered Gauss-law physical receiver.

No direct assertion of either latter covariance is made here; in
particular AAP's integrated posterior response covariance and its
1/3-participation consequence remain conditional. No Haar replacement,
new axioms, sorry/admit/native_decide, volume-uniform coercivity,
positive fine interval, endpoint E/F, H1-H4 or continuum 4D mass gap.
Append-only: no existing theorem carrier is modified.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AAR_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAR_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAR_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAR_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAR_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

private noncomputable instance p4Q2PZ37AAR_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
private noncomputable instance p4Q2PZ37AAR_plaquetteFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section OriginalOneSlabTranslation
variable (H : ℕ)
local notation "V" => PeriodicHypercubicEvenSpatialSliceVertex H
local notation "D" => PeriodicHypercubicEvenSpatialDirection
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "P" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Disp" => PeriodicHypercubicEvenSpatialDisplacement H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2

/-- Translate genuine spatial plaquette bases, preserving their
ORIGINAL ordered two spatial directions. -/
def p4Q2PZ37AAR_actualSpatialPlaquetteTranslation
    (a : Disp) : P ≃ P :=
  Equiv.prodCongr
    (p4Q2PZ37AAP_actualSpatialVertexTranslation H a)
    (Equiv.refl PeriodicHypercubicEvenSpatialDirectionPair)

/-- Original spatial unit shifts commute exactly with spatial
translation of the time-zero base vertex, including at H=0. -/
theorem p4Q2PZ37AAR_originalSpatialShift_translation
    (a : Disp) (v : V) (mu : D) :
    p4Q2PZ37AAP_actualSpatialVertexTranslation H a
      (periodicHypercubicEvenSpatialSliceShift H v mu) =
    periodicHypercubicEvenSpatialSliceShift H
      (p4Q2PZ37AAP_actualSpatialVertexTranslation H a v) mu := by
  apply Subtype.ext
  change
    periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) v.1 mu.1 + a.1 =
      periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) (v.1 + a.1) mu.1
  exact (periodicHypercubicShift_add
    (PeriodicHypercubicEvenSideLength H) v.1 a.1 mu.1).symm

/-- A TRUE four-link spatial plaquette holonomy is unchanged when
its four ORIGINAL links and its plaquette base are translated
simultaneously. No averaged or reference connection is used. -/
theorem p4Q2PZ37AAR_originalSpatialPlaquetteHolonomy_translation
    (a : Disp) (A : Cfg) (p : P) :
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
      (p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a A)
      (p4Q2PZ37AAR_actualSpatialPlaquetteTranslation H a p) =
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p := by
  let Tv := p4Q2PZ37AAP_actualSpatialVertexTranslation H a
  let Tc := p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a
  have hAt (v : V) (d : D) :
      Tc A (Tv v, d) = A (v, d) :=
    p4Q2PZ37AAQ_configurationTranslation_apply_translatedLink H a A (v, d)
  have hShift (v : V) (mu nu : D) :
      Tc A (periodicHypercubicEvenSpatialSliceShift H (Tv v) mu, nu) =
        A (periodicHypercubicEvenSpatialSliceShift H v mu, nu) := by
    rw [← p4Q2PZ37AAR_originalSpatialShift_translation H a v mu]
    exact hAt (periodicHypercubicEvenSpatialSliceShift H v mu) nu
  change
    Tc A (Tv p.1, p.2.1.1) *
      Tc A (periodicHypercubicEvenSpatialSliceShift H (Tv p.1) p.2.1.1,
        p.2.1.2) *
      (Tc A (periodicHypercubicEvenSpatialSliceShift H (Tv p.1) p.2.1.2,
        p.2.1.1))⁻¹ *
      (Tc A (Tv p.1, p.2.1.2))⁻¹ =
    A (p.1, p.2.1.1) *
      A (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.1,
        p.2.1.2) *
      (A (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.2,
        p.2.1.1))⁻¹ *
      (A (p.1, p.2.1.2))⁻¹
  rw [hAt p.1 p.2.1.1, hShift p.1 p.2.1.1 p.2.1.2,
    hShift p.1 p.2.1.2 p.2.1.1, hAt p.1 p.2.1.2]

/-- Exact finite-sum form of the ORIGINAL spatial Wilson action
on the complete time-zero spatial plaquette set. -/
private theorem p4Q2PZ37AAR_originalSpatialAction_eq_sum
    (A : Cfg) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 A =
      ∑ p : P,
        specialUnitaryWilsonPlaquetteEnergy 2
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) := by
  classical
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction
    periodicHypercubicEvenSpatialSlicePlaquetteList
  exact Finset.sum_map_toList
    (s := (Finset.univ : Finset P))
    (f := fun p : P =>
      specialUnitaryWilsonPlaquetteEnergy 2
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p))

/-- UNCONDITIONAL exact spatial translation symmetry of the
ORIGINAL genuine SU(2) time-zero spatial Wilson action. -/
theorem p4Q2PZ37AAR_originalSpatialWilsonAction_translation
    (a : Disp) (A : Cfg) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
      (p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a A) =
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 A := by
  rw [p4Q2PZ37AAR_originalSpatialAction_eq_sum H,
    p4Q2PZ37AAR_originalSpatialAction_eq_sum H]
  rw [← Equiv.sum_comp (p4Q2PZ37AAR_actualSpatialPlaquetteTranslation H a)]
  apply Finset.sum_congr rfl
  intro p _hp
  exact congrArg (specialUnitaryWilsonPlaquetteEnergy 2)
    (p4Q2PZ37AAR_originalSpatialPlaquetteHolonomy_translation H a A p)

/-- The original actual spatial action CONTINUOUS Wilson source, not
a substituted detector, is invariant at every configuration. -/
theorem p4Q2PZ37AAR_originalPhysicalSpatialWilsonSource_translation
    (a : Disp) (A : Cfg) :
    p4Q2JI_actualSpatialWilsonContinuous H
      (p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a A) =
    p4Q2JI_actualSpatialWilsonContinuous H A := by
  exact p4Q2PZ37AAR_originalSpatialWilsonAction_translation H a A

/-- Exact finite-sum presentation of the ORIGINAL temporal crossing
Wilson action over ALL genuine positive spatial links. -/
private theorem p4Q2PZ37AAR_originalCrossingAction_eq_sum
    (A B : Cfg) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B =
      ∑ e : Link,
        specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * B e) := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
    periodicHypercubicEvenSpatialSliceLinkList
  exact Finset.sum_map_toList
    (s := (Finset.univ : Finset Link))
    (f := fun e : Link =>
      specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * B e))

/-- The original temporal crossing action of TWO adjacent physical
spatial boundaries is spatially translation covariant. -/
theorem p4Q2PZ37AAR_originalTemporalCrossingAction_translation
    (a : Disp) (A B : Cfg) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
      (p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a A)
      (p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a B) =
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B := by
  rw [p4Q2PZ37AAR_originalCrossingAction_eq_sum H,
    p4Q2PZ37AAR_originalCrossingAction_eq_sum H]
  let T := p4Q2PZ37AAP_actualSpatialLinkTranslation H a
  rw [← Equiv.sum_comp T]
  apply Finset.sum_congr rfl
  intro e _he
  have hA :
      p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a A (T e) =
        A e :=
    p4Q2PZ37AAQ_configurationTranslation_apply_translatedLink H a A e
  have hB :
      p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a B (T e) =
        B e :=
    p4Q2PZ37AAQ_configurationTranslation_apply_translatedLink H a B e
  rw [hA, hB]

/-- True original symmetric one-slab Wilson action is invariant
when both of its physical boundary configurations are translated. -/
theorem p4Q2PZ37AAR_originalCompleteOneSlabAction_translation
    (a : Disp) (A B : Cfg) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
      (p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a A)
      (p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a B) =
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
  rw [p4Q2PZ37AAR_originalSpatialWilsonAction_translation H a A,
    p4Q2PZ37AAR_originalSpatialWilsonAction_translation H a B,
    p4Q2PZ37AAR_originalTemporalCrossingAction_translation H a A B]

/-- UNCONDITIONAL exact covariance of the original interacting
symmetric SU(2) Wilson one-slab Boltzmann kernel. This does NOT
yet assert Perron vacuum or conditional posterior covariance. -/
theorem p4Q2PZ37AAR_originalCompleteOneSlabKernel_translation
    (a : Disp) (beta : ℝ) (A B : Cfg) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta
      (p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a A)
      (p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H a B) =
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    p4Q2PZ37AAR_originalCompleteOneSlabAction_translation H a A B]

end OriginalOneSlabTranslation
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAR_originalSpatialShift_translation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAR_originalSpatialPlaquetteHolonomy_translation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAR_originalSpatialWilsonAction_translation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAR_originalPhysicalSpatialWilsonSource_translation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAR_originalTemporalCrossingAction_translation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAR_originalCompleteOneSlabAction_translation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAR_originalCompleteOneSlabKernel_translation
