import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGIProjectionMomentSandwichV5_PZ37ABB2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABC — split the SAME original centered physical Wilson GI source
# into exact genuine plaquette components and a signed residual

This is an unconditional decomposition of the actual original centered
Gauss-law Wilson GI two-interacting-posterior source, NOT a new probe,
a surrogate posterior, or a changed Wilson action.

AAI proves that the unchanged centered physical Wilson source,
embedded in the original spatial Haar L2 carrier, is one half the
finite sum of the actual individually Haar-centered plaquette sources.
AAK proves that its genuine two-posterior signed expectation gap equals
the JH original GI continuous linear functional on this centered source.

Therefore the exact GI gap Delta_(H,b,e,z) is a sum of original
plaquette-source GI contributions at the ORIGINAL link and boundary
pair. For any selected actual plaquette p, split that sum into its
original local contribution and all remaining genuine plaquettes.
The reverse triangle estimate exposes the EXACT signed-cancellation
obstruction: the local response must dominate the entire residual
on an original positive-mass pair-Haar event to yield a useful lower
bound. The residual is NOT assumed zero or small.

Individual local plaquette inputs have only four SU(2) link coordinates,
but the true interacting Wilson/Perron GI functional may have
nonlocal response; no unsupported conditional locality is asserted.
No volume-uniform lower bound or cylinder construction is claimed.
Original kernel, Perron vacuum, physical source, two interacting Wilson
posteriors, original Haar, and all previous no-go results unchanged.
Append-only, standard 3 axioms only, no sorry/admit/native_decide,
Dobrushin, common fine interval, endpoints E/F, H1-H4 or continuum gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABC_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABC_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABC_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABC_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABC_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- ORIGINAL physical source centering is exactly the total
Haar-centered genuine plaquette-source sum on its unchanged L2 carrier.
This is a strengthening of the AAI physical-source synthesis to a
direct input identity for JH's actual original GI linear functional. -/
theorem p4Q2PZ37ABC_originalHaarCenteredWilson_eq_centeredPlaquetteSum
    (H : ℕ) :
    ContinuousMap.toLp 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
      (p4Q2JI_actualSpatialWilsonContinuous H) -
      (inner ℝ (p4Q2JU_originalSpatialWilsonPhysicalSource H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)) •
        ContinuousMap.toLp 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
          (1 : C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ)) =
      ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
        p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H p := by
  classical
  rw [p4Q2PZ37AAI_originalSpatialWilsonHaar_eq_finsetSum H,
    p4Q2PZ37AAI_originalPhysicalWilsonMean_eq_plaquetteHaarSum H]
  simp only [p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource,
    Finset.sum_sub_distrib, Finset.sum_smul]

/-- The exact original one-plaquette contribution, after genuine
Haar centering, to the unmodified JH two-Wilson-posterior signed
Gauss-law GI response on the original actual spatial link. -/
noncomputable def p4Q2PZ37ABC_originalCenteredPlaquetteGIContribution
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ :=
  (1 / 2 : ℝ) *
    p4Q2JH_originalGIResponseCLM H b hb.le e z
      (p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H p)

/-- Unconditional exact ORIGINAL Wilson-centered physical GI
expectation-gap decomposition as the sum of all genuine centered
plaquette-source responses, at every H, b>0, link and pair-Haar
boundary configuration. No local response is assumed nonzero. -/
theorem p4Q2PZ37ABC_originalGIGap_eq_sum_truePlaquetteContributions
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z =
      ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
        p4Q2PZ37ABC_originalCenteredPlaquetteGIContribution H b hb e z p := by
  classical
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let Haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 Haar :=
    ContinuousMap.toLp 2 Haar ℝ
  let W := p4Q2JI_actualSpatialWilsonContinuous H
  let U : C(Cfg, ℝ) := 1
  let m : ℝ := inner ℝ
    (p4Q2JU_originalSpatialWilsonPhysicalSource H)
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
  let J := p4Q2JH_originalGIResponseCLM H b hb.le e z
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  let V : Plaq → Lp ℝ 2 Haar :=
    p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H
  have hSource : L W - m • L U = ∑ p : Plaq, V p := by
    exact p4Q2PZ37ABC_originalHaarCenteredWilson_eq_centeredPlaquetteSum H
  have hJ : J (L W) - m * J (L U) = ∑ p : Plaq, J (V p) := by
    calc
      J (L W) - m * J (L U) = J (L W - m • L U) := by
        simp
      _ = J (∑ p : Plaq, V p) := by rw [hSource]
      _ = ∑ p : Plaq, J (V p) := by rw [map_sum]
  rw [p4Q2PZ37AAK_originalCenteredGI_eq_halfMeanSubtractedWilson
    H b hb e z]
  change (1 / 2 : ℝ) * (J (L W) - m * J (L U)) =
    ∑ p : Plaq, (1 / 2 : ℝ) * J (V p)
  rw [hJ]
  rw [Finset.mul_sum]

/-- Extract a SINGLE actual Wilson plaquette from the original finite
sum without deleting or modifying any of the remaining genuine terms.
Those remaining terms constitute the potential nonlocal cancellation. -/
theorem p4Q2PZ37ABC_originalGIGap_eq_onePlaquette_add_fullResidual
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z =
      p4Q2PZ37ABC_originalCenteredPlaquetteGIContribution H b hb e z p +
        ∑ q ∈ (Finset.univ : Finset
            (PeriodicHypercubicEvenSpatialSlicePlaquette H)).erase p,
          p4Q2PZ37ABC_originalCenteredPlaquetteGIContribution H b hb e z q := by
  classical
  rw [p4Q2PZ37ABC_originalGIGap_eq_sum_truePlaquetteContributions]
  let f := p4Q2PZ37ABC_originalCenteredPlaquetteGIContribution H b hb e z
  change (∑ q : PeriodicHypercubicEvenSpatialSlicePlaquette H, f q) =
    f p + ∑ q ∈ (Finset.univ : Finset
        (PeriodicHypercubicEvenSpatialSlicePlaquette H)).erase p, f q
  have hErase :=
    (Finset.univ : Finset
      (PeriodicHypercubicEvenSpatialSlicePlaquette H)).sum_erase_add
        f (Finset.mem_univ p)
  simpa only [add_comm] using hErase.symm

/-- The exact ORIGINAL signed residual cannot be ignored:
a putative genuine plaquette-level GI signal is attenuated by the
absolute sum of all other actual plaquette-source responses. -/
theorem p4Q2PZ37ABC_originalGIGap_abs_ge_plaquette_minus_fullResidual
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    |p4Q2PZ37ABC_originalCenteredPlaquetteGIContribution H b hb e z p| -
      |∑ q ∈ (Finset.univ : Finset
        (PeriodicHypercubicEvenSpatialSlicePlaquette H)).erase p,
        p4Q2PZ37ABC_originalCenteredPlaquetteGIContribution H b hb e z q| ≤
    |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z| := by
  let a := p4Q2PZ37ABC_originalCenteredPlaquetteGIContribution H b hb e z p
  let t := ∑ q ∈ (Finset.univ : Finset
    (PeriodicHypercubicEvenSpatialSlicePlaquette H)).erase p,
    p4Q2PZ37ABC_originalCenteredPlaquetteGIContribution H b hb e z q
  have hIdentity :
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z =
      a + t :=
    p4Q2PZ37ABC_originalGIGap_eq_onePlaquette_add_fullResidual
      H b hb e z p
  have hReverse : |a| ≤ |a + t| + |t| := by
    calc
      |a| = |(a + t) + (-t)| := by ring
      _ ≤ |a + t| + |-t| := abs_add_le _ _
      _ = |a + t| + |t| := by rw [abs_neg]
  rw [hIdentity]
  change |a| - |t| ≤ |a + t|
  linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABC_originalHaarCenteredWilson_eq_centeredPlaquetteSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABC_originalGIGap_eq_sum_truePlaquetteContributions
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABC_originalGIGap_eq_onePlaquette_add_fullResidual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABC_originalGIGap_abs_ge_plaquette_minus_fullResidual
