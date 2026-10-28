import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCenteredHaarBesselSynthesisV5_PZ37AAF
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalCenteredGLRayleighLimitV5_PZ37ZW
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAG — exact original Wilson centered Gauss-law physical / Haar bridge

The original Wilson spatial source is the sum of its TRUE spatial
plaquette energy observables (LO); the original physical Gauss-law
source has EXACTLY the same original spatial Haar-L² representative
(JU). The original physical Haar vacuum is the constant-one toLp
source, and the original inner-product centering coefficient equals
the SUM of the genuine plaquette Haar means.

Therefore the actual strong original Wilson tangent
    V_H = (W_H - <W_H,U_H> U_H)/2
agrees in the SAME Haar-L² carrier with one half of the unit-weight
original centered plaquette synthesis of AAF, rather than an invented
proxy. The physical Gauss-law Hilbert norm is therefore bounded by
    ||V_H||² <= 6 * (number of genuine spatial plaquettes).
The proof uses ZA's 24-Gram-row Haar covariance, no substitute Wilson
posterior or fake physical source.

IMPORTANT: this is a physical-source NORM UPPER bound, not a
lower bound on the GL mass, an all-volume positive Rayleigh floor,
an unproved common positive fine radius, endpoint E/F, H1-H4 or
a continuum four-dimensional Yang--Mills mass gap.
No new axiom, sorry, admit, native_decide.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AAG_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAG_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAG_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAG_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAG_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- The actual original GLOBAL Wilson action is the Finset sum
of its canonical genuine spatial plaquette energies, with no
coordinate or Wilson action replacement. -/
theorem p4Q2PZ37AAG_originalSpatialWilsonContinuous_eq_finsetSum
    (H : ℕ) :
    p4Q2JI_actualSpatialWilsonContinuous H =
      ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
        p4Q2LO_originalLocalPlaquetteContinuous H p := by
  classical
  rw [p4Q2LO_originalSpatialWilsonContinuous_eq_localSum H]
  simp only [periodicHypercubicEvenSpatialSlicePlaquetteList]
  simpa using (Finset.sum_map_toList
    (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSlicePlaquette H))
    (fun p => p4Q2LO_originalLocalPlaquetteContinuous H p))

/-- Exact original spatial Wilson Haar embedding is the sum of
original toLp plaquettes; continuous source embedding is real-linear. -/
theorem p4Q2PZ37AAG_originalSpatialWilsonHaar_eq_finsetSum
    (H : ℕ) :
    ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
        (p4Q2JI_actualSpatialWilsonContinuous H) =
      ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
        ContinuousMap.toLp 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
          (p4Q2LO_originalLocalPlaquetteContinuous H p) := by
  rw [p4Q2PZ37AAG_originalSpatialWilsonContinuous_eq_finsetSum H]
  simp only [map_sum]

/-- Every original local Wilson continuous observable's inner
product with the ORIGINAL constant Haar-L² vacuum equals its genuine
product-Haar mean. This is a physical integral identity, not a
surrogate probability measure. -/
theorem p4Q2PZ37AAG_originalLocalPlaquetteHaar_inner_unit_eq_integral
    (H : ℕ) (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    inner ℝ
      (ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
        (p4Q2LO_originalLocalPlaquetteContinuous H p))
      (ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
        (1 : C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ))) =
      ∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2 := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
      (p4Q2LO_originalLocalPlaquetteContinuous H p),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
      (1 : C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ))]
    with A hA hOne
  rw [hA, hOne]
  change (1 : ℝ) * p4Q2LO_originalLocalPlaquetteContinuous H p A =
    p4Q2LO_originalLocalPlaquetteContinuous H p A
  ring

/-- The ORIGINAL Gauss-law physical spatial-Wilson vacuum mean is
the sum of the original individual plaquette Haar means. -/
theorem p4Q2PZ37AAG_originalPhysicalWilsonMean_eq_plaquetteHaarSum
    (H : ℕ) :
    inner ℝ (p4Q2JU_originalSpatialWilsonPhysicalSource H)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) =
    ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
      ∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2 := by
  classical
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar :=
    ContinuousMap.toLp 2 haar ℝ
  let Phys := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let W : Phys := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let U : Phys := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  have hInnerSum :
      ∀ s : Finset Plaq,
        inner ℝ (∑ p ∈ s, L (p4Q2LO_originalLocalPlaquetteContinuous H p))
          (L (1 : C(Cfg, ℝ))) =
        ∑ p ∈ s, inner ℝ (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
          (L (1 : C(Cfg, ℝ))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
        simp only [Finset.sum_insert hp, real_inner_add_left, ih]
  have hMeanLocal (p : Plaq) :
      inner ℝ (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
        (L (1 : C(Cfg, ℝ))) =
      ∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A ∂haar :=
    p4Q2PZ37AAG_originalLocalPlaquetteHaar_inner_unit_eq_integral H p
  calc
    inner ℝ W U =
        inner ℝ (L (p4Q2JI_actualSpatialWilsonContinuous H))
          (L (1 : C(Cfg, ℝ))) := by
      change inner ℝ (W : Lp ℝ 2 haar) (U : Lp ℝ 2 haar) = _
      rw [p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp H,
        p4Q2JU_originalPhysicalUnit_coe_eq_toLp H]
    _ = inner ℝ (∑ p : Plaq,
          L (p4Q2LO_originalLocalPlaquetteContinuous H p))
          (L (1 : C(Cfg, ℝ))) := by
      rw [p4Q2PZ37AAG_originalSpatialWilsonHaar_eq_finsetSum H]
    _ = ∑ p : Plaq, inner ℝ
          (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
          (L (1 : C(Cfg, ℝ))) := by
      simpa only using hInnerSum Finset.univ
    _ = ∑ p : Plaq,
          ∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A ∂haar := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hMeanLocal p

/-- The actual original centered Gauss-law PHYSICAL tangent
represented in the original spatial Haar-L² carrier is IDENTICAL
to one half of the AAF centered genuine plaquette synthesis.
The original two interacting Wilson posteriors remain unchanged. -/
theorem p4Q2PZ37AAG_originalCenteredPhysical_coe_eq_halfHaarSynthesis
    (H : ℕ) :
    ((p4Q2PZ37ZW_originalCenteredPhysicalDirection H :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
    (1 / 2 : ℝ) •
      p4Q2PZ37AAF_originalCenteredHaarPlaquetteSynthesis H (fun _ => 1) := by
  classical
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar :=
    ContinuousMap.toLp 2 haar ℝ
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  let Phys := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let W : Phys := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let U : Phys := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let w : ℝ := inner ℝ W U
  have hMean : w = ∑ p : Plaq,
      ∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A ∂haar :=
    p4Q2PZ37AAG_originalPhysicalWilsonMean_eq_plaquetteHaarSum H
  have hUncentered :
      (W : Lp ℝ 2 haar) =
        ∑ p : Plaq, L (p4Q2LO_originalLocalPlaquetteContinuous H p) := by
    rw [p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp H]
    exact p4Q2PZ37AAG_originalSpatialWilsonHaar_eq_finsetSum H
  have hUnit : (U : Lp ℝ 2 haar) = L (1 : C(Cfg, ℝ)) :=
    p4Q2JU_originalPhysicalUnit_coe_eq_toLp H
  have hCenterSum :
      (∑ p : Plaq, p4Q2PZ37ZA_originalCenteredPlaquetteHaarSource H p) =
        (∑ p : Plaq, L (p4Q2LO_originalLocalPlaquetteContinuous H p)) -
          (∑ p : Plaq,
            ∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A ∂haar) •
              L (1 : C(Cfg, ℝ)) := by
    simp only [p4Q2PZ37ZA_originalCenteredPlaquetteHaarSource,
      Finset.sum_sub_distrib, Finset.sum_smul]
  change (((1 / 2 : ℝ) • (W - w • U) : Phys) : Lp ℝ 2 haar) =
    (1 / 2 : ℝ) •
      (∑ p : Plaq, p4Q2PZ37ZA_originalCenteredPlaquetteHaarSource H p)
  rw [Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_smul]
  rw [hCenterSum, ← hMean, ← hUncentered, ← hUnit]

/-- The PHYSICAL Gauss-law normalized centered Wilson tangent,
not a substitute source, has a true Haar-L² squared norm bounded
by 6 times the ACTUAL original spatial plaquette count. -/
theorem p4Q2PZ37AAG_originalCenteredPhysicalNorm_sq_le_six_plaquetteCount
    (H : ℕ) :
    ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤
      6 * (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) := by
  let V := p4Q2PZ37ZW_originalCenteredPhysicalDirection H
  let S := p4Q2PZ37AAF_originalCenteredHaarPlaquetteSynthesis H (fun _ => 1)
  have hEq : ‖V‖ = ‖(1 / 2 : ℝ) • S‖ := by
    change ‖(V : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))‖ =
      ‖(1 / 2 : ℝ) • S‖
    exact congrArg norm
      (p4Q2PZ37AAG_originalCenteredPhysical_coe_eq_halfHaarSynthesis H)
  have hSq : ‖V‖^2 = (1 / 4 : ℝ) * ‖S‖^2 := by
    rw [hEq, norm_smul, Real.norm_eq_abs]
    norm_num [mul_pow]
  have hBessel :
      ‖S‖^2 ≤ 24 *
        (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) :=
    p4Q2PZ37AAF_originalCenteredHaarPlaquetteUnitSum_sq_le_card H
  dsimp [V] at hSq ⊢
  linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAG_originalSpatialWilsonContinuous_eq_finsetSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAG_originalSpatialWilsonHaar_eq_finsetSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAG_originalLocalPlaquetteHaar_inner_unit_eq_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAG_originalPhysicalWilsonMean_eq_plaquetteHaarSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAG_originalCenteredPhysical_coe_eq_halfHaarSynthesis
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAG_originalCenteredPhysicalNorm_sq_le_six_plaquetteCount
