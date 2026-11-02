import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSphereAmbientOrthogonalV5_PZ37ADX
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADY — orthogonal invariance of Mathlib's genuine S³ surface measure

ADX proves that the original SU(2) sphere action T_g is the literal
restriction of a genuine E4 ≃ₗᵢ[ℝ] E4, with E4 = EuclideanSpace ℝ (Fin 4).
This file independently studies the fixed Mathlib
  Measure.toSphere (volume : Measure E4),
not the already pushed-forward original SU(2) Haar measure.

Using the genuine Mathlib polar sector definition of toSphere, we
prove that every real-linear isometry of E4 preserves this surface
measure on the TRUE unit-three-sphere. The proof uses real-volume
preservation under the linear isometry and the exact radial sector
preimage, then extends from open sets by outer regularity.
Finally the same statement is obtained for original SU(2) action T_g
using ADX's exact equality of actions.

No substitute group, arbitrary "uniform" distribution, fake Haar,
physical receiver change, or continuum Yang–Mills mass-gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => Metric.sphere (0 : E4) 1
local notation "surf" => Measure.toSphere (volume : Measure E4)
local notation "act" => p4Q2PZ37ADU_originalLeftActionOnSphere
local notation "ambient" => p4Q2PZ37ADX_originalAmbientLinearIsometry

/-- A genuine real-linear orthogonal map restricts to the SAME
unit S³ in the fixed Mathlib Euclidean metric, with no change of
measurable space or surface measure. -/
noncomputable def p4Q2PZ37ADY_orthogonalSphereMap
    (L : E4 ≃ₗᵢ[ℝ] E4) (x : S3) : S3 :=
  ⟨L (x : E4), by
    have hx : ‖(x : E4)‖ = 1 := by
      simpa only [dist_zero_right] using x.property
    change dist (L (x : E4)) (0 : E4) = 1
    simpa only [dist_zero_right, LinearIsometryEquiv.norm_map] using hx⟩

theorem p4Q2PZ37ADY_orthogonalSphereMap_continuous
    (L : E4 ≃ₗᵢ[ℝ] E4) :
    Continuous (p4Q2PZ37ADY_orthogonalSphereMap L) := by
  exact Continuous.subtype_mk
    (L.continuous.comp continuous_subtype_val) _

theorem p4Q2PZ37ADY_orthogonalSphereMap_inv
    (L : E4 ≃ₗᵢ[ℝ] E4) (x : S3) :
    p4Q2PZ37ADY_orthogonalSphereMap L
      (p4Q2PZ37ADY_orthogonalSphereMap L.symm x) = x := by
  apply Subtype.ext
  change L (L.symm (x : E4)) = (x : E4)
  exact L.apply_symm_apply _

/-- The actual orthogonal self-map of S³ is a HOMEOMORPHISM,
not a merely measurable or abstract bijection. -/
noncomputable def p4Q2PZ37ADY_orthogonalSphereHomeomorph
    (L : E4 ≃ₗᵢ[ℝ] E4) : S3 ≃ₜ S3 where
  toFun := p4Q2PZ37ADY_orthogonalSphereMap L
  invFun := p4Q2PZ37ADY_orthogonalSphereMap L.symm
  left_inv := by
    intro x
    simpa only [LinearIsometryEquiv.symm_symm] using
      (p4Q2PZ37ADY_orthogonalSphereMap_inv L.symm x)
  right_inv := p4Q2PZ37ADY_orthogonalSphereMap_inv L
  continuous_toFun := p4Q2PZ37ADY_orthogonalSphereMap_continuous L
  continuous_invFun := p4Q2PZ37ADY_orthogonalSphereMap_continuous L.symm

/-- The exact radial sector in the fixed Mathlib polar construction
commutes with the inverse image of EVERY ambient linear isometry.
This identity, rather than an assumed "uniform sphere law", is the
geometric core of genuine toSphere invariance. -/
theorem p4Q2PZ37ADY_radialSector_preimage
    (L : E4 ≃ₗᵢ[ℝ] E4) (s : Set S3) :
    (Set.Ioo (0 : ℝ) 1) •
      (Subtype.val '' ((p4Q2PZ37ADY_orthogonalSphereMap L) ⁻¹' s)) =
      L ⁻¹' ((Set.Ioo (0 : ℝ) 1) • (Subtype.val '' s)) := by
  ext z
  constructor
  · rintro ⟨r, hr, _, ⟨x, hx, rfl⟩, rfl⟩
    change L (r • (x : E4)) ∈ _
    rw [map_smul]
    exact Set.smul_mem_smul hr
      (show L (x : E4) ∈ Subtype.val '' s from
        ⟨p4Q2PZ37ADY_orthogonalSphereMap L x, hx, rfl⟩)
  · intro hz
    change L z ∈ (Set.Ioo (0 : ℝ) 1) • (Subtype.val '' s) at hz
    rcases hz with ⟨r, hr, _, ⟨x, hx, rfl⟩, hz⟩
    have hInverse :
        p4Q2PZ37ADY_orthogonalSphereMap L
          (p4Q2PZ37ADY_orthogonalSphereMap L.symm x) = x :=
      p4Q2PZ37ADY_orthogonalSphereMap_inv L x
    have hMember :
        (p4Q2PZ37ADY_orthogonalSphereMap L.symm x : E4) ∈
          Subtype.val '' ((p4Q2PZ37ADY_orthogonalSphereMap L) ⁻¹' s) :=
      ⟨p4Q2PZ37ADY_orthogonalSphereMap L.symm x,
        by simpa only [Set.mem_preimage, hInverse] using hx, rfl⟩
    have hScaled :=
      Set.smul_mem_smul hr hMember
    have hEqual :
        r • (p4Q2PZ37ADY_orthogonalSphereMap L.symm x : E4) = z := by
      apply L.injective
      calc
        L (r • (p4Q2PZ37ADY_orthogonalSphereMap L.symm x : E4)) =
            r • L (L.symm (x : E4)) := by
              rw [map_smul]
              rfl
        _ = r • (x : E4) := by rw [L.apply_symm_apply]
        _ = L z := hz
    exact hEqual ▸ hScaled

/-- The fixed Mathlib toSphere measure itself is invariant on ALL
open subsets of the real unit-three-sphere, using only Euclidean
volume invariance under genuine linear isometries. -/
theorem p4Q2PZ37ADY_toSphere_preimage_open
    (L : E4 ≃ₗᵢ[ℝ] E4) (s : Set S3) (hs : IsOpen s) :
    surf ((p4Q2PZ37ADY_orthogonalSphereMap L) ⁻¹' s) = surf s := by
  have hCont := p4Q2PZ37ADY_orthogonalSphereMap_continuous L
  have hPre : IsOpen ((p4Q2PZ37ADY_orthogonalSphereMap L) ⁻¹' s) :=
    hs.preimage hCont
  have hOpenSector :
      IsOpen ((Set.Ioo (0 : ℝ) 1) • (Subtype.val '' s)) := by
    exact isOpen_Ioo.smul_sphere one_ne_zero (by simp) hs
  have hVolume : MeasurePreserving (L : E4 → E4)
      (volume : Measure E4) (volume : Measure E4) :=
    LinearIsometryEquiv.measurePreserving L
  rw [Measure.toSphere_apply' (μ := (volume : Measure E4)) hPre.measurableSet,
      Measure.toSphere_apply' (μ := (volume : Measure E4)) hs.measurableSet,
      p4Q2PZ37ADY_radialSector_preimage]
  rw [hVolume.measure_preimage hOpenSector.measurableSet.nullMeasurableSet]

/-- Unconditional invariance of the independent fixed Mathlib
toSphere surface measure under every ambient real-linear isometry.
NOT defined from original SU(2) Haar. -/
theorem p4Q2PZ37ADY_toSphere_map_orthogonal
    (L : E4 ≃ₗᵢ[ℝ] E4) :
    Measure.map (p4Q2PZ37ADY_orthogonalSphereMap L) surf = surf := by
  letI : Measure.OuterRegular surf := inferInstance
  have hOuter :
      Measure.OuterRegular
        (Measure.map (p4Q2PZ37ADY_orthogonalSphereHomeomorph L) surf) :=
    Measure.OuterRegular.map (p4Q2PZ37ADY_orthogonalSphereHomeomorph L) surf
  haveI : Measure.OuterRegular
      (Measure.map (p4Q2PZ37ADY_orthogonalSphereMap L) surf) := by
    convert hOuter using 1
  apply Measure.OuterRegular.ext_isOpen
  intro s hs
  rw [Measure.map_apply
    (p4Q2PZ37ADY_orthogonalSphereMap_continuous L).measurable
    hs.measurableSet]
  exact p4Q2PZ37ADY_toSphere_preimage_open L s hs

/-- The precise independent Mathlib sphere-surface measure is now
invariant under the SAME original SU(2) left action from ADU/ADV,
because ADX proved that action equals a genuine ambient isometry. -/
theorem p4Q2PZ37ADY_originalLeftAction_preserves_toSphere (g : G) :
    Measure.map (act g) surf = surf := by
  have hAction :
      act g = p4Q2PZ37ADY_orthogonalSphereMap (ambient g) := by
    funext x
    apply Subtype.ext
    exact (p4Q2PZ37ADX_originalAmbient_eq_originalSphereAction g x).symm
  rw [hAction]
  exact p4Q2PZ37ADY_toSphere_map_orthogonal (ambient g)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADY_orthogonalSphereMap_continuous
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADY_orthogonalSphereMap_inv
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADY_radialSector_preimage
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADY_toSphere_preimage_open
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADY_toSphere_map_orthogonal
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADY_originalLeftAction_preserves_toSphere
