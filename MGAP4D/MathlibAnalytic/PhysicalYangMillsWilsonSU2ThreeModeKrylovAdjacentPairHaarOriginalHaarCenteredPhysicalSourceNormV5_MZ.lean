import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPlaquetteHaarVarianceUniformV5_MY
import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Tactic

/-!
# P4-Q2-MZ — uniform ORIGINAL Gauss-law physical-source Hilbert norm

MY proves a universal strictly positive SU(2) Haar Wilson plaquette
variance on every actual spatial H,p. MX identifies the ACTUAL
Gauss-law physical two-source Hilbert map with continuous representatives
in the ORIGINAL spatial reference Haar-L2.

MZ transfers MY's scalar variance exactly into the squared physical
Hilbert norm of the genuine original Wilson source centered at the
universal spatial-Haar mean:
  C^Haar_(H,p) = W_(H,p) U - m_SU2 U,
  ||C^Haar_(H,p)||^2 = V_SU2 > 0
for every H,p, without an assumed source-rank condition.

At frozen beta=0 the original two-interacting-posterior signed GI
Riesz detector is identically zero on the entire physical L2 space,
hence in particular on C^Haar_(H,p). This is a QUANTITATIVE real
source-versus-receiver obstruction.

Do not confuse Haar-centered C^Haar with MS's K_b-centered physical
source, nor original Haar variance with Var_(K_b). No claim of positive
beta signed receiver nonconstancy, nonzero GI covariance, uniform
Wilson-kernel conditional variance, H1-C3 or continuum mass gap.
No surrogate source, detector, posterior, Dobrushin, sorry or axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MZ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MZ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MZ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MZ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MZ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2


namespace GroundStatePosteriorJoint
section PhysicalSource
variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "w" => p4Q2LO_originalLocalPlaquetteContinuous H
local notation "m" => p4Q2MY_singleSU2HaarWilsonMean
local notation "V" => p4Q2MY_singleSU2HaarWilsonVariance
local notation "L" => ContinuousMap.toLp 2 haar ℝ

/-- The actual Gauss-law physical plaquette state with its ORIGINAL
spatial Haar mean subtracted, without changing its Wilson source map. -/
noncomputable def p4Q2MZ_originalHaarCenteredPhysicalPlaquetteSource
    (p : Plaq) : Phys :=
  p4Q2LO_originalPhysicalLocalTwoSource H p (-m) 1

local notation "Source" => p4Q2MZ_originalHaarCenteredPhysicalPlaquetteSource H

/-- Exact genuine physical Hilbert representative of the Haar-centered
original Wilson plaquette state. The real scalar function is evaluated
on the original full spatial SU(2) configurations. -/
theorem p4Q2MZ_originalHaarCenteredPhysicalSource_coe_eq_toLp
    (p : Plaq) :
    ((Source p : Phys) : Lp ℝ 2 haar) =
      L ((-m) • (1 : C(Cfg,ℝ)) + (1 : ℝ) • w p) := by
  exact p4Q2MX_originalPhysicalTwoSource_coe_eq_toLp H p (-m) 1

/-- Exact L2 norm-square integral of the genuine Gauss-law Wilson
physical source, via the pinned mathlib real-L2 inner product identity
and the original continuous Haar-L2 representative. -/
theorem p4Q2MZ_originalHaarCenteredPhysicalSource_norm_sq_eq_integral
    (p : Plaq) :
    ‖Source p‖ ^ 2 =
      ∫ A : Cfg, (w p A - m)^2 ∂haar := by
  let f : C(Cfg,ℝ) :=
    (-m) • (1 : C(Cfg,ℝ)) + (1 : ℝ) • w p
  have hrepr :
      ((Source p : Phys) : Lp ℝ 2 haar) = L f := by
    simpa only [f] using
      p4Q2MZ_originalHaarCenteredPhysicalSource_coe_eq_toLp H p
  calc
    ‖Source p‖ ^ 2 =
        ‖((Source p : Phys) : Lp ℝ 2 haar)‖ ^ 2 := rfl
    _ = ‖L f‖ ^ 2 := by rw [hrepr]
    _ = ∫ A : Cfg, ‖(L f) A‖ ^ 2 ∂haar :=
      realL2_norm_sq_eq_integral_norm_sq (L f)
    _ = ∫ A : Cfg, (w p A - m)^2 ∂haar := by
      apply integral_congr_ae
      filter_upwards
        [ContinuousMap.coeFn_toLp (𝕜 := ℝ)
          (p := (2 : ENNReal)) (μ := haar) f] with A hA
      rw [hA]
      simp only [f, ContinuousMap.add_apply, ContinuousMap.smul_apply,
        ContinuousMap.one_apply, smul_eq_mul, mul_one, one_mul]
      rw [Real.norm_eq_abs, sq_abs]
      ring

/-- EVERY original physical Haar-centered SU(2) Wilson source has the
EXACT SAME positive squared Hilbert norm independent of H,p.
Unlike a K_b-weighted variance this is a reference-Haar norm. -/
theorem p4Q2MZ_originalHaarCenteredPhysicalSource_norm_sq_eq_universal
    (p : Plaq) :
    ‖Source p‖ ^ 2 = V := by
  rw [p4Q2MZ_originalHaarCenteredPhysicalSource_norm_sq_eq_integral H p]
  exact p4Q2MY_originalSpatialWilsonEnergy_HaarVariance_eq_single H p

/-- Volume- and plaquette-independent strictly positive norm of the
ORIGINAL gauge-invariant SU(2) physical Wilson source. -/
theorem p4Q2MZ_originalHaarCenteredPhysicalSource_norm_pos_uniform
    (p : Plaq) :
    0 < ‖Source p‖ := by
  have hs :
      0 < ‖Source p‖ ^ 2 := by
    rw [p4Q2MZ_originalHaarCenteredPhysicalSource_norm_sq_eq_universal H p]
    exact p4Q2MY_singleSU2HaarWilsonVariance_pos
  nlinarith [norm_nonneg (Source p)]

end PhysicalSource

/-- Quantitative genuine beta-zero receiver obstruction:
the actual gauge-invariant Haar-centered physical Wilson source has
the fixed positive H-independent norm, but the ORIGINAL signed
two-interacting-Wilson-posterior Riesz receiver vanishes on it.
This does NOT hold as a proven claim at beta>0. -/
theorem p4Q2MZ_originalHaarPhysicalSource_betaZero_signedReceiver_noGo
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (‖p4Q2MZ_originalHaarCenteredPhysicalPlaquetteSource H p‖ ^ 2 =
       p4Q2MY_singleSU2HaarWilsonVariance ∧
     0 < p4Q2MY_singleSU2HaarWilsonVariance) ∧
    p4Q2JH_originalGIResponseCLM H 0 (le_refl (0 : ℝ)) e z
      ((p4Q2MZ_originalHaarCenteredPhysicalPlaquetteSource H p :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) = 0 := by
  constructor
  · exact ⟨p4Q2MZ_originalHaarCenteredPhysicalSource_norm_sq_eq_universal H p,
      p4Q2MY_singleSU2HaarWilsonVariance_pos⟩
  · rw [p4Q2JL_originalGIResponseCLM_zero H e z]
    simp

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MZ_originalHaarCenteredPhysicalSource_coe_eq_toLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MZ_originalHaarCenteredPhysicalSource_norm_sq_eq_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MZ_originalHaarCenteredPhysicalSource_norm_sq_eq_universal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MZ_originalHaarCenteredPhysicalSource_norm_pos_uniform
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MZ_originalHaarPhysicalSource_betaZero_signedReceiver_noGo
