import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSU2FeatureCoordinateMomentSeparationV5_KL
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorExtremalDensitySignV5_KF
import Mathlib.Tactic

/-!
# P4-Q2-KM — the actual two INTERACTING Wilson posteriors admit a nonzero
# SU(2) coordinate-polynomial Haar moment

KL proves that moments against every actual SU(2) real/imaginary matrix
coordinate polynomial separate continuous signed sources, using exact
compact SU(2) Haar L² and the fixed mathlib Stone–Weierstrass theorem.
KF proves that the density difference of two *actual interacting*
Wilson conditional posteriors is strictly positive at the physical
identity insertion and strictly negative at the true pi rotation,
at EVERY finite H, physical link/right environment and frozen b>0.

We construct the original continuous posterior density difference,
prove it agrees pointwise with the exact GB/JN density contrast and
is nonzero, then apply KL to obtain a genuinely nonzero Haar pairing
against some true SU(2) coordinate polynomial. This is a theorem-
generated witness for the ACTUAL interacting conditional posterior
contrast, not a replacement by an independent-Haar posterior or a
synthetic GI receiver. The polynomial is a TEST of posterior contrast,
NOT YET the spatial Wilson transfer receiver in the unresolved
Gauss-law second context. No H1-C3 or continuum gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KM_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KM_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KM_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KM_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KM_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "nu" => normalizedCompactHaar Gauge
local notation "Alg" => p4Q2KK_originalSU2MatrixCoordinateAlgebra

/-- Continuous signed density difference of the TWO unchanged genuine
physical Wilson posteriors: left identity minus left pi-rotation. -/
noncomputable def p4Q2KM_originalInteractingWilsonPosteriorContrastContinuous
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) : C(Gauge, ℝ) :=
  p4Q2JN2_originalPosteriorIdentityContinuous H b hb right e -
  p4Q2JN2_originalPosteriorPiContinuous H b hb right e

/-- This continuous function is pointwise the EXACT original physical
GB Wilson posterior density contrast, including its Perron vacuum. -/
@[simp] theorem p4Q2KM_originalInteractingWilsonPosteriorContrastContinuous_apply
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) (g : Gauge) :
    p4Q2KM_originalInteractingWilsonPosteriorContrastContinuous H b hb right e g =
      p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb right e g := by
  rfl

/-- The actual two interacting Wilson posterior contrast is a NONZERO
continuous signed source at each fixed positive b: this follows from
the theorem-proved strict identity value, not an assumed rank. -/
theorem p4Q2KM_originalInteractingWilsonPosteriorContrastContinuous_ne_zero
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link) :
    p4Q2KM_originalInteractingWilsonPosteriorContrastContinuous H b hb.le right e ≠ 0 := by
  let ψ := p4Q2KM_originalInteractingWilsonPosteriorContrastContinuous H b hb.le right e
  have hpos : 0 < ψ (1 : Gauge) := by
    simpa [ψ] using
      (p4Q2KF_originalPosteriorDensityContrast_identity_pos H b hb right e)
  intro heq
  have hz := congrArg (fun (f : C(Gauge, ℝ)) => f (1 : Gauge)) heq
  exact (ne_of_gt hpos) (by simpa [ψ] using hz)

/-- There exists a nonzero genuine SU(2) reference-Haar moment of the
actual interacting physical two-posterior density difference against
a coordinate polynomial from the DEFINING representation. This
polynomial witness is theorem-constructed from KL rather than imposed
as a detector frame or substituted conditional probability law. -/
theorem p4Q2KM_originalInteractingWilsonPosterior_detected_by_coordinatePolynomial
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link) :
    ∃ p : Alg,
      (∫ g : Gauge, (p : C(Gauge, ℝ)) g *
        p4Q2GB_originalWilsonPosteriorLeftDensityContrast
          H b hb.le right e g ∂nu) ≠ 0 := by
  let ψ := p4Q2KM_originalInteractingWilsonPosteriorContrastContinuous
    H b hb.le right e
  have hψ : ψ ≠ 0 :=
    p4Q2KM_originalInteractingWilsonPosteriorContrastContinuous_ne_zero
      H b hb right e
  by_contra hNo
  have hAll (p : Alg) :
      (∫ g : Gauge, (p : C(Gauge, ℝ)) g * ψ g ∂nu) = 0 := by
    by_contra hMoment
    apply hNo
    refine ⟨p, ?_⟩
    simpa only [ψ,
      p4Q2KM_originalInteractingWilsonPosteriorContrastContinuous_apply]
      using hMoment
  have hzero : ψ = 0 :=
    p4Q2KL_originalSU2HaarCoordinatePolynomialMoments_separate ψ hAll
  exact hψ hzero

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KM_originalInteractingWilsonPosteriorContrastContinuous_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KM_originalInteractingWilsonPosteriorContrastContinuous_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KM_originalInteractingWilsonPosterior_detected_by_coordinatePolynomial
