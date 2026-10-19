import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLeftBoundaryExponentialFactorizationV5_KZ
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialFourLegInvariantContraction
import Mathlib.Tactic

/-!
# P4-Q2-LA — genuine SU(2) antipodal transfer of the negative exponential kernel

KZ has shown that the ORIGINAL physical constant-unit GI receiver
under changing actual left-link boundary u is a strictly positive
scalar times a right source convolved against
  exp(-(beta/4) * <Phi(u),Phi(g)>).
KV proves the ACTUAL original Wilson SU(2) positive-coupling one-link
Haar transform is injective. Here no new injectivity theorem is assumed:
we prove that the central SU(2) rotation by pi acts as exact real
feature negation, hence the KZ negative exponential is a strictly
positive scalar multiple of the KV Wilson kernel at coupling beta/2.

Consequently every nonzero genuine continuous signed source admits
a nonzero negative-exponential Haar receiver. The remaining genuinely
physical GI gap connection additionally needs the exact signed
posterior source continuity/nonzero verification and JQ's ratio;
it is not asserted by this step alone.

No independent-Haar conditional posterior, artificial rank axiom,
sorry/admit, H1-C3 or continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2LA_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LA_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LA_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LA_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LA_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section SU2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Phi" => specialUnitaryMatrixRealFeature 2
local notation "nu" => normalizedCompactHaar Gauge
local notation "Z" => specialUnitaryTwoRotation Real.pi

/-- The authentic SU(2) pi-rotation is exactly the scalar matrix
minus identity. This is a concrete two-by-two trigonometric identity. -/
theorem p4Q2LA_originalSU2PiRotation_matrix_eq_negOne :
    ((Z : Gauge) : Matrix (Fin 2) (Fin 2) ℂ) =
      -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix,
      Matrix.neg_apply, Real.cos_pi, Real.sin_pi]

/-- Multiplication by the REAL SU(2) central pi-rotation negates
the defining complex matrix of every group element. -/
theorem p4Q2LA_originalSU2PiRotation_mul_matrix_neg
    (u : Gauge) :
    (((Z * u : Gauge) : Matrix (Fin 2) (Fin 2) ℂ)) =
      -(u : Matrix (Fin 2) (Fin 2) ℂ) := by
  change (((Z : Gauge) : Matrix (Fin 2) (Fin 2) ℂ) *
      (u : Matrix (Fin 2) (Fin 2) ℂ)) = _
  rw [p4Q2LA_originalSU2PiRotation_matrix_eq_negOne]
  simp

/-- Exact antipodal action on the ORIGINAL real eight-coordinate
feature: Phi((-I)u) = -Phi(u). The realification is the
ALREADY CONSTRUCTED real-linear map, no synthetic feature. -/
theorem p4Q2LA_originalSU2PiRotation_realFeature_neg (u : Gauge) :
    Phi (Z * u) = -Phi u := by
  change complexMatrixRealFeature 2
      (((Z * u : Gauge) : Matrix (Fin 2) (Fin 2) ℂ)) =
    -(complexMatrixRealFeature 2 (u : Matrix (Fin 2) (Fin 2) ℂ))
  rw [p4Q2LA_originalSU2PiRotation_mul_matrix_neg u]
  simpa only [neg_one_smul] using
    (complexMatrixRealFeature_smul 2 (-1 : ℝ)
      (u : Matrix (Fin 2) (Fin 2) ℂ))

/-- The left-boundary negative feature exponential from KZ is
EXACTLY an original positive-coupling Wilson relative kernel section
after a physical central SU(2) rotation, at coupling b/2, times exp(b/2).
Thus no second injectivity engine or sign assumption is needed. -/
theorem p4Q2LA_originalNegativeFeatureExponential_eq_antipodalWilson
    (b : ℝ) (u g : Gauge) :
    Real.exp (-(b / 4) * inner ℝ (Phi u) (Phi g)) =
      Real.exp (b / 2) *
        specialUnitaryWilsonRelativeKernel 2 (b / 2) (Z * u) g := by
  rw [p4Q2KV_originalWilsonRelativeKernel_eq_realFeatureExponential,
    p4Q2KR_originalSU2FeatureExponentialContinuous_apply,
    p4Q2LA_originalSU2PiRotation_realFeature_neg, inner_neg_left]
  have hCancel : Real.exp (b / 2) * Real.exp (-(b / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [← mul_assoc, hCancel, one_mul]
  congr 1
  ring

/-- All nonzero continuous REAL signed SU(2) Haar sources are detected
by the exact negative-feature exponential required by the TRUE
physical Perron half-density factorization. Apply existing KV, and
use the genuine SU(2) central rotation only on the receiver variable. -/
theorem p4Q2LA_originalNegativeExponentialHaarTransform_exists_nonzero_receiver
    (b : ℝ) (hb : 0 < b) (ψ : C(Gauge, ℝ)) (hψ : ψ ≠ 0) :
    ∃ u : Gauge,
      (∫ g : Gauge,
        Real.exp (-(b / 4) * inner ℝ (Phi u) (Phi g)) * ψ g ∂nu) ≠ 0 := by
  obtain ⟨v, hv⟩ :=
    p4Q2KV_originalWilsonSingleLinkHaarTransform_exists_nonzero_receiver
      (b / 2) (by positivity) ψ hψ
  let u : Gauge := Z⁻¹ * v
  have hZu : Z * u = v := by
    dsimp [u]
    group
  refine ⟨u, ?_⟩
  have hPoint (g : Gauge) :
      Real.exp (-(b / 4) * inner ℝ (Phi u) (Phi g)) =
        Real.exp (b / 2) *
          specialUnitaryWilsonRelativeKernel 2 (b / 2) v g := by
    rw [← hZu]
    exact p4Q2LA_originalNegativeFeatureExponential_eq_antipodalWilson b u g
  have hIntegral :
      (∫ g : Gauge,
        Real.exp (-(b / 4) * inner ℝ (Phi u) (Phi g)) * ψ g ∂nu) =
      Real.exp (b / 2) *
        (∫ g : Gauge,
          specialUnitaryWilsonRelativeKernel 2 (b / 2) v g * ψ g ∂nu) := by
    calc
      _ = ∫ g : Gauge,
          Real.exp (b / 2) *
            (specialUnitaryWilsonRelativeKernel 2 (b / 2) v g * ψ g) ∂nu := by
        apply integral_congr_ae
        filter_upwards with g
        rw [hPoint g]
        ring
      _ = _ := integral_const_mul _ _
  rw [hIntegral]
  exact mul_ne_zero (Real.exp_pos _).ne' hv

/-- A convenient direct injectivity formulation for LA/LB: if ALL
negative-feature receivers vanish, the actual signed continuous SU(2)
source must be zero, as a theorem consequence of existing KV. -/
theorem p4Q2LA_originalNegativeExponentialHaarTransform_injective
    (b : ℝ) (hb : 0 < b) (ψ : C(Gauge, ℝ))
    (hZero : ∀ u : Gauge,
      (∫ g : Gauge,
        Real.exp (-(b / 4) * inner ℝ (Phi u) (Phi g)) * ψ g ∂nu) = 0) :
    ψ = 0 := by
  by_contra hψ
  obtain ⟨u, hu⟩ :=
    p4Q2LA_originalNegativeExponentialHaarTransform_exists_nonzero_receiver
      b hb ψ hψ
  exact hu (hZero u)

end SU2
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LA_originalSU2PiRotation_matrix_eq_negOne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LA_originalSU2PiRotation_mul_matrix_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LA_originalSU2PiRotation_realFeature_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LA_originalNegativeFeatureExponential_eq_antipodalWilson
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LA_originalNegativeExponentialHaarTransform_exists_nonzero_receiver
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LA_originalNegativeExponentialHaarTransform_injective
