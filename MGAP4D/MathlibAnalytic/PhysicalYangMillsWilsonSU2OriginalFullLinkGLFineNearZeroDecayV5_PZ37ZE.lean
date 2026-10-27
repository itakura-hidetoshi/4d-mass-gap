import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGLExplicitPhysicalVolumeEnvelopeV5_PZ37ZD
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalizedOneSlabBetaContinuity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroRankOne
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZE — actual full-link GL near-zero-fine cancellation decay

Use the UNMODIFIED original SU(2) Wilson normalized Gauss-law transfer
T_t, its exactly fixed Haar constant source U at fine coupling t=0,
and its verified operator-NORM continuity on the genuine nonnegative
Wilson coupling half-line.

For each fixed finite physical H, frozen b>0 and t>=0, define the
genuine physical cancellation source

    F_t = U - T_t U.

PZ37ZC's ORIGINAL TWO-INTERACTING-POSTERIOR all-link GL mass upper
bound then yields the exact quantitative operator-distance estimate

    0 <= M_GL(H,b; F_t)
       <= (2 * |Links(H)| / exp(-16 b)) * ||T_t - T_0||^2.

The upper bound is a true original Wilson bound on a nonzero-fine
Krylov difference, NOT the invalidated compensated two-context local
GI Q/N density. At t=0 the true cancellation F_0 vanishes, and as
t tends to zero through the nonnegative half-line, the upper bound
and the genuine GL mass both tend to ZERO.

The first result is quantitative for every fine t>=0; the second
does NOT posit any H-uniform modulus. The conclusion obstructs a
coefficient-l2 floor uniform down to fine zero, NOT a Hilbert-source
norm coercivity estimate on nonzero source directions. There is no
surrogate Haar posterior, no Dobrushin, no new axiom, sorry, admit,
native_decide or continuum mass-gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZE_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZE_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZE_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZE_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZE_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZE_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The exact original Gauss-law physical source arising from the
difference of zero-step and one-step TRUE normalized fine transfers.
The fine parameter lives on the genuine nonnegative Wilson half-line. -/
noncomputable def p4Q2PZ37ZE_originalPhysicalCancellation
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 -
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine
      H 2 specialUnitaryTwoWilsonRankPositive t
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)

/-- The unchanged Wilson normalized transfer fixes the true constant
Gauss-law unit at fine coupling exactly zero, so the physical
cancellation source vanishes (not merely its GI receiver). -/
theorem p4Q2PZ37ZE_originalPhysicalCancellation_zero (H : ℕ) :
    p4Q2PZ37ZE_originalPhysicalCancellation H
        (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)) = 0 := by
  unfold p4Q2PZ37ZE_originalPhysicalCancellation
  simp only [
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine_apply,
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_zero_constantUnit,
    sub_self]

/-- The REAL original Wilson full-link posterior GL mass of U - T_t U
is bounded by the squared TRUE operator distance from the rank-one
fine-zero normalized Wilson transfer, for ALL t>=0. -/
theorem p4Q2PZ37ZE_originalGL_cancellation_le_physicalTransferDistanceSq
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (t : Set.Ici (0 : ℝ)) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b (le_of_lt hb)
      (p4Q2PZ37ZE_originalPhysicalCancellation H t)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≤
      (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * 2) /
        Real.exp (-16 * b)) *
        ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine
            H 2 specialUnitaryTwoWilsonRankPositive t -
          periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine
            H 2 specialUnitaryTwoWilsonRankPositive
              (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ))‖ ^ 2 := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine
      H 2 specialUnitaryTwoWilsonRankPositive
  let t0 : Set.Ici (0 : ℝ) := ⟨0, le_refl (0 : ℝ)⟩
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let F := p4Q2PZ37ZE_originalPhysicalCancellation H t
  have h0 : T t0 U = U := by
    simp [T, t0, U]
  have hF : F = -((T t - T t0) U) := by
    change U - T t U = -((T t - T t0) U)
    rw [ContinuousLinearMap.sub_apply, h0]
    abel
  have hUNorm : ‖U‖ = (1 : ℝ) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  have hNorm : ‖F‖ ≤ ‖T t - T t0‖ := by
    rw [hF, norm_neg]
    calc
      ‖(T t - T t0) U‖ ≤ ‖T t - T t0‖ * ‖U‖ :=
        (T t - T t0).le_opNorm U
      _ = ‖T t - T t0‖ := by rw [hUNorm, mul_one]
  have hSq : ‖F‖ ^ 2 ≤ ‖T t - T t0‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  have hCoef : 0 ≤
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * 2) /
        Real.exp (-16 * b) := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hSq hCoef
  have hWilson :=
    p4Q2PZ37ZC_originalGL_fullLink_le_explicit_physicalSourceNorm
      H b hb F
  calc
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b (le_of_lt hb) F
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≤
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        (2 * ‖F‖ ^ 2)) / Real.exp (-16 * b) := hWilson
    _ =
        (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * 2) /
          Real.exp (-16 * b)) * ‖F‖ ^ 2 := by ring
    _ ≤
        (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * 2) /
          Real.exp (-16 * b)) * ‖T t - T t0‖ ^ 2 := hScaled

/-- TRUE full-link two-interacting-posterior Wilson GL mass of the
original physical cancellation source tends to ZERO as positive fine
approaches the genuine rank-one fine endpoint. The upper bound uses
the EXACT physical one-slab operator-norm continuity and no local
two-context GI assumption. This is at each FIXED H,b, not uniform H. -/
theorem p4Q2PZ37ZE_originalGL_cancellation_tendsto_zero
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto
      (fun t : Set.Ici (0 : ℝ) =>
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H b (le_of_lt hb)
          (p4Q2PZ37ZE_originalPhysicalCancellation H t)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
      (𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
      (𝓝 (0 : ℝ)) := by
  let t0 : Set.Ici (0 : ℝ) := ⟨0, le_refl (0 : ℝ)⟩
  let T :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine
      H 2 specialUnitaryTwoWilsonRankPositive
  let C : ℝ :=
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * 2) /
        Real.exp (-16 * b)
  let M : Set.Ici (0 : ℝ) → ℝ := fun t =>
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b (le_of_lt hb)
      (p4Q2PZ37ZE_originalPhysicalCancellation H t)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  have hT : Continuous T := by
    simpa [T] using
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine_continuous
        H 2 specialUnitaryTwoWilsonRankPositive)
  have hDiff : Continuous (fun t : Set.Ici (0 : ℝ) => T t - T t0) :=
    hT.sub continuous_const
  let Phys :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let Op := Phys →L[ℝ] Phys
  have hOpNorm : Continuous (fun S : Op => ‖S‖) := continuous_norm
  have hNorm : Continuous (fun t : Set.Ici (0 : ℝ) => ‖T t - T t0‖) :=
    hOpNorm.comp hDiff
  have hN : Continuous (fun t : Set.Ici (0 : ℝ) => ‖T t - T t0‖ ^ 2) :=
    hNorm.pow 2
  have hNLimit :
      Tendsto (fun t : Set.Ici (0 : ℝ) => ‖T t - T t0‖ ^ 2)
        (𝓝 t0) (𝓝 (0 : ℝ)) := by
    simpa using hN.continuousAt
  have hCLimit :
      Tendsto (fun t : Set.Ici (0 : ℝ) => C * ‖T t - T t0‖ ^ 2)
        (𝓝 t0) (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hNLimit : Tendsto
      (fun t : Set.Ici (0 : ℝ) => C * ‖T t - T t0‖ ^ 2)
      (𝓝 t0) (𝓝 (C * (0 : ℝ))))
  have hNonneg (t : Set.Ici (0 : ℝ)) : 0 ≤ M t := by
    unfold M p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    apply Finset.sum_nonneg
    intro e _he
    unfold p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
    apply integral_nonneg
    intro z
    exact div_nonneg (sq_nonneg _)
      (p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
        H b hb z.2 e).le
  have hUpper (t : Set.Ici (0 : ℝ)) :
      M t ≤ C * ‖T t - T t0‖ ^ 2 := by
    simpa only [M, C, T, t0] using
      (p4Q2PZ37ZE_originalGL_cancellation_le_physicalTransferDistanceSq
        H b hb t)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hCLimit
    (Filter.Eventually.of_forall hNonneg)
    (Filter.Eventually.of_forall hUpper)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZE_originalPhysicalCancellation_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZE_originalGL_cancellation_le_physicalTransferDistanceSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZE_originalGL_cancellation_tendsto_zero
