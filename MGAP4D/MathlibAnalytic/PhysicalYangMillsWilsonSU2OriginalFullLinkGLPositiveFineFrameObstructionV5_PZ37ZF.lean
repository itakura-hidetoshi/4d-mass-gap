import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullLinkGLFineNearZeroDecayV5_PZ37ZE
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonSmallPositiveFineUnitNonEigenlineV5_OL
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZF — genuine positive-fine full-link GL coefficient-frame obstruction

The exact original SU(2) Wilson physical transfer T_t, its canonical
Gauss-law unit U, the original interacting TWO-posterior signed link gap
and the true FULL-LINK/FULL-BOUNDARY-Haar GL mass are unchanged.

PZ37ZE proved M_GL(U - T_t U) -> 0 as t -> 0 along the genuine
nonnegative fine coupling half-line, for each fixed finite H and
positive frozen coupling b. OL/IV proved that the actual physical source
U - T_t U is NONZERO at every sufficiently small positive t.
Together they imply arbitrarily small positive fine couplings whose
genuinely nonzero Wilson physical cancellation sources have arbitrarily
small genuine integrated posterior GL mass.

In particular a single fixed coefficient vector (1,-1) on the
ACTUAL physical modes (U, T_t U) has coefficient squared norm 2
independent of t; no strictly positive coefficient-l2 GL lower frame
constant works throughout ANY punctured fine window (0,delta).

This does NOT assert that mass / ||U-T_t U||^2 vanishes, nor disprove
a source-norm coercivity estimate, a positive-fine interval separated
from zero, scale/endpoint transport, H1-H4 or a continuum mass gap.
No two-context GI density, surrogate posterior, Dobrushin, new axiom,
sorry, admit or native_decide is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZF_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZF_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZF_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZF_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZF_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZF_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

private theorem p4Q2PZ37ZF_exists_positive_subtype_eventually
    (P : Set.Ici (0 : ℝ) → Prop)
    (hP : ∀ᶠ t in 𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)), P t)
    (delta : ℝ) (hDelta : 0 < delta) :
    ∃ t : Set.Ici (0 : ℝ),
      0 < (t : ℝ) ∧ (t : ℝ) < delta ∧ P t := by
  let t0 : Set.Ici (0 : ℝ) := ⟨0, le_refl (0 : ℝ)⟩
  obtain ⟨eta, hEta, hBall⟩ :=
    (Metric.eventually_nhds_iff).mp hP
  let tau : ℝ := min (eta / 2) (delta / 2)
  have hTauPos : 0 < tau := by
    dsimp [tau]
    exact lt_min (half_pos hEta) (half_pos hDelta)
  have hTauEta : tau < eta := by
    dsimp [tau]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hEta)
  have hTauDelta : tau < delta := by
    dsimp [tau]
    exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hDelta)
  let t : Set.Ici (0 : ℝ) := ⟨tau, le_of_lt hTauPos⟩
  have hDist : dist t t0 < eta := by
    change dist tau (0 : ℝ) < eta
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hTauPos] using hTauEta
  exact ⟨t, hTauPos, hTauDelta, hBall hDist⟩

/-- The TRUE original Wilson full-link posterior mass of the same
two-mode physical cancellation is arbitrarily small at arbitrarily
small STRICTLY POSITIVE fine t. This is not obtained by taking t=0. -/
theorem p4Q2PZ37ZF_exists_positiveFine_originalGLMass_small
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (delta epsilon : ℝ) (hDelta : 0 < delta) (hEps : 0 < epsilon) :
    ∃ t : Set.Ici (0 : ℝ),
      0 < (t : ℝ) ∧ (t : ℝ) < delta ∧
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b (le_of_lt hb)
        (p4Q2PZ37ZE_originalPhysicalCancellation H t)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) <
        epsilon := by
  have hLimit :=
    p4Q2PZ37ZE_originalGL_cancellation_tendsto_zero H b hb
  have hEventually :
      ∀ᶠ t : Set.Ici (0 : ℝ)
        in 𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)),
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H b (le_of_lt hb)
          (p4Q2PZ37ZE_originalPhysicalCancellation H t)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) <
          epsilon :=
    (tendsto_order.1 hLimit).2 epsilon hEps
  exact p4Q2PZ37ZF_exists_positive_subtype_eventually
    _ hEventually delta hDelta

/-- Original Wilson Haar rows are strictly distinct at small fine t
(OL). The ORIGINAL physical normalized transfer therefore does NOT fix
the constant Gauss-law unit in the interval. The cancellation source
U-T_tU is genuinely NONZERO at every such positive t. -/
theorem p4Q2PZ37ZF_originalPhysicalCancellation_ne_zero_smallPositive
    (H : ℕ) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t : Set.Ici (0 : ℝ),
        0 < (t : ℝ) → (t : ℝ) < delta →
          p4Q2PZ37ZE_originalPhysicalCancellation H t ≠ 0 := by
  obtain ⟨delta, hDelta, hRows⟩ :=
    p4Q2OL_originalWilsonHaarRows_notConstant_smallPositive H
  refine ⟨delta, hDelta, ?_⟩
  intro t ht hSmall hCancel
  let beta : ℕ → ℝ := fun k => if k = 0 then (0 : ℝ) else (t : ℝ)
  have hbeta : ∀ k, 0 ≤ beta k := by
    intro k
    dsimp [beta]
    split_ifs
    · exact le_refl 0
    · exact t.property
  have hNotEigen :
      ¬ ∃ c : ℝ,
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) =
          c • periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 := by
    have hWitness :=
      (p4Q2IV_actualFineUnit_notEigenline_iff_two_rawWilson_boundaries
        (halfExtent := fun _ : ℕ => H) (beta := beta) (hbeta := hbeta) 0).mpr
          (hRows (t : ℝ) ht hSmall)
    simpa [beta] using hWitness
  have hZero :
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 -
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) = 0 := by
    simpa [p4Q2PZ37ZE_originalPhysicalCancellation,
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine] using
        hCancel
  have hEq := (sub_eq_zero.mp hZero).symm
  apply hNotEigen
  exact ⟨1, by simpa only [one_smul] using hEq⟩

/-- Arbitrarily small, genuinely POSITIVE fine couplings admit
NONZERO genuine physical Gauss-law sources whose actual two-interacting
Wilson-posterior full-link GL mass is arbitrarily small.
Nonzero physical source does NOT mean unit-normalized physical source. -/
theorem p4Q2PZ37ZF_exists_nonzeroOriginalPhysical_smallPositiveFine_smallGLMass
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (delta epsilon : ℝ) (hDelta : 0 < delta) (hEps : 0 < epsilon) :
    ∃ t : Set.Ici (0 : ℝ),
      0 < (t : ℝ) ∧ (t : ℝ) < delta ∧
      p4Q2PZ37ZE_originalPhysicalCancellation H t ≠ 0 ∧
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b (le_of_lt hb)
        (p4Q2PZ37ZE_originalPhysicalCancellation H t)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) <
        epsilon := by
  obtain ⟨eta, hEta, hNonzero⟩ :=
    p4Q2PZ37ZF_originalPhysicalCancellation_ne_zero_smallPositive H
  have hmin : 0 < min delta eta := lt_min hDelta hEta
  obtain ⟨t, ht, hsmall, hMass⟩ :=
    p4Q2PZ37ZF_exists_positiveFine_originalGLMass_small
      H b hb (min delta eta) epsilon hmin hEps
  exact ⟨t, ht, lt_of_lt_of_le hsmall (min_le_left _ _),
    hNonzero t ht (lt_of_lt_of_le hsmall (min_le_right _ _)), hMass⟩

/-- An exact NO-GO for a fixed positive coefficient-l2 lower frame
over ANY punctured positive-fine interval. The TRUE physical coefficients
(1,-1) have squared norm 2 even though U-T_tU tends to zero in the
original Gauss-law Hilbert norm. This is not an assertion about
the ratio mass/||U-T_tU||^2 or a physical-source uniform lower bound. -/
theorem p4Q2PZ37ZF_no_uniformPositiveFine_twoModeCoefficientGLFrame
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ¬ ∃ gamma delta : ℝ, 0 < gamma ∧ 0 < delta ∧
      ∀ t : Set.Ici (0 : ℝ),
        0 < (t : ℝ) → (t : ℝ) < delta →
          gamma * 2 ≤
            p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
              H b (le_of_lt hb)
              (p4Q2PZ37ZE_originalPhysicalCancellation H t)
              (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  rintro ⟨gamma, delta, hGamma, hDelta, hLower⟩
  obtain ⟨t, ht, hSmall, hMassSmall⟩ :=
    p4Q2PZ37ZF_exists_positiveFine_originalGLMass_small
      H b hb delta (gamma * 2) hDelta (by positivity)
  exact (not_lt_of_ge (hLower t ht hSmall)) hMassSmall

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZF_exists_positiveFine_originalGLMass_small
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZF_originalPhysicalCancellation_ne_zero_smallPositive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZF_exists_nonzeroOriginalPhysical_smallPositiveFine_smallGLMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZF_no_uniformPositiveFine_twoModeCoefficientGLFrame
