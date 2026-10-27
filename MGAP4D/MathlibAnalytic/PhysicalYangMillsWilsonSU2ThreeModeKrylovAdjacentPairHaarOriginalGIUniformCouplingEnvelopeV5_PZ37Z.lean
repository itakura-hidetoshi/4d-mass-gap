import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIAbsoluteActivityU0CriterionV5_PZ37Z
import Mathlib.Tactic

/-!
# P4-Q2-PZ37Z — coupling-schedule U0-type obstruction and mean/variance

The fixed-positive-frozen theorem of PZ37Z is upgraded to a varying
original Wilson frozen coupling schedule b_H>0. No fixed coupling
is smuggled into a changing-volume limit.

For each genuine H, maintain the SAME two-interacting-Wilson-posterior
compensated GI local minor d_{H,b_H,p}, original plaquette carrier
and original normalized energy Q_H/N_H.

For a uniform ORIGINAL Wilson amplitude envelope
  0 < K,   (4 E_{b_H}^2)^2 <= K  for every H,
the CONTEXT-SELECTABLE U0-type density criterion is equivalent to
uniform spatial occupancy above one absolute, H-independent threshold.

The envelope is an explicit additional condition; the result does not
prove it for arbitrary frozen-coupling schedules. Nor does it prove
that a compatible endpoint source or the U0 lower itself exists.

LZ's exact genuine mean-variance decomposition shows a finite-H
energy floor must be sustained by EITHER signed mean or spatial
heterogeneity. Finally, a purely scalar example proves positive
numbers for every finite H need not admit a positive uniform infimum.
The example is logical, NOT substituted for the genuine Wilson model.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZB_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZB_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZB_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZB_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZB_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

private abbrev p4Q2PZ37ZB_Cfg (H : ℕ) :=
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
private abbrev p4Q2PZ37ZB_Link (H : ℕ) :=
  PeriodicHypercubicEvenSpatialSliceLink H

/-- Context-selectable U0-type energy along a genuinely varying Wilson
frozen-coupling schedule. One ε>0 must work at every finite H;
Wilson links and boundary contexts are selected after H. -/
def p4Q2PZ37Z_scheduleContextSelectableOriginalGIUniformDensity
    (b : ℕ → ℝ) (hb : ∀ H, 0 ≤ b H) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ,
    ∃ e e' : p4Q2PZ37ZB_Link H,
    ∃ z z' : p4Q2PZ37ZB_Cfg H × p4Q2PZ37ZB_Cfg H,
      ε ≤
        p4Q2LY_originalCompensatedLocalGISquareEnergy
          H (b H) (hb H) e e' z z' /
          (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)

/-- Context-selectable positive-fraction activity above one genuine
absolute GI minor-square threshold for the variable frozen b_H. -/
def p4Q2PZ37Z_scheduleContextSelectableOriginalGIUniformAbsoluteActivity
    (b : ℕ → ℝ) (hb : ∀ H, 0 ≤ b H) : Prop :=
  ∃ τ ρ : ℝ, 0 < τ ∧ 0 < ρ ∧ ∀ H : ℕ,
    ∃ e e' : p4Q2PZ37ZB_Link H,
    ∃ z z' : p4Q2PZ37ZB_Cfg H × p4Q2PZ37ZB_Cfg H,
      ρ ≤
        ((p4Q2PZ37Z_originalGIAbsoluteActivePlaquettes
          H (b H) (hb H) τ e e' z z').card : ℝ) /
          (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)

/-- The exact coupling-SCHEDULE version of the original Wilson GI
absolute-threshold criterion. Unlike fixed b, a common ceiling K for
the *actual* original Wilson Harnack contrast is explicitly required.
This is a conditional equivalence, not proof that U0 holds. -/
theorem p4Q2PZ37Z_scheduleOriginalGI_uniformDensity_iff_absoluteActivity
    (b : ℕ → ℝ) (hb : ∀ H, 0 ≤ b H)
    (hbpos : ∀ H, 0 < b H)
    (K : ℝ) (hK : 0 < K)
    (hEnvelope : ∀ H : ℕ,
      (4 * (p4Q2LW_originalHarnackContrastScale (b H)) ^ 2) ^ 2 ≤ K) :
    p4Q2PZ37Z_scheduleContextSelectableOriginalGIUniformDensity b hb ↔
      p4Q2PZ37Z_scheduleContextSelectableOriginalGIUniformAbsoluteActivity b hb := by
  constructor
  · rintro ⟨ε, hε, hWit⟩
    have hDenK : 0 < 2 * K := mul_pos (by norm_num) hK
    refine ⟨ε / 2, ε / (2 * K),
      div_pos hε (by norm_num), div_pos hε hDenK, ?_⟩
    intro H
    obtain ⟨e, e', z, z', hEnergy⟩ := hWit H
    have hN : 0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) := by
      obtain ⟨_, _, _, _, hn, _⟩ :=
        p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor
          H (b H) (hb H) (hbpos H) e e' z.1 z.2
      exact hn
    let M_H : ℝ :=
      (4 * (p4Q2LW_originalHarnackContrastScale (b H)) ^ 2) ^ 2
    have hE : 0 < p4Q2LW_originalHarnackContrastScale (b H) :=
      p4Q2LW_originalHarnackContrastScale_pos (b H) (hbpos H)
    have hMH : 0 < M_H := by
      dsimp [M_H]
      positivity
    have hDenH : 0 < 2 * M_H := mul_pos (by norm_num) hMH
    have hMhK : M_H ≤ K := hEnvelope H
    have hScalar : ε / (2 * K) ≤ ε / (2 * M_H) := by
      apply (div_le_div_iff₀ hDenK hDenH).mpr
      nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hMhK)]
    have hPhysical :
        ε / (2 * M_H) ≤
          ((p4Q2PZ37Z_originalGIAbsoluteActivePlaquettes
            H (b H) (hb H) (ε / 2) e e' z z').card : ℝ) /
            (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) := by
      simpa only [M_H] using
        (p4Q2PZ37Z_originalGI_energyFloor_implies_absoluteActive_density
          H (b H) (hb H) (hbpos H) hN ε e e' z z' hEnergy)
    exact ⟨e, e', z, z', hScalar.trans hPhysical⟩
  · rintro ⟨τ, ρ, hτ, hρ, hWit⟩
    refine ⟨τ * ρ, mul_pos hτ hρ, ?_⟩
    intro H
    obtain ⟨e, e', z, z', hActivity⟩ := hWit H
    have hN : 0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) := by
      obtain ⟨_, _, _, _, hn, _⟩ :=
        p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor
          H (b H) (hb H) (hbpos H) e e' z.1 z.2
      exact hn
    exact ⟨e, e', z, z',
      p4Q2PZ37Z_originalGI_absoluteActive_implies_energyFloor
        H (b H) (hb H) hN τ ρ hτ.le e e' z z' hActivity⟩

/-- The genuine LZ cancellation-free normalized GI mean-square can
be maintained only by the squared signed Wilson global mean OR by
genuine spatial heterogeneity/variance, for the SAME physical contexts.
No independence or phase assumption on the plaquette responses. -/
theorem p4Q2PZ37Z_originalGI_energyFloor_meanSquare_or_heterogeneity
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hN : 0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ))
    (ε : ℝ)
    (e e' : p4Q2PZ37ZB_Link H)
    (z z' : p4Q2PZ37ZB_Cfg H × p4Q2PZ37ZB_Cfg H)
    (hEnergy : ε ≤
      p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb e e' z z' /
        (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)) :
    ε / 2 ≤
        (p4Q2LZ_originalCompensatedLocalGIMean H b hb e e' z z') ^ 2 ∨
      ε / 2 ≤
        p4Q2LZ_originalCompensatedLocalGIVariance H b hb e e' z z' := by
  have hSplit :=
    p4Q2LZ_originalCompensatedLocalSquareEnergy_eq_meanSq_add_variance
      H b hb hN e e' z z'
  rw [hSplit] at hEnergy
  by_cases hMean :
      ε / 2 ≤
        (p4Q2LZ_originalCompensatedLocalGIMean H b hb e e' z z') ^ 2
  · exact Or.inl hMean
  · exact Or.inr (by linarith)

/-- Pure SCALAR logical obstruction, not a replacement Wilson model:
strict positive numbers at each finite H do not logically imply any
positive H-independent lower bound. This isolates what finite-volume
rank-3 / GL positivity alone cannot provide. -/
theorem p4Q2PZ37Z_positiveEveryFiniteVolume_not_uniformInf :
    (∀ H : ℕ, 0 < (1 : ℝ) / ((H : ℝ) + 1)) ∧
      ¬ ∃ ε : ℝ, 0 < ε ∧
        ∀ H : ℕ, ε ≤ (1 : ℝ) / ((H : ℝ) + 1) := by
  constructor
  · intro H
    positivity
  · rintro ⟨ε, hε, hAll⟩
    obtain ⟨H, hH⟩ := exists_nat_gt (1 / ε)
    have hLarge : 1 < (H : ℝ) * ε :=
      (div_lt_iff₀ hε).mp hH
    have hDen : 0 < (H : ℝ) + 1 := by positivity
    have hSmall : ε * ((H : ℝ) + 1) ≤ 1 :=
      (le_div_iff₀ hDen).mp (hAll H)
    nlinarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Z_scheduleOriginalGI_uniformDensity_iff_absoluteActivity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Z_originalGI_energyFloor_meanSquare_or_heterogeneity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Z_positiveEveryFiniteVolume_not_uniformInf
