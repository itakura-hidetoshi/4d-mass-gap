import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalEveryLinkPosteriorHaarL2SensitivityV5_FX
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergyInversion
import Mathlib.Tactic

/-!
# P4-Q2-FZ: a universal positive SU(2) temporal Wilson Haar variance constant

The exact original one-link Wilson posterior ratio between physical left
link values 1 and R(pi) is controlled by the ORIGINAL temporal contrast

 D(g) := E_W(g) - E_W(R(pi)^(-1)*g).

This SU(2) group function is independent of the volume H, target e,
right environment and physical ground-state vacuum. It is continuous
and takes the exact distinct values D(1)=-2, D(R(pi))=+2.

Let μ denote the ORIGINAL normalized compact SU(2) Haar probability.
Define the universal positive squared mean-zero Haar variation

 V_SU2 := integral [D(g) - integral D dμ]^2 dμ.

The support of this nonnegative continuous function contains a
nonempty open subset of SU(2), so V_SU2 > 0. The derivation uses the
genuine Haar topology and two explicit SU(2) Wilson energies, not
a finite-atom replacement of the physical group.

This is a volume-independent, beta-independent genuinely positive
Haar coefficient for the next analytic step. A later theorem must
combine the exact Wilson posterior log-ratio cancellation (FR)
with the uniform posterior density floor (FK) to produce a quantitative
actual posterior HAAR-L² row separation; and further input is needed
for source-dependent original FG RMS mass.

No Dobrushin coefficient, source-frame floor, beta-continuum gap,
or unproved summability is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 650000

local instance p4Q2FZ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2FZ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2FZ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2FZ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2FZ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2FZ_haarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

namespace GroundStatePosteriorJoint

/-- Exactly the original SU(2) Wilson crossing-energy difference between
the temporal left link values 1 and R(pi), evaluated at a candidate g. -/
noncomputable def p4Q2FZ_originalSU2TemporalWilsonContrast
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  specialUnitaryWilsonPlaquetteEnergy 2 g -
    specialUnitaryWilsonPlaquetteEnergy 2
      ((specialUnitaryTwoRotation Real.pi)⁻¹ * g)

/-- The SU(2) Wilson contrast is exactly -2 at the identity. -/
theorem p4Q2FZ_originalSU2TemporalWilsonContrast_one :
    p4Q2FZ_originalSU2TemporalWilsonContrast
      (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = -2 := by
  unfold p4Q2FZ_originalSU2TemporalWilsonContrast
  simp only [mul_one]
  rw [specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num)]
  rw [specialUnitaryWilsonPlaquetteEnergy_inv]
  rw [originalWilsonExplicitPiRotation_energy_eq_two]
  norm_num

/-- The SU(2) Wilson contrast is exactly +2 at the actual pi-rotation. -/
theorem p4Q2FZ_originalSU2TemporalWilsonContrast_rotation :
    p4Q2FZ_originalSU2TemporalWilsonContrast
      (specialUnitaryTwoRotation Real.pi) = 2 := by
  unfold p4Q2FZ_originalSU2TemporalWilsonContrast
  simp only [inv_mul_cancel]
  rw [specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num)]
  rw [originalWilsonExplicitPiRotation_energy_eq_two]
  norm_num

/-- The SU(2) crossing-energy contrast is a genuine continuous observable. -/
theorem p4Q2FZ_originalSU2TemporalWilsonContrast_continuous :
    Continuous p4Q2FZ_originalSU2TemporalWilsonContrast := by
  let R : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    specialUnitaryTwoRotation Real.pi
  have hShift : Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin 2) ℂ => R⁻¹ * g) :=
    continuous_const.mul continuous_id
  have hEnergy : Continuous
      (specialUnitaryWilsonPlaquetteEnergy 2) :=
    continuous_specialUnitaryWilsonPlaquetteEnergy 2
  exact hEnergy.sub (hEnergy.comp hShift)

/-- A truly universal (volume/link/background independent) real Haar
squared-variance of the temporal Wilson contrast. No finite SU(2)
Haar point masses or L² representative point-evaluation is assumed. -/
noncomputable def p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance : ℝ :=
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  let F := p4Q2FZ_originalSU2TemporalWilsonContrast
  ∫ g : Matrix.specialUnitaryGroup (Fin 2) ℂ,
    (F g - ∫ h, F h ∂μ) ^ 2 ∂μ

/-- The exact temporal Wilson contrast has STRICTLY POSITIVE centered
SU(2) Haar variance, independent of the physical lattice volume,
selected link, environment and Wilson coupling. -/
theorem p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance_pos :
    0 < p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance := by
  let μ : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  let F := p4Q2FZ_originalSU2TemporalWilsonContrast
  let m : ℝ := ∫ h, F h ∂μ
  let Q : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ :=
    fun g => (F g - m) ^ 2
  have hFContinuous : Continuous F :=
    p4Q2FZ_originalSU2TemporalWilsonContrast_continuous
  have hQContinuous : Continuous Q :=
    (hFContinuous.sub continuous_const).pow 2
  have hQIntegrable : Integrable Q μ :=
    hQContinuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let R : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    specialUnitaryTwoRotation Real.pi
  have hDifferent :
      F (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) ≠ F R := by
    change
      p4Q2FZ_originalSU2TemporalWilsonContrast 1 ≠
        p4Q2FZ_originalSU2TemporalWilsonContrast
          (specialUnitaryTwoRotation Real.pi)
    rw [p4Q2FZ_originalSU2TemporalWilsonContrast_one,
      p4Q2FZ_originalSU2TemporalWilsonContrast_rotation]
    norm_num
  obtain ⟨g, hg⟩ :
      ∃ g : Matrix.specialUnitaryGroup (Fin 2) ℂ, F g ≠ m := by
    by_cases hOne : F (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = m
    · refine ⟨R, ?_⟩
      intro hRot
      exact hDifferent (hOne.trans hRot.symm)
    · exact ⟨1, hOne⟩
  have hQNonzero : Q g ≠ 0 := by
    exact pow_ne_zero 2 (sub_ne_zero.mpr hg)
  have hSupportOpen : IsOpen (Function.support Q) := by
    change IsOpen (Q ⁻¹' ({0} : Set ℝ)ᶜ)
    exact isClosed_singleton.isOpen_compl.preimage hQContinuous
  have hSupportNonempty : (Function.support Q).Nonempty :=
    ⟨g, hQNonzero⟩
  have hSupportPos : 0 < μ (Function.support Q) :=
    hSupportOpen.measure_pos μ hSupportNonempty
  change 0 < ∫ g, Q g ∂μ
  rw [integral_pos_iff_support_of_nonneg]
  · exact hSupportPos
  · intro x
    exact sq_nonneg _
  · exact hQIntegrable

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FZ_originalSU2TemporalWilsonContrast_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FZ_originalSU2TemporalWilsonContrast_rotation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FZ_originalSU2TemporalWilsonContrast_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance_pos
