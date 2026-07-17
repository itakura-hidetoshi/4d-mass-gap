import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectorySpecialUnitaryWilsonMultiStapleBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

local instance specialUnitaryTwoIsTopologicalGroup :
    IsTopologicalGroup (SpecialUnitaryMatrixGroup 2) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance specialUnitaryTwoCompactSpace :
    CompactSpace (SpecialUnitaryMatrixGroup 2) :=
  specialUnitaryGroupCompactSpace 2

/-- The central negative identity in `SU(2)`.  The determinant restriction is
specific to even rank; this theorem unit deliberately specializes to rank two. -/
def specialUnitaryTwoNegativeIdentity : SpecialUnitaryMatrixGroup 2 := by
  refine ⟨-(1 : Matrix (Fin 2) (Fin 2) ℂ), ?_⟩
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    simp
  · simp [Matrix.det_fin_two]

@[simp]
theorem specialUnitaryTwoNegativeIdentity_coe :
    ((specialUnitaryTwoNegativeIdentity : SpecialUnitaryMatrixGroup 2) :
      Matrix (Fin 2) (Fin 2) ℂ) =
      -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rfl

/-- Right multiplication by the central negative identity negates the ambient
matrix. -/
theorem specialUnitaryTwo_mul_negativeIdentity_coe
    (g : SpecialUnitaryMatrixGroup 2) :
    (((g * specialUnitaryTwoNegativeIdentity : SpecialUnitaryMatrixGroup 2) :
        Matrix (Fin 2) (Fin 2) ℂ)) =
      -((g : SpecialUnitaryMatrixGroup 2) : Matrix (Fin 2) (Fin 2) ℂ) := by
  change
    ((g : SpecialUnitaryMatrixGroup 2) : Matrix (Fin 2) (Fin 2) ℂ) *
        (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      -((g : SpecialUnitaryMatrixGroup 2) : Matrix (Fin 2) (Fin 2) ℂ)
  simp

/-- Real trace changes sign after multiplication by the rank-two central
negative identity. -/
theorem specialUnitaryTwo_trace_mul_negativeIdentity_re
    (g : SpecialUnitaryMatrixGroup 2) :
    (Matrix.trace
      (((g * specialUnitaryTwoNegativeIdentity : SpecialUnitaryMatrixGroup 2) :
        Matrix (Fin 2) (Fin 2) ℂ))).re =
      -(Matrix.trace
        (((g : SpecialUnitaryMatrixGroup 2) :
          Matrix (Fin 2) (Fin 2) ℂ))).re := by
  rw [specialUnitaryTwo_mul_negativeIdentity_coe]
  simp

/-- The `SU(2)` Wilson energy is complemented by the central negative identity. -/
theorem specialUnitaryWilsonPlaquetteEnergy_two_mul_negativeIdentity
    (g : SpecialUnitaryMatrixGroup 2) :
    specialUnitaryWilsonPlaquetteEnergy 2
        (g * specialUnitaryTwoNegativeIdentity) =
      2 - specialUnitaryWilsonPlaquetteEnergy 2 g := by
  unfold specialUnitaryWilsonPlaquetteEnergy
  rw [specialUnitaryTwo_trace_mul_negativeIdentity_re]
  ring

@[simp]
theorem specialUnitaryWilsonPlaquetteEnergy_two_one :
    specialUnitaryWilsonPlaquetteEnergy 2
      (1 : SpecialUnitaryMatrixGroup 2) = 0 := by
  norm_num [specialUnitaryWilsonPlaquetteEnergy, Matrix.trace, Fin.sum_univ_two]

@[simp]
theorem specialUnitaryWilsonPlaquetteEnergy_two_negativeIdentity :
    specialUnitaryWilsonPlaquetteEnergy 2
      specialUnitaryTwoNegativeIdentity = 2 := by
  simpa using
    (specialUnitaryWilsonPlaquetteEnergy_two_mul_negativeIdentity
      (1 : SpecialUnitaryMatrixGroup 2))

/-- The rank-two Wilson energy as an actual bounded continuous function. -/
def specialUnitaryTwoWilsonEnergyBCF :
    BoundedContinuousFunction (SpecialUnitaryMatrixGroup 2) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨specialUnitaryWilsonPlaquetteEnergy 2,
      continuous_specialUnitaryWilsonPlaquetteEnergy 2⟩

@[simp]
theorem specialUnitaryTwoWilsonEnergyBCF_apply
    (g : SpecialUnitaryMatrixGroup 2) :
    specialUnitaryTwoWilsonEnergyBCF g =
      specialUnitaryWilsonPlaquetteEnergy 2 g := by
  rfl

/-- Two coincident identity staples. -/
def specialUnitaryTwoSameStapleFamily :
    Fin 2 → SpecialUnitaryMatrixGroup 2 :=
  fun _ => 1

/-- One identity staple and one central negative-identity staple. -/
def specialUnitaryTwoOppositeStapleFamily :
    Fin 2 → SpecialUnitaryMatrixGroup 2 :=
  fun i => if i = 0 then 1 else specialUnitaryTwoNegativeIdentity

/-- The coincident two-staple section is twice the Wilson energy. -/
theorem specialUnitaryTwo_sameStaple_section_apply
    (g : SpecialUnitaryMatrixGroup 2) :
    multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
        specialUnitaryTwoSameStapleFamily g =
      2 * specialUnitaryWilsonPlaquetteEnergy 2 g := by
  rw [multiRightTranslateSumBCF_apply]
  simp [specialUnitaryTwoSameStapleFamily, Fin.sum_univ_two]
  ring

/-- The opposite-center two-staple section is the constant function two. -/
theorem specialUnitaryTwo_oppositeStaple_section_apply
    (g : SpecialUnitaryMatrixGroup 2) :
    multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
        specialUnitaryTwoOppositeStapleFamily g = 2 := by
  rw [multiRightTranslateSumBCF_apply]
  simp [specialUnitaryTwoOppositeStapleFamily, Fin.sum_univ_two,
    specialUnitaryWilsonPlaquetteEnergy_two_mul_negativeIdentity]

/-- The coincident section is nonnegative. -/
theorem specialUnitaryTwo_sameStaple_section_nonneg
    (g : SpecialUnitaryMatrixGroup 2) :
    0 ≤ multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
      specialUnitaryTwoSameStapleFamily g := by
  rw [specialUnitaryTwo_sameStaple_section_apply]
  nlinarith [specialUnitaryWilsonPlaquetteEnergy_nonneg (N := 2) (by norm_num) g]

/-- The coincident section is bounded above by four. -/
theorem specialUnitaryTwo_sameStaple_section_le_four
    (g : SpecialUnitaryMatrixGroup 2) :
    multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
      specialUnitaryTwoSameStapleFamily g ≤ 4 := by
  rw [specialUnitaryTwo_sameStaple_section_apply]
  nlinarith [specialUnitaryWilsonPlaquetteEnergy_le_two (N := 2) (by norm_num) g]

@[simp]
theorem specialUnitaryTwo_sameStaple_section_one :
    multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
      specialUnitaryTwoSameStapleFamily
      (1 : SpecialUnitaryMatrixGroup 2) = 0 := by
  rw [specialUnitaryTwo_sameStaple_section_apply]
  simp

@[simp]
theorem specialUnitaryTwo_sameStaple_section_negativeIdentity :
    multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
      specialUnitaryTwoSameStapleFamily specialUnitaryTwoNegativeIdentity = 4 := by
  rw [specialUnitaryTwo_sameStaple_section_apply]
  simp

/-- The coincident two-staple section has exact oscillation four. -/
theorem specialUnitaryTwo_sameStaple_oscillation_eq_four :
    multiRightTranslateSumOscillationBCF specialUnitaryTwoWilsonEnergyBCF
      specialUnitaryTwoSameStapleFamily = 4 := by
  let F := multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
    specialUnitaryTwoSameStapleFamily
  have hGreatest : IsGreatest (Set.range F) 4 := by
    constructor
    · exact ⟨specialUnitaryTwoNegativeIdentity,
        specialUnitaryTwo_sameStaple_section_negativeIdentity⟩
    · intro y hy
      rcases hy with ⟨g, rfl⟩
      exact specialUnitaryTwo_sameStaple_section_le_four g
  have hLeast : IsLeast (Set.range F) 0 := by
    constructor
    · exact ⟨(1 : SpecialUnitaryMatrixGroup 2),
        specialUnitaryTwo_sameStaple_section_one⟩
    · intro y hy
      rcases hy with ⟨g, rfl⟩
      exact specialUnitaryTwo_sameStaple_section_nonneg g
  unfold multiRightTranslateSumOscillationBCF
  change sSup (Set.range F) - sInf (Set.range F) = 4
  rw [hGreatest.csSup_eq, hLeast.csInf_eq]
  norm_num

/-- The opposite-center two-staple section has zero oscillation. -/
theorem specialUnitaryTwo_oppositeStaple_oscillation_eq_zero :
    multiRightTranslateSumOscillationBCF specialUnitaryTwoWilsonEnergyBCF
      specialUnitaryTwoOppositeStapleFamily = 0 := by
  let F := multiRightTranslateSumBCF specialUnitaryTwoWilsonEnergyBCF
    specialUnitaryTwoOppositeStapleFamily
  have hValue : ∀ g : SpecialUnitaryMatrixGroup 2, F g = 2 := by
    intro g
    exact specialUnitaryTwo_oppositeStaple_section_apply g
  have hGreatest : IsGreatest (Set.range F) 2 := by
    constructor
    · exact ⟨(1 : SpecialUnitaryMatrixGroup 2), hValue 1⟩
    · intro y hy
      rcases hy with ⟨g, rfl⟩
      rw [hValue g]
  have hLeast : IsLeast (Set.range F) 2 := by
    constructor
    · exact ⟨(1 : SpecialUnitaryMatrixGroup 2), hValue 1⟩
    · intro y hy
      rcases hy with ⟨g, rfl⟩
      rw [hValue g]
  unfold multiRightTranslateSumOscillationBCF
  change sSup (Set.range F) - sInf (Set.range F) = 0
  rw [hGreatest.csSup_eq, hLeast.csInf_eq]
  norm_num

/-- Exact algebraic separation of the two relative-staple geometries. -/
theorem specialUnitaryTwo_twoStaple_oscillations_ne :
    multiRightTranslateSumOscillationBCF specialUnitaryTwoWilsonEnergyBCF
        specialUnitaryTwoSameStapleFamily ≠
      multiRightTranslateSumOscillationBCF specialUnitaryTwoWilsonEnergyBCF
        specialUnitaryTwoOppositeStapleFamily := by
  rw [specialUnitaryTwo_sameStaple_oscillation_eq_four,
    specialUnitaryTwo_oppositeStaple_oscillation_eq_zero]
  norm_num

/-- Once two endpoint staple families have unequal section oscillations, the
existing hybrid-trajectory wrapper yields the coordinate-update witness. -/
theorem continuous_compact_oriented_multiStapleCylinderObservableBCF_coordinateUpdateWitness_of_endpoint_oscillation_ne
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {ι : Type*}
    [Fintype ι]
    (target : C.base.geometry.Edge)
    (f : BoundedContinuousFunction C.base.Gauge ℝ)
    (staple : ι → ContinuousMap C.base.Configuration C.base.Gauge)
    (hStaple : C.targetIndependentStapleFamilyBCF target staple)
    (z : C.base.Configuration × C.base.Configuration)
    (sInitial sFinal : ι → C.base.Gauge)
    (hInitial :
      (fun i => staple i
        (C.independentPairHybridConfiguration z.1 z.2 0)) = sInitial)
    (hFinal :
      (fun i => staple i
        (C.independentPairHybridConfiguration z.1 z.2
          (Fintype.card C.base.geometry.Edge))) = sFinal)
    (hNe :
      multiRightTranslateSumOscillationBCF f sInitial ≠
        multiRightTranslateSumOscillationBCF f sFinal) :
    C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
      target (C.multiStapleCylinderObservableBCF target f staple) z := by
  rw [continuous_compact_oriented_multiStapleCylinderObservableBCF_coordinateUpdateWitness_iff_oscillation_ne
    C target f staple hStaple z]
  rw [hInitial, hFinal]
  exact hNe

end

end MathlibAnalytic
end MGAP4D
