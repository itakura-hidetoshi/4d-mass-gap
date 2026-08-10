import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyHaarL2GramSchmidt

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance specialUnitaryTwoGramSchmidtClassTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance specialUnitaryTwoGramSchmidtClassCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance specialUnitaryTwoGramSchmidtClassSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance specialUnitaryTwoGramSchmidtClassMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance specialUnitaryTwoGramSchmidtClassBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance specialUnitaryTwoGramSchmidtClassHaarMeasure :
    Measure.IsHaarMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance specialUnitaryTwoGramSchmidtClassNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The actual continuous representative chosen in the previous layer is not
merely some preimage of its `L²` class: it lies in the finite initial span of
the continuous Wilson-energy powers from which Gram--Schmidt was constructed. -/
theorem specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_mem_power_span_Iic
    (k : ℕ) :
    specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k ∈
      Submodule.span ℝ
        ((fun j : ℕ => specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ j) ''
          Set.Iic k) := by
  let T :
      C(Matrix.specialUnitaryGroup (Fin 2) ℂ, ℝ) →L[ℝ]
        Lp ℝ 2
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
    ContinuousMap.toLp
      (E := ℝ) 2
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) ℝ
  have hMapped :
      specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode k ∈
        Submodule.map T.toLinearMap
          (Submodule.span ℝ
            ((fun j : ℕ => specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ j) ''
              Set.Iic k)) := by
    rw [Submodule.map_span]
    simpa [T, Set.image_image, Function.comp_def] using
      specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode_mem_continuousPower_span_Iic k
  rcases hMapped with ⟨f, hf, hTf⟩
  have hEq :
      specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k = f := by
    apply ContinuousMap.toLp_injective
      (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
      (μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    rw [specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_toLp]
    exact hTf.symm
  rwa [hEq]

/-- Real continuous class functions on `SU(2)` form a linear subspace. -/
def specialUnitaryTwoContinuousClassFunctionSubmodule :
    Submodule ℝ C(Matrix.specialUnitaryGroup (Fin 2) ℂ, ℝ) where
  carrier :=
    {f | ∀ h g : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      f (h * g * h⁻¹) = f g}
  zero_mem' := by
    intro h g
    rfl
  add_mem' := by
    intro f g hf hg h x
    change f (h * x * h⁻¹) + g (h * x * h⁻¹) = f x + g x
    rw [hf h x, hg h x]
  smul_mem' := by
    intro c f hf h x
    change c * f (h * x * h⁻¹) = c * f x
    rw [hf h x]

/-- Every continuous Wilson-energy power belongs to the continuous class-
function submodule. -/
theorem specialUnitaryWilsonPlaquetteEnergyTwoContinuousPower_mem_classFunctionSubmodule
    (k : ℕ) :
    specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ k ∈
      specialUnitaryTwoContinuousClassFunctionSubmodule := by
  change ∀ h g : Matrix.specialUnitaryGroup (Fin 2) ℂ,
    (specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ k) (h * g * h⁻¹) =
      (specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ k) g
  intro h g
  simpa [specialUnitaryWilsonPlaquetteEnergyTwoContinuous,
    specialUnitaryWilsonPlaquetteEnergyPower] using
    (specialUnitaryWilsonPlaquetteEnergyPower_conjInvariant
      (N := 2) (k := k) h g)

/-- Hence the theorem-generated continuous Gram--Schmidt representative is a
class function.  This removes any representative-level conjugation-invariance
assumption from the `SU(2)` Wilson mode construction. -/
theorem specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_mem_classFunctionSubmodule
    (k : ℕ) :
    specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k ∈
      specialUnitaryTwoContinuousClassFunctionSubmodule := by
  apply (Submodule.span_le.2 ?_)
    (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_mem_power_span_Iic k)
  rintro f ⟨j, _hj, rfl⟩
  exact specialUnitaryWilsonPlaquetteEnergyTwoContinuousPower_mem_classFunctionSubmodule j

/-- Pointwise conjugation invariance of each actual continuous Gram--Schmidt
representative. -/
theorem specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_conjInvariant
    (k : ℕ)
    (h g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
        (h * g * h⁻¹) =
      specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k g :=
  specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_mem_classFunctionSubmodule k h g

/-- The actual canonical primary spatial plaquette and its cyclic boundary Haar
holonomy have exactly the same value under every theorem-generated continuous
`SU(2)` Wilson Gram--Schmidt class function. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtMode_eq_boundaryCyclicHolonomy
    (H k : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialPlaquette H)) =
      specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
          H 2
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A)) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteHolonomy_eq_conj_boundaryCyclicHolonomy]
  exact specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_conjInvariant k
    (A (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 0) *
      A (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 1))
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
      H 2
      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A))

/-- The actual continuous `k`-th SU(2) Wilson Gram--Schmidt observable on the
canonical primary spatial plaquette of a full finite configuration. -/
def periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtObservable
    (H k : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
    (periodicHypercubicPlaquetteHolonomy A
      (periodicHypercubicEvenPrimarySpatialPlaquette H))

/-- The same mode read only from the reflection-fixed boundary configuration. -/
def periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable
    (H k : ℕ)
    (b : PeriodicHypercubicEvenBoundaryEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 b)

/-- The actual full-configuration observable factors exactly through the
reflection-fixed boundary restriction. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtObservable_eq_boundaryRestriction
    (H k : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtObservable
        H k A =
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable
        H k ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A) := by
  exact periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtMode_eq_boundaryCyclicHolonomy
    H k A

end

end MathlibAnalytic
end MGAP4D
