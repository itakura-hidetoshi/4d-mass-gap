import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyInfiniteRange
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal

noncomputable section

local instance specialUnitaryTwoGramSchmidtTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance specialUnitaryTwoGramSchmidtCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance specialUnitaryTwoGramSchmidtSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance specialUnitaryTwoGramSchmidtMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance specialUnitaryTwoGramSchmidtBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance specialUnitaryTwoGramSchmidtHaarMeasure :
    Measure.IsHaarMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

private theorem specialUnitaryTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance specialUnitaryTwoGramSchmidtNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The concrete `MemLp.toLp` Wilson-energy power vector from the primary-
plaquette package is exactly the canonical `ContinuousMap.toLp` vector used in
the infinite-range linear-independence theorem. -/
theorem specialUnitaryWilsonPlaquetteEnergyPowerHaarL2_two_eq_continuousMap_toLp
    (k : ℕ) :
    specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
        specialUnitaryTwoRankPositive k =
      ContinuousMap.toLp
        (E := ℝ) 2
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) ℝ
        (specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ k) := by
  apply Lp.ext
  filter_upwards
    [specialUnitaryWilsonPlaquetteEnergyPowerHaarL2_coeFn
      specialUnitaryTwoRankPositive k,
     ContinuousMap.coeFn_toLp
      (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
      (μ := normalizedCompactHaar
        (Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ k)] with U hPower hContinuous
  rw [hPower, hContinuous]
  rfl

/-- The concrete Wilson-energy power vectors from the primary-plaquette Haar
package are linearly independent in normalized-Haar real `L²(SU(2))`.

This identifies the concrete `MemLp.toLp` family with the canonical continuous
family from #1620 and transports its theorem-generated linear independence. -/
theorem specialUnitaryWilsonPlaquetteEnergyPowerHaarL2_two_linearIndependent :
    LinearIndependent ℝ
      (fun k : ℕ =>
        specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
          specialUnitaryTwoRankPositive k) := by
  have hEq :
      (fun k : ℕ =>
        specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
          specialUnitaryTwoRankPositive k) =
      (fun k : ℕ =>
        ContinuousMap.toLp
          (E := ℝ) 2
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) ℝ
          (specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ k)) := by
    funext k
    exact specialUnitaryWilsonPlaquetteEnergyPowerHaarL2_two_eq_continuousMap_toLp k
  rw [hEq]
  exact specialUnitaryWilsonPlaquetteEnergyTwoPower_toLp_linearIndependent

/-- The theorem-generated normalized-Haar `L²(SU(2))` mode family obtained by
Mathlib Gram--Schmidt orthonormalization of the concrete Wilson-energy powers. -/
noncomputable def specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode :
    ℕ → SpecialUnitaryNormalizedHaarL2 2 :=
  InnerProductSpace.gramSchmidtNormed ℝ
    (fun k : ℕ =>
      specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
        specialUnitaryTwoRankPositive k)

/-- The concrete SU(2) Wilson-energy Gram--Schmidt modes are orthonormal in
normalized-Haar real `L²`.  No orthonormal-family existence assumption is
introduced. -/
theorem specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode_orthonormal :
    Orthonormal ℝ specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode := by
  exact InnerProductSpace.gramSchmidtNormed_orthonormal
    specialUnitaryWilsonPlaquetteEnergyPowerHaarL2_two_linearIndependent

/-- Each normalized Gram--Schmidt mode lies in the finite initial span of the
concrete Wilson-energy power family.  This is the triangularity needed to
recover an actual continuous representative rather than only an `L²` class. -/
theorem specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode_mem_power_span_Iic
    (k : ℕ) :
    specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode k ∈
      Submodule.span ℝ
        ((fun j : ℕ =>
          specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
            specialUnitaryTwoRankPositive j) '' Set.Iic k) := by
  change
    InnerProductSpace.gramSchmidtNormed ℝ
        (fun j : ℕ =>
          specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
            specialUnitaryTwoRankPositive j) k ∈ _
  rw [InnerProductSpace.gramSchmidtNormed]
  exact Submodule.smul_mem _ _
    (InnerProductSpace.gramSchmidt_mem_span ℝ
      (fun j : ℕ =>
        specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
          specialUnitaryTwoRankPositive j)
      (le_refl k))

/-- The same finite-span statement expressed entirely through the canonical
continuous Wilson-energy powers and Mathlib `ContinuousMap.toLp`. -/
theorem specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode_mem_continuousPower_span_Iic
    (k : ℕ) :
    specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode k ∈
      Submodule.span ℝ
        ((fun j : ℕ =>
          ContinuousMap.toLp
            (E := ℝ) 2
            (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) ℝ
            (specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ j)) '' Set.Iic k) := by
  have hSet :
      ((fun j : ℕ =>
          specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
            specialUnitaryTwoRankPositive j) '' Set.Iic k) =
        ((fun j : ℕ =>
          ContinuousMap.toLp
            (E := ℝ) 2
            (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) ℝ
            (specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ j)) '' Set.Iic k) := by
    ext v
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj,
        (specialUnitaryWilsonPlaquetteEnergyPowerHaarL2_two_eq_continuousMap_toLp j).symm⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj,
        specialUnitaryWilsonPlaquetteEnergyPowerHaarL2_two_eq_continuousMap_toLp j⟩
  rw [← hSet]
  exact specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode_mem_power_span_Iic k

/-- Every theorem-generated SU(2) Wilson Gram--Schmidt `L²` mode lies in the
range of the canonical continuous-function embedding. -/
theorem specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode_mem_continuousMap_toLp_range
    (k : ℕ) :
    specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode k ∈
      (ContinuousMap.toLp
        (E := ℝ) 2
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) ℝ).range := by
  apply (Submodule.span_le.2 ?_)
    (specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode_mem_continuousPower_span_Iic k)
  rintro v ⟨j, hj, rfl⟩
  exact ⟨specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ j, rfl⟩

/-- The canonical actual continuous representative of the `k`-th theorem-
generated SU(2) Wilson Gram--Schmidt `L²` mode. -/
noncomputable def specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode
    (k : ℕ) :
    C(Matrix.specialUnitaryGroup (Fin 2) ℂ, ℝ) :=
  (specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode_mem_continuousMap_toLp_range k).choose

/-- The chosen continuous representative maps exactly to the normalized-Haar
`L²` Gram--Schmidt mode. -/
theorem specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_toLp
    (k : ℕ) :
    ContinuousMap.toLp
        (E := ℝ) 2
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) ℝ
        (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k) =
      specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode k :=
  (specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode_mem_continuousMap_toLp_range k).choose_spec

/-- Realize the theorem-generated SU(2) Wilson-energy orthonormal modes on the
actual canonical primary spatial plaquette inside the full boundary Haar
`L²`. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
    (H : ℕ) :
    ℕ → PeriodicHypercubicEvenBoundaryHaarL2 H 2 :=
  (periodicHypercubicEvenPrimarySpatialPlaquetteHolonomyBoundaryL2Pullback H 2) ∘
    specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode

/-- Exact primary-plaquette boundary realization preserves orthonormality of
the SU(2) Wilson-energy Gram--Schmidt family. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2_orthonormal
    (H : ℕ) :
    Orthonormal ℝ
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2 H) := by
  exact specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode_orthonormal.comp_linearIsometry
    (periodicHypercubicEvenPrimarySpatialPlaquetteHolonomyBoundaryL2Pullback H 2)

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoRankPositive beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}

/-- The theorem-generated SU(2) Wilson-energy Gram--Schmidt mode transported to
a selected interacting/projective finite marginal through the exact canonical
primary-plaquette isometry. -/
noncomputable def primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n : ℕ) :
    ℕ → Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) :=
  (R.primarySpatialPlaquetteHaarProjectiveL2Isometry n) ∘
    specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode

/-- Every selected projective finite marginal therefore contains the concrete
SU(2) primary-plaquette Wilson-energy Gram--Schmidt family as an orthonormal
family. -/
theorem primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode_orthonormal
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n : ℕ) :
    Orthonormal ℝ
      (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n) := by
  exact R.primarySpatialPlaquetteHaarProjectiveL2Isometry_orthonormal n
    specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode
    specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode_orthonormal

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

end

end MathlibAnalytic
end MGAP4D
