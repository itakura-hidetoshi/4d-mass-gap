import MGAP4D.MathlibAnalytic.RationalToRealContinuousExtensionExistence
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorialConnectedSchwingerRealShiftStationarity

/-!
# Existence of the continuous real common-shift extension

Rational connected Schwinger stationarity makes the common-shift family exactly constant on
`ℚ`.  Hence its canonical extension to a real common-shift parameter is simply the same constant
family.  This file constructs that extension, proves that it restricts to the already constructed
rational shifted connected Schwinger function, and proves uniqueness among continuous real
extensions.

Only the common translation parameter is extended here.  The insertion tuple remains
`time : Fin n → ℚ`; no `ℝ`-indexed path law and no independently irrational insertion times are
asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealShiftExistenceNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealShiftExistenceTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealShiftExistenceCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealShiftExistenceSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealShiftExistenceMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealShiftExistenceBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The canonical real common-shift extension of a rational connected Schwinger function.
It is the constant family at the unshifted connected Schwinger value. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerRealShiftExtension
    (μ : Measure (ℚ → ℝ)) (n : ℕ) (time : Fin n → ℚ) (O : Fin n → ℝ → ℝ) : ℝ → ℝ :=
  fun _ =>
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
      μ n time O

/-- The canonical real common-shift extension is continuous. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerRealShiftExtension_continuous
    (μ : Measure (ℚ → ℝ)) (n : ℕ) (time : Fin n → ℚ) (O : Fin n → ℝ → ℝ) :
    Continuous
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerRealShiftExtension
        μ n time O) := by
  exact continuous_const

/-- On every rational shift, the canonical real extension agrees with the actual rational shifted
connected Schwinger function. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_realShiftExtension_rat_eq
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Filter.Tendsto physicalVolume Filter.atTop Filter.atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (n : ℕ) (time : Fin n → ℚ) (O : Fin n → ℝ → ℝ) (q : ℚ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerRealShiftExtension
        L.continuumMeasure.toMeasure n time O (q : ℝ) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalShiftedConnectedSchwingerFunction
        L.continuumMeasure.toMeasure n time O q := by
  change
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
        L.continuumMeasure.toMeasure n time O =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalShiftedConnectedSchwingerFunction
        L.continuumMeasure.toMeasure n time O q
  exact
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L n time q O).symm

/-- The rational common-shift family therefore has a unique continuous extension to all real
common shifts. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_existsUnique_continuous_realShiftExtension
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Filter.Tendsto physicalVolume Filter.atTop Filter.atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (n : ℕ) (time : Fin n → ℚ) (O : Fin n → ℝ → ℝ) :
    ∃! F : ℝ → ℝ,
      Continuous F ∧
      ∀ q : ℚ,
        F (q : ℝ) =
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalShiftedConnectedSchwingerFunction
            L.continuumMeasure.toMeasure n time O q := by
  exact
    MGAP4D.existsUnique_continuous_real_extension_of_rational_eq_const
      (fun q =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalShiftedConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O q)
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
        L.continuumMeasure.toMeasure n time O)
      (fun q =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_shift_eq_self
          H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L n time q O)

/-- The unique continuous real common-shift extension is the canonical constant extension above. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_continuous_realShiftExtension_eq_canonical
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Filter.Tendsto physicalVolume Filter.atTop Filter.atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (n : ℕ) (time : Fin n → ℚ) (O : Fin n → ℝ → ℝ)
    (F : ℝ → ℝ) (hF : Continuous F)
    (hrestrict : ∀ q : ℚ,
      F (q : ℝ) =
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalShiftedConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O q) :
    F =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerRealShiftExtension
        L.continuumMeasure.toMeasure n time O := by
  apply MGAP4D.continuous_eq_of_eq_on_rat hF
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerRealShiftExtension_continuous
      L.continuumMeasure.toMeasure n time O)
  intro q
  calc
    F (q : ℝ) =
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalShiftedConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O q := hrestrict q
    _ =
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O :=
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_shift_eq_self
        H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L n time q O
    _ =
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerRealShiftExtension
          L.continuumMeasure.toMeasure n time O (q : ℝ) := rfl

end
end MathlibAnalytic
end MGAP4D
