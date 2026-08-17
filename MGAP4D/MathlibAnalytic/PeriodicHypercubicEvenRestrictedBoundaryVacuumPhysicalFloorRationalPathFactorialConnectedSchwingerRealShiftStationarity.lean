import MGAP4D.MathlibAnalytic.RationalToRealContinuousStationarity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorialConnectedSchwingerStationarity

/-!
# Real-shift stationarity of connected Schwinger extensions

This file connects the generic `ℚ → ℝ` dense-range uniqueness lemma to the actual
finite connected Schwinger functions already constructed on rational Euclidean time.

For the common-shift scalar family, rational stationarity already makes the rational
function constant. Hence there is a canonical continuous extension to `ℝ`, namely the
constant function with value the unshifted connected Schwinger function. This gives
existence and uniqueness of the continuous scalar extension without adding an analytic
continuity hypothesis.

This still does not construct an `ℝ`-indexed path law or define observables at arbitrary
irrational insertion times. It only closes the common-shift scalar extension problem.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealShiftNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealShiftTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealShiftCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealShiftSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealShiftMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealShiftBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The canonical real common-shift extension of a rational connected Schwinger function.

Because the actual rational family is stationary, the only continuous extension compatible
with that family is the constant function at the unshifted connected Schwinger value. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerRealShiftExtension
    (μ : Measure (ℚ → ℝ)) (n : ℕ) (time : Fin n → ℚ) (O : Fin n → ℝ → ℝ) : ℝ → ℝ :=
  fun _ =>
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
      μ n time O

/-- The canonical real common-shift extension is continuous. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerRealShiftExtension_continuous
    (μ : Measure (ℚ → ℝ)) (n : ℕ) (time : Fin n → ℚ) (O : Fin n → ℝ → ℝ) :
    Continuous
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerRealShiftExtension
        μ n time O) := by
  exact continuous_const

/-- On rational shifts, the canonical real extension agrees exactly with the actual
rational shifted connected Schwinger function. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_realShiftExtension_rat_eq_shifted
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
  symm
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L n time q O

/-- The canonical real common-shift extension is stationary at every real shift. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerRealShiftExtension_eq_self
    (μ : Measure (ℚ → ℝ)) (n : ℕ) (time : Fin n → ℚ) (O : Fin n → ℝ → ℝ)
    (r : ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerRealShiftExtension
        μ n time O r =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
        μ n time O := by
  rfl

/-- Any continuous real-shift extension of the actual rational connected Schwinger
function is exactly stationary under every real common shift. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_realShift_eq_self_of_continuous_extension
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
    (realShiftedConnectedSchwinger : ℝ → ℝ)
    (hcontinuous : Continuous realShiftedConnectedSchwinger)
    (hrestrict : ∀ q : ℚ,
      realShiftedConnectedSchwinger (q : ℝ) =
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalShiftedConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O q) :
    ∀ r : ℝ,
      realShiftedConnectedSchwinger r =
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O := by
  apply MGAP4D.real_eq_const_of_rational_eq_const
    realShiftedConnectedSchwinger hcontinuous
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
      L.continuumMeasure.toMeasure n time O)
  intro q
  calc
    realShiftedConnectedSchwinger (q : ℝ) =
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalShiftedConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O q := hrestrict q
    _ =
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O :=
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_shift_eq_self
        H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L n time q O

/-- The canonical constant extension is the unique continuous real-shift extension
whose rational restriction is the actual rational shifted connected Schwinger family. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_realShiftExtension_unique
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
    (realShiftedConnectedSchwinger : ℝ → ℝ)
    (hcontinuous : Continuous realShiftedConnectedSchwinger)
    (hrestrict : ∀ q : ℚ,
      realShiftedConnectedSchwinger (q : ℝ) =
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalShiftedConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O q) :
    realShiftedConnectedSchwinger =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerRealShiftExtension
        L.continuumMeasure.toMeasure n time O := by
  apply MGAP4D.continuous_eq_of_eq_on_rat
    hcontinuous
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerRealShiftExtension_continuous
      L.continuumMeasure.toMeasure n time O)
  intro q
  calc
    realShiftedConnectedSchwinger (q : ℝ) =
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
