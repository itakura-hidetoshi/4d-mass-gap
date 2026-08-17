import MGAP4D.MathlibAnalytic.RationalToRealContinuousStationarity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorialConnectedSchwingerStationarity

/-!
# Real-shift stationarity of connected Schwinger extensions

This file connects the generic `ℚ → ℝ` dense-range uniqueness lemma to the actual
finite connected Schwinger functions already constructed on rational Euclidean time.

It remains deliberately an extension theorem: a continuous real-shift family whose
restriction to rational shifts is the existing rational shifted connected Schwinger
function is forced to be stationary at every real shift. No existence of a real-time
path law or continuous modification is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

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

end
end MathlibAnalytic
end MGAP4D
