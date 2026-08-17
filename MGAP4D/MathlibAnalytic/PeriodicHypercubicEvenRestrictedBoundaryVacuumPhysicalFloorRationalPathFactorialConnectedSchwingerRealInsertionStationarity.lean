import MGAP4D.MathlibAnalytic.RationalPiToRealContinuousStationarity
import MGAP4D.MathlibAnalytic.RationalToRealContinuousStationarity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorialConnectedSchwingerStationarity

/-!
# Real insertion-time stationarity of continuous Schwinger extensions

This file upgrades the common-translation identity from rational insertion tuples to arbitrary
real insertion tuples, conditional only on a continuous real-tuple extension whose restriction
on rational tuples is the already constructed rational connected Schwinger function.

No existence of that full real-tuple extension is asserted here. In particular this does not
construct an `ℝ`-indexed path law or a Minkowski continuation.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealInsertionNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealInsertionTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealInsertionCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealInsertionSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealInsertionMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerRealInsertionBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Evaluating the rational connected Schwinger function at a commonly shifted rational tuple
is definitionally the shifted connected Schwinger function. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction_add_eq_shifted
    (μ : Measure (ℚ → ℝ)) (n : ℕ) (time : Fin n → ℚ) (O : Fin n → ℝ → ℝ)
    (q : ℚ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
        μ n (fun i => time i + q) O =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalShiftedConnectedSchwingerFunction
        μ n time O q := by
  rfl

/-- If a continuous connected Schwinger function on real insertion tuples restricts to the
actual rational connected Schwinger function, then every rational common shift already acts
trivially on every real insertion tuple. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_realInsertion_ratShift_eq_self_of_continuous_extension
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
    (n : ℕ) (O : Fin n → ℝ → ℝ)
    (realConnectedSchwinger : (Fin n → ℝ) → ℝ)
    (hcontinuous : Continuous realConnectedSchwinger)
    (hrestrict : ∀ time : Fin n → ℚ,
      realConnectedSchwinger (MGAP4D.ratPiCast time) =
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O)
    (q : ℚ) :
    ∀ time : Fin n → ℝ,
      realConnectedSchwinger (MGAP4D.realCommonShift time (q : ℝ)) =
        realConnectedSchwinger time := by
  have hEq :
      (fun time : Fin n → ℝ =>
        realConnectedSchwinger (MGAP4D.realCommonShift time (q : ℝ))) =
        realConnectedSchwinger := by
    apply MGAP4D.continuous_eq_of_eq_on_rat_pi
      (hcontinuous.comp (MGAP4D.realCommonShift_continuous_time (ι := Fin n) (q : ℝ)))
      hcontinuous
    intro time
    have hShiftCast :
        MGAP4D.realCommonShift (MGAP4D.ratPiCast time) (q : ℝ) =
          MGAP4D.ratPiCast (fun i => time i + q) := by
      funext i
      simp [MGAP4D.realCommonShift, MGAP4D.ratPiCast]
    change
      realConnectedSchwinger
          (MGAP4D.realCommonShift (MGAP4D.ratPiCast time) (q : ℝ)) =
        realConnectedSchwinger (MGAP4D.ratPiCast time)
    rw [hShiftCast]
    calc
      realConnectedSchwinger (MGAP4D.ratPiCast (fun i => time i + q)) =
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
            L.continuumMeasure.toMeasure n (fun i => time i + q) O :=
        hrestrict (fun i => time i + q)
      _ = periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalShiftedConnectedSchwingerFunction
            L.continuumMeasure.toMeasure n time O q :=
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction_add_eq_shifted
          L.continuumMeasure.toMeasure n time O q
      _ = periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
            L.continuumMeasure.toMeasure n time O :=
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_shift_eq_self
          H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L n time q O
      _ = realConnectedSchwinger (MGAP4D.ratPiCast time) := (hrestrict time).symm
  intro time
  exact congrFun hEq time

/-- A continuous real-insertion-time extension of the actual rational connected Schwinger
function is stationary under every real common translation. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_realInsertion_realShift_eq_self_of_continuous_extension
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
    (n : ℕ) (O : Fin n → ℝ → ℝ)
    (realConnectedSchwinger : (Fin n → ℝ) → ℝ)
    (hcontinuous : Continuous realConnectedSchwinger)
    (hrestrict : ∀ time : Fin n → ℚ,
      realConnectedSchwinger (MGAP4D.ratPiCast time) =
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
          L.continuumMeasure.toMeasure n time O) :
    ∀ (time : Fin n → ℝ) (r : ℝ),
      realConnectedSchwinger (MGAP4D.realCommonShift time r) =
        realConnectedSchwinger time := by
  intro time
  apply MGAP4D.real_eq_const_of_rational_eq_const
    (fun r : ℝ => realConnectedSchwinger (MGAP4D.realCommonShift time r))
    (hcontinuous.comp (MGAP4D.realCommonShift_continuous_shift time))
    (realConnectedSchwinger time)
  intro q
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_realInsertion_ratShift_eq_self_of_continuous_extension
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L n O
      realConnectedSchwinger hcontinuous hrestrict q time

end
end MathlibAnalytic
end MGAP4D
