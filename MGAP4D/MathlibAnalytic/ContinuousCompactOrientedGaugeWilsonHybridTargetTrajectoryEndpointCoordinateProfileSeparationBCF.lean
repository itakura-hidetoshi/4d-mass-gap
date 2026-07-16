import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- A strict coordinate-profile separation witness on one fixed endpoint-transport
fiber.  At one trajectory rank, the complete transport range over the fiber above
`gLower` lies below `a`, while the range over the fiber above `gUpper` lies above
`b`, with `a < b`. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : Prop :=
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF target O z
  ∃ rank : Finset.Iic (Fintype.card C.base.geometry.Edge),
    ∃ gLower gUpper : C.base.Gauge,
      ∃ a b : ℝ,
        a < b ∧
        (∀ x : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier,
          x rank = gLower → T x ≤ a) ∧
        (∀ y : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier,
          y rank = gUpper → b ≤ T y)

/-- A strict coordinate-profile gap produces two nonempty open Gauge regions on
which every cross-cylinder pair has different endpoint transports.

The proof projects the two closed bad-trajectory sets to the selected coordinate.
The full trajectory carrier is compact, so both projected bad-coordinate sets are
compact and therefore closed. Their complements are the required open regions. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF_implies_open_region_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF
        target O z) :
    C.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
      target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF
    at hWitness
  dsimp only at hWitness
  rcases hWitness with
    ⟨rank, gLower, gUpper, a, b, hab, hLowerFiber, hUpperFiber⟩
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF target O z
  let c : ℝ := (a + b) / 2
  let badLower :
      Set C.independentPairHybridTargetTrajectoryEndpointFiberCarrier :=
    {x | c ≤ T x}
  let badUpper :
      Set C.independentPairHybridTargetTrajectoryEndpointFiberCarrier :=
    {x | T x ≤ c}
  let lowerForbidden : Set C.base.Gauge :=
    (fun x : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier =>
      x rank) '' badLower
  let upperForbidden : Set C.base.Gauge :=
    (fun x : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier =>
      x rank) '' badUpper
  let lower : Set C.base.Gauge := lowerForbiddenᶜ
  let upper : Set C.base.Gauge := upperForbiddenᶜ
  have hac : a < c := by
    dsimp [c]
    linarith
  have hcb : c < b := by
    dsimp [c]
    linarith
  have hT : Continuous T := by
    exact
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_continuous
        C target O z
  have hBadLowerClosed : IsClosed badLower := by
    dsimp [badLower]
    exact isClosed_le continuous_const hT
  have hBadUpperClosed : IsClosed badUpper := by
    dsimp [badUpper]
    exact isClosed_le hT continuous_const
  have hLowerForbiddenCompact : IsCompact lowerForbidden := by
    dsimp [lowerForbidden]
    exact hBadLowerClosed.isCompact.image
      (continuous_apply rank).continuousOn
  have hUpperForbiddenCompact : IsCompact upperForbidden := by
    dsimp [upperForbidden]
    exact hBadUpperClosed.isCompact.image
      (continuous_apply rank).continuousOn
  have hLowerForbiddenClosed : IsClosed lowerForbidden :=
    hLowerForbiddenCompact.isClosed
  have hUpperForbiddenClosed : IsClosed upperForbidden :=
    hUpperForbiddenCompact.isClosed
  have hLowerOpen : IsOpen lower := by
    dsimp [lower]
    exact hLowerForbiddenClosed.isOpen_compl
  have hUpperOpen : IsOpen upper := by
    dsimp [upper]
    exact hUpperForbiddenClosed.isOpen_compl
  have hgLower : gLower ∈ lower := by
    change gLower ∉ lowerForbidden
    intro hg
    rcases hg with ⟨x, hxBad, hxRank⟩
    have hxBad' : c ≤ T x := by
      simpa [badLower] using hxBad
    have hxBound : T x ≤ a := by
      exact hLowerFiber x hxRank
    exact (not_le_of_gt hac) (hxBad'.trans hxBound)
  have hgUpper : gUpper ∈ upper := by
    change gUpper ∉ upperForbidden
    intro hg
    rcases hg with ⟨y, hyBad, hyRank⟩
    have hyBad' : T y ≤ c := by
      simpa [badUpper] using hyBad
    have hyBound : b ≤ T y := by
      exact hUpperFiber y hyRank
    exact (not_le_of_gt hcb) (hyBound.trans hyBad')
  refine
    ⟨rank, lower, upper, hLowerOpen, ⟨gLower, hgLower⟩,
      hUpperOpen, ⟨gUpper, hgUpper⟩, ?_⟩
  intro x hx y hy
  have hxNot : x rank ∉ lowerForbidden := by
    simpa [
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF,
      lower] using hx
  have hyNot : y rank ∉ upperForbidden := by
    simpa [
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF,
      upper] using hy
  have hxLt : T x < c := by
    apply lt_of_not_ge
    intro hcx
    apply hxNot
    exact ⟨x, by simpa [badLower] using hcx, rfl⟩
  have hyGt : c < T y := by
    apply lt_of_not_ge
    intro hyc
    apply hyNot
    exact ⟨y, by simpa [badUpper] using hyc, rfl⟩
  exact ne_of_lt (hxLt.trans hyGt)

/-- A strict coordinate-profile separation witness forces positive endpoint
innovation mass on the fixed original-pair fiber. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF_implies_innovationMass_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF_implies_innovationMass_pos
      C target O z
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF_implies_open_region_witness
        C target O z hWitness)

/-- A strict coordinate-profile separation witness forces positive fixed-fiber
conditional variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF_implies_gap_pos
      C target O z
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF_implies_open_region_witness
        C target O z hWitness)

/-- A strict coordinate-profile separation witness forces positive fixed-fiber iid
double endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF_implies_double_energy_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF_implies_double_energy_pos
      C target O z
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF_implies_open_region_witness
        C target O z hWitness)

/-- A non-null Gibbs-pair family carrying strict coordinate-profile separation
witnesses. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : Prop :=
  ∃ᵐ z ∂(C.gibbsMeasure.prod C.gibbsMeasure),
    C.independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF
      target O z

/-- A non-null family of strict coordinate-profile gaps produces the open-region
witness family. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF_implies_fiberwise_open_region_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF
      target O := by
  exact hWitness.mono fun z hz =>
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF_implies_open_region_witness
      C target O z hz

/-- A non-null family of strict coordinate-profile gaps forces positive global
conditional variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF_implies_gap_pos
      C target O
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF_implies_fiberwise_open_region_witness
        C target O hWitness)

/-- A non-null family of strict coordinate-profile gaps forces positive global iid
double endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF_implies_double_energy_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
      target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF_implies_double_energy_pos
      C target O
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF_implies_fiberwise_open_region_witness
        C target O hWitness)

/-- With positive native energy, a non-null family of strict coordinate-profile
gaps forces the exact endpoint correlation ratio below one. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF_implies_correlationRatio_lt_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF target O < 1 := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF_implies_correlationRatio_lt_one
      C target O hNative
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF_implies_fiberwise_open_region_witness
        C target O hWitness)

/-- With positive native energy, a non-null family of strict coordinate-profile
gaps produces a strict endpoint correlation factor. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF_implies_exists_strict_correlation_factor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF
        target O) :
    ∃ ρ : ℝ, ρ < 1 ∧
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O ≤
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF_implies_exists_strict_correlation_factor
      C target O hNative
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF_implies_fiberwise_open_region_witness
        C target O hWitness)

end

end MathlibAnalytic
end MGAP4D
