import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteClusteringInput
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A result receipt for the concrete infinite-lattice `Z₂` plaquette
connected-correlation bound attached to one standard clustering input.

The receipt stores the selected Prokhorov subsequential weak limit, the two local
bounded continuous plaquette observables, and the explicit exponential bound.

This remains a proof-engineering receipt on the compact infinite-lattice binary
carrier.  It does not construct a continuum `ℝ⁴` gauge-field configuration
space, DLR state, reflection-positivity limit, OS reconstruction, Hamiltonian,
Hamiltonian spectral gap, physical mass gap, or an unconditional proof of the
four-dimensional Yang--Mills mass gap problem. -/
structure z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceipt
    (I : z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInput) where
  prokhorovLimit :
    PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (z2PeriodicHypercubicInfiniteLatticeEmbedding I.beta I.hBeta).toLatticeEmbedding
  sourceObservable :
    BoundedContinuousFunction Z2InfiniteHypercubicBinaryConfiguration ℝ
  targetObservable :
    BoundedContinuousFunction Z2InfiniteHypercubicBinaryConfiguration ℝ
  connectedCorrelation_abs_le :
    abs (prokhorovLimit.toWeakLimit.continuumConnectedCorrelation
        sourceObservable targetObservable) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor I.beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate I.beta *
            (I.distance : ℝ))

namespace z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceipt

/-- The canonical receipt extracted from a standard clustering input. -/
noncomputable def ofInput
    (I : z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInput) :
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceipt I :=
  { prokhorovLimit := I.prokhorovLimit
    sourceObservable := I.sourceObservable
    targetObservable := I.targetObservable
    connectedCorrelation_abs_le := I.connectedCorrelation_abs_le }

/-- The selected weak-limit receipt bound obtained from a standard clustering
input. -/
theorem ofInput_connectedCorrelation_abs_le
    (I : z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInput) :
    abs ((ofInput I).prokhorovLimit.toWeakLimit.continuumConnectedCorrelation
        (ofInput I).sourceObservable (ofInput I).targetObservable) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor I.beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate I.beta *
            (I.distance : ℝ)) :=
  (ofInput I).connectedCorrelation_abs_le

/-- The canonical receipt uses the standard input's selected Prokhorov limit. -/
theorem ofInput_prokhorovLimit_eq
    (I : z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInput) :
    (ofInput I).prokhorovLimit = I.prokhorovLimit :=
  rfl

/-- The canonical receipt uses the standard input's source observable. -/
theorem ofInput_sourceObservable_eq
    (I : z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInput) :
    (ofInput I).sourceObservable = I.sourceObservable :=
  rfl

/-- The canonical receipt uses the standard input's target observable. -/
theorem ofInput_targetObservable_eq
    (I : z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringInput) :
    (ofInput I).targetObservable = I.targetObservable :=
  rfl

end z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringReceipt

end

end MathlibAnalytic
end MGAP4D
