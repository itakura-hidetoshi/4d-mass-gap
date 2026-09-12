import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2PeriodicCanonicalProkhorovClustering
import MGAP4D.MathlibAnalytic.PhysicalYangMillsCoerciveFunctional

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A canonical-radius coercive moment certificate on the original periodic
finite-lattice laws chooses a Prokhorov subsequential continuum limit.

The compact-sublevel and uniform-moment inputs are consumed by the existing
Markov-tail and Prokhorov layers. -/
noncomputable def
    PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData.prokhorovLimitOfLatticeNaturalRadiusCoerciveMoment
    {beta : ℝ}
    {hBeta : 0 < beta}
    {E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta}
    {distance : ℕ}
    (D : PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData E distance)
    (C : E.toLatticeEmbedding.LatticeNaturalRadiusCoerciveMomentCertificate) :
    PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding :=
  D.prokhorovLimitOfTight
    (E.toLatticeEmbedding.isTight_of_latticeNaturalRadiusCoerciveMoment C)

/-- A finite uniform coercive moment on the original periodic Gibbs laws is
sufficient for a selected subsequential continuum connected-correlation bound.

No independent tightness or weak-convergence hypothesis remains. -/
theorem
    PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData.continuum_abs_le_of_latticeNaturalRadiusCoerciveMoment
    {beta : ℝ}
    {hBeta : 0 < beta}
    {E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta}
    {distance : ℕ}
    (D : PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData E distance)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta)
    (C : E.toLatticeEmbedding.LatticeNaturalRadiusCoerciveMomentCertificate) :
    let L := D.prokhorovLimitOfLatticeNaturalRadiusCoerciveMoment C
    abs (L.toWeakLimit.continuumConnectedCorrelation
      D.sourceObservable D.targetObservable) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) := by
  dsimp only
  exact D.continuum_abs_le_of_tight K
    (E.toLatticeEmbedding.isTight_of_latticeNaturalRadiusCoerciveMoment C)

/-- A separated physical coercive functional and its finite-lattice uniform
moment receipt also choose a Prokhorov subsequential continuum limit. -/
noncomputable def
    PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData.prokhorovLimitOfLatticeCoerciveFunctionalMoment
    {beta : ℝ}
    {hBeta : 0 < beta}
    {E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta}
    {distance : ℕ}
    (D : PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData E distance)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (M : E.toLatticeEmbedding.LatticeCoerciveFunctionalMomentBound Phi) :
    PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding :=
  D.prokhorovLimitOfTight M.isTight

/-- The separated coercive-functional and lattice-moment receipts imply the
same explicit subsequential continuum clustering estimate. -/
theorem
    PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData.continuum_abs_le_of_latticeCoerciveFunctionalMoment
    {beta : ℝ}
    {hBeta : 0 < beta}
    {E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta}
    {distance : ℕ}
    (D : PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData E distance)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (M : E.toLatticeEmbedding.LatticeCoerciveFunctionalMomentBound Phi) :
    let L := D.prokhorovLimitOfLatticeCoerciveFunctionalMoment Phi M
    abs (L.toWeakLimit.continuumConnectedCorrelation
      D.sourceObservable D.targetObservable) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) := by
  dsimp only
  exact D.continuum_abs_le_of_tight K M.isTight

end

end MathlibAnalytic
end MGAP4D
