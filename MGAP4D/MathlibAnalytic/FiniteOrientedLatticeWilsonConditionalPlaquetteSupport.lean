import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalRemoteCancellation
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalActionOscillation
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkConditionalFiberInvariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The oriented conditional total variation vanishes on an off-link fiber. -/
theorem finite_oriented_singleLinkConditionalTotalVariation_eq_zero_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkConditionalTotalVariation A B e = 0 := by
  classical
  have hPMF :
      L.singleLinkConditionalPMF A e =
        L.singleLinkConditionalPMF B e :=
    finite_oriented_singleLinkConditionalPMF_eq_of_agreeOffLink
      L A B e hAgree
  simp [FiniteOrientedLatticeWilsonSystem.singleLinkConditionalTotalVariation,
    hPMF]

/-- A non-neighbor source cannot change the target-local Boltzmann factor. -/
theorem finite_oriented_targetLocalSingleLinkBoltzmannWeight_eq_of_not_neighbor
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source)
    (g : L.Gauge) :
    L.targetLocalSingleLinkBoltzmannWeight A target g =
      L.targetLocalSingleLinkBoltzmannWeight B target g := by
  unfold FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight
  rw [finite_oriented_targetLocalPlaquetteAction_replaceLink_eq_of_not_neighbor
    L A B target source g hNotNeighbor hAgree]

/-- The target-local partition function is unchanged by a non-neighbor update. -/
theorem finite_oriented_targetLocalSingleLinkPartitionFunction_eq_of_not_neighbor
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source) :
    L.targetLocalSingleLinkPartitionFunction A target =
      L.targetLocalSingleLinkPartitionFunction B target := by
  unfold FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkPartitionFunction
  apply tsum_congr
  intro g
  exact finite_oriented_targetLocalSingleLinkBoltzmannWeight_eq_of_not_neighbor
    L A B target source hNotNeighbor hAgree g

/-- The normalized target-local conditional law has exact plaquette support. -/
theorem finite_oriented_targetLocalSingleLinkConditionalPMF_eq_of_not_neighbor
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source) :
    L.targetLocalSingleLinkConditionalPMF A target =
      L.targetLocalSingleLinkConditionalPMF B target := by
  ext g
  rw [finite_oriented_targetLocalSingleLinkConditionalPMF_apply,
    finite_oriented_targetLocalSingleLinkConditionalPMF_apply,
    finite_oriented_targetLocalSingleLinkBoltzmannWeight_eq_of_not_neighbor
      L A B target source hNotNeighbor hAgree g,
    finite_oriented_targetLocalSingleLinkPartitionFunction_eq_of_not_neighbor
      L A B target source hNotNeighbor hAgree]

/-- The exact oriented conditional law is unchanged outside plaquette support. -/
theorem finite_oriented_singleLinkConditionalPMF_eq_of_not_plaquetteNeighbor
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source) :
    L.singleLinkConditionalPMF A target =
      L.singleLinkConditionalPMF B target := by
  rw [finite_oriented_singleLinkConditionalPMF_eq_targetLocal,
    finite_oriented_singleLinkConditionalPMF_eq_targetLocal]
  exact
    finite_oriented_targetLocalSingleLinkConditionalPMF_eq_of_not_neighbor
      L A B target source hNotNeighbor hAgree

/-- Exact conditional total variation is zero outside plaquette support. -/
theorem finite_oriented_singleLinkConditionalTotalVariation_eq_zero_of_not_plaquetteNeighbor
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source) :
    L.singleLinkConditionalTotalVariation A B target = 0 := by
  classical
  have hPMF :=
    finite_oriented_singleLinkConditionalPMF_eq_of_not_plaquetteNeighbor
      L A B target source hNotNeighbor hAgree
  simp [FiniteOrientedLatticeWilsonSystem.singleLinkConditionalTotalVariation,
    hPMF]

end

end MathlibAnalytic
end MGAP4D
