import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerFamilyL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridgeL2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExcitationEmbeddedGapTransfer

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology

/-- Common-carrier vector convergence data connecting the uniformly gapped
compact Wilson implicit-Euler excitation spaces to one continuum OS physical
Hilbert space. -/
structure ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerEmbeddedOSBridge
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (P : D.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup)
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ℕ) where
  approximate :
    (n : ℕ) → P.VacuumOrthogonalHilbert →L[ℝ]
      (U.system n).VacuumOrthogonalL2
  embed :
    (n : ℕ) → (U.system n).VacuumOrthogonalL2 →L[ℝ]
      P.PhysicalHilbert
  embed_norm :
    ∀ (n : ℕ) (phi : (U.system n).VacuumOrthogonalL2),
      ‖embed n phi‖ = ‖phi‖
  approximate_tendsto :
    ∀ psi : P.VacuumOrthogonalHilbert,
      Tendsto
        (fun n : ℕ => embed n (approximate n psi))
        atTop
        (nhds (psi : P.PhysicalHilbert))
  evolved_tendsto :
    ∀ (t : NNReal) (psi : P.VacuumOrthogonalHilbert),
      Tendsto
        (fun n : ℕ =>
          embed n (U.uniformImplicitEulerL2 n t (approximate n psi)))
        atTop
        (nhds
          (T.toPhysicalSemigroup.operator t
            (psi : P.PhysicalHilbert)))

namespace ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerEmbeddedOSBridge

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ℕ}

/-- The embedded Wilson implicit-Euler bridge instantiates the abstract
common-carrier excitation-only finite-volume transfer. -/
noncomputable def toExcitationEmbeddedFiniteVolumeGapTransfer
    (B : ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerEmbeddedOSBridge
      P T U) :
    T.ExcitationEmbeddedFiniteVolumeGapTransfer where
  mass := continuousCompactOrientedUniformDobrushinGap U
  mass_pos := continuous_compact_oriented_uniformDobrushinGap_pos U
  decayFactor := implicitEulerGapDecayFactor
    (continuousCompactOrientedUniformDobrushinGap U)
  slope_tendsto :=
    continuous_compact_oriented_uniformImplicitEulerL2_decay_slope U
  FiniteExcitation := fun n => (U.system n).VacuumOrthogonalL2
  finiteNormedAddCommGroup := fun _ => inferInstance
  finiteInnerProductSpace := fun _ => inferInstance
  finiteOperator := fun n t => U.uniformImplicitEulerL2 n t
  approximate := B.approximate
  embed := B.embed
  embed_norm := B.embed_norm
  approximate_tendsto := B.approximate_tendsto
  evolved_tendsto := B.evolved_tendsto
  finite_decay := by
    intro n t phi
    exact continuous_compact_oriented_uniformImplicitEulerL2_norm_bound
      U n t phi

/-- Vector convergence through isometric embeddings supplies the scalar OS
implicit-Euler bridge used by the continuum resolvent layer. -/
noncomputable def toUniformImplicitEulerOSBridge
    (B : ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerEmbeddedOSBridge
      P T U) :
    ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge P T U := by
  let G := B.toExcitationEmbeddedFiniteVolumeGapTransfer
  let F := G.toExcitationFiniteVolumeGapTransfer
  exact
    { approximate := B.approximate
      approximate_norm_tendsto := F.approximate_norm_tendsto
      evolved_norm_tendsto := F.evolved_norm_tendsto }

/-- The embedded Wilson family transfers the uniform Dobrushin lower bound to
the graph-closed continuum OS Hamiltonian. -/
theorem closedRightHamiltonian_inner_ge_uniformDobrushinGap_mul_norm_sq
    (B : ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerEmbeddedOSBridge
      P T U)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    continuousCompactOrientedUniformDobrushinGap U *
        ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) :=
  B.toUniformImplicitEulerOSBridge.
    closedRightHamiltonian_inner_ge_uniformDobrushinGap_mul_norm_sq
      hP psi hpsi

end ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerEmbeddedOSBridge

end

end MathlibAnalytic
end MGAP4D
