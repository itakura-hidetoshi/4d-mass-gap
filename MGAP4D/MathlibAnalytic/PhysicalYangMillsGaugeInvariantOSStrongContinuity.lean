import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveTimeContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- Strong continuity at time zero for the completed physical contraction
semigroup.  The continuity field is stated vectorwise, which is the strong
operator topology relevant to the Osterwalder--Schrader Hamiltonian generator. -/
structure StronglyContinuousPhysicalSemigroup (P : D.OSPreHilbertData) where
  toPhysicalSemigroup : P.PhysicalSemigroup
  strongContinuousAt_zero :
    ∀ psi : P.PhysicalHilbert,
      ContinuousAt (fun t : NNReal => toPhysicalSemigroup.operator t psi) 0

namespace PositiveTimeContractionSemigroup

variable {P : D.OSPreHilbertData}

/-- Minimal observable-side continuity input.  It is required only on the dense
family of represented positive-time observables, not on arbitrary vectors of
the completed physical Hilbert space. -/
structure StrongContinuityOnDenseStates
    (T : P.PositiveTimeContractionSemigroup) : Prop where
  continuousAt_zero_on_physicalState :
    ∀ F : P.Carrier,
      ContinuousAt
        (fun t : NNReal => P.physicalState (T.translate t F)) 0

namespace StrongContinuityOnDenseStates

/-- Contractivity and density transfer continuity at time zero from represented
OS states to every vector of the completed physical Hilbert space. -/
theorem physicalOperator_continuousAt_zero
    {T : P.PositiveTimeContractionSemigroup}
    (hT : T.StrongContinuityOnDenseStates)
    (psi : P.PhysicalHilbert) :
    ContinuousAt (fun t : NNReal => T.physicalOperator t psi) 0 := by
  rw [Metric.continuousAt_iff]
  intro epsilon hepsilon
  have hepsilon3 : 0 < epsilon / 3 := by positivity
  obtain ⟨F, hF⟩ :=
    P.physicalStateLinearMap_denseRange.exists_dist_lt psi hepsilon3
  have hpsiF : dist psi (P.physicalState F) < epsilon / 3 := by
    simpa using hF
  have hFpsi : dist (P.physicalState F) psi < epsilon / 3 := by
    simpa [dist_comm] using hpsiF
  rcases Metric.continuousAt_iff.mp
      (hT.continuousAt_zero_on_physicalState F)
      (epsilon / 3) hepsilon3 with
    ⟨delta, hdelta, hcontinuous⟩
  refine ⟨delta, hdelta, ?_⟩
  intro t ht
  rw [T.physicalOperator_zero_apply]
  have hmiddle :
      dist (T.physicalOperator t (P.physicalState F))
        (P.physicalState F) < epsilon / 3 := by
    rw [T.physicalOperator_on_physicalState t F]
    have h := hcontinuous ht
    simpa [T.translate_zero] using h
  have hleft :
      dist (T.physicalOperator t psi)
          (T.physicalOperator t (P.physicalState F)) ≤
        dist psi (P.physicalState F) := by
    simpa only [dist_eq_norm, map_sub] using
      T.physicalOperator_norm_le t (psi - P.physicalState F)
  calc
    dist (T.physicalOperator t psi) psi ≤
        dist (T.physicalOperator t psi)
            (T.physicalOperator t (P.physicalState F)) +
          dist (T.physicalOperator t (P.physicalState F))
            (P.physicalState F) +
          dist (P.physicalState F) psi :=
      dist_triangle4 _ _ _ _
    _ < epsilon := by linarith

/-- Equivalent strong-limit formulation at the origin. -/
theorem physicalOperator_tendsto_zero
    {T : P.PositiveTimeContractionSemigroup}
    (hT : T.StrongContinuityOnDenseStates)
    (psi : P.PhysicalHilbert) :
    Filter.Tendsto
      (fun t : NNReal => T.physicalOperator t psi)
      (nhds 0) (nhds psi) := by
  simpa [ContinuousAt, T.physicalOperator_zero_apply] using
    hT.physicalOperator_continuousAt_zero psi

/-- Canonical strongly continuous physical contraction semigroup generated from
observable-side continuity on the dense represented-state family. -/
noncomputable def toStronglyContinuousPhysicalSemigroup
    (T : P.PositiveTimeContractionSemigroup)
    (hT : T.StrongContinuityOnDenseStates) :
    P.StronglyContinuousPhysicalSemigroup where
  toPhysicalSemigroup := T.toPhysicalSemigroup
  strongContinuousAt_zero := by
    intro psi
    change ContinuousAt (fun t : NNReal => T.physicalOperator t psi) 0
    exact hT.physicalOperator_continuousAt_zero psi

end StrongContinuityOnDenseStates

end PositiveTimeContractionSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
