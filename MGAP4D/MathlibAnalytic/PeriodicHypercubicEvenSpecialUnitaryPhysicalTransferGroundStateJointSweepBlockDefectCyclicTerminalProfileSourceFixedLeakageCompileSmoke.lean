import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicTerminalProfileSourceFixedLeakage

namespace MGAP4D.MathlibAnalytic

#check
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicSourceResidualBudget_of_sourceFixedLeakage

-- Recheck the algebraic identity under the full physical import graph.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q : E →L[ℝ] E)
    (hPIdem : P.comp P = P) (hQIdem : Q.comp Q = Q)
    (hPSymm : ∀ u v : E, inner ℝ (P u) v = inner ℝ u (P v))
    (hQSymm : ∀ u v : E, inner ℝ (Q u) v = inner ℝ u (Q v))
    (x : E) :
    ‖Q x - P (Q x)‖ ^ 2 =
      inner ℝ (Q x - P (Q x)) (x - P x) +
        inner ℝ (P (Q x) - Q (P (Q x))) (x - Q x) :=
  realHilbertProjection_targetResidual_sq_eq_inner_residual_add_sourceLeakage
    P Q hPIdem hQIdem hPSymm hQSymm x

-- Regression: a leading let is not the first source/side-condition binder.
example {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ι → E →L[ℝ] E) (target : ι)
    (hIdem : ∀ i, (P i).comp (P i) = P i) :
    (let Q := P
     ∀ source : ι, source ≠ target → ∀ x : E, Q source (Q source x) = Q source x) := by
  change ∀ source : ι, source ≠ target → ∀ x : E,
    P source (P source x) = P source x
  intro source _ x
  simpa only [ContinuousLinearMap.comp_apply] using
    congrArg (fun T : E →L[ℝ] E => T x) (hIdem source)

end MGAP4D.MathlibAnalytic
