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

end MGAP4D.MathlibAnalytic
