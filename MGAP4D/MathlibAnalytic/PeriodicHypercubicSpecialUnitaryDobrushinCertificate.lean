import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonSharedPlaquetteEnergyGap
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFourDimensionalDobrushinCertificate

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem periodicHypercubicSpecialUnitary_plaquetteEnergy_le_two
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.plaquetteEnergy U ≤ 2 := by
  change specialUnitaryWilsonPlaquetteEnergy N U ≤ 2
  exact specialUnitaryWilsonPlaquetteEnergy_le_two hN U

theorem periodicHypercubicSpecialUnitary_activeLocalActionDifference_abs_le_two
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEdge n)
    (A : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.Configuration)
    (g u : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hActive : source ∈
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).base.activePlaquetteNeighbors target) :
    |(periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).base.targetLocalPlaquetteAction
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta hBeta).base.replaceLink A target u) target -
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).base.targetLocalPlaquetteAction
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta hBeta).base.replaceLink
              ((periodicHypercubicSpecialUnitaryWilsonSystem
                n N hN beta hBeta).base.replaceLink A source g)
              target u) target| ≤ 2 := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta hBeta
  let I := periodicHypercubicSpecialUnitaryIncidenceCertificate
    n N hn hN beta hBeta
  have hRaw :=
    compact_oriented_targetLocalAction_sub_sourceReplace_abs_le_sharedCard_mul
      C.base 2
      (periodicHypercubicSpecialUnitary_plaquetteEnergy_le_two
        n N hN beta hBeta)
      A target source u g
  have hCardNat := I.activeSharedPlaquetteCard_le_one
    target source hActive
  have hCard :
      ((C.base.sharedPlaquettes target source).card : ℝ) ≤ 1 := by
    exact_mod_cast hCardNat
  have hScale :
      ((C.base.sharedPlaquettes target source).card : ℝ) * 2 ≤ 2 := by
    nlinarith
  exact le_trans hRaw hScale

theorem periodicHypercubicSpecialUnitary_activeLocalActionDifferenceOscillationBound_four
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta) :
    ContinuousCompactOrientedGaugeWilsonSystem.ActiveLocalActionDifferenceOscillationBound
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta) 4 := by
  intro target source A g hActive u v
  have hu := abs_le.mp
    (periodicHypercubicSpecialUnitary_activeLocalActionDifference_abs_le_two
      n N hn hN beta hBeta target source A g u hActive)
  have hv := abs_le.mp
    (periodicHypercubicSpecialUnitary_activeLocalActionDifference_abs_le_two
      n N hn hN beta hBeta target source A g v hActive)
  linarith

noncomputable def periodicHypercubicSpecialUnitary_dobrushinMatrixData
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (hThreshold :
      (Real.exp (beta * 4) - 1) / (Real.exp (beta * 4) + 1) <
        (18 : ℝ)⁻¹) :
    ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta hBeta
  exact
    ContinuousCompactOrientedGaugeWilsonFourDimensionalIncidenceCertificate.dobrushinMatrixData_of_localActionOscillation
      (periodicHypercubicSpecialUnitaryIncidenceCertificate
        n N hn hN beta hBeta)
      4 (by norm_num)
      (periodicHypercubicSpecialUnitary_activeLocalActionDifferenceOscillationBound_four
        n N hn hN beta hBeta)
      (by
        simpa [continuousCompactOrientedGaugeWilsonConditionalTVMajorant, C] using
          hThreshold)

end
end MathlibAnalytic
end MGAP4D
