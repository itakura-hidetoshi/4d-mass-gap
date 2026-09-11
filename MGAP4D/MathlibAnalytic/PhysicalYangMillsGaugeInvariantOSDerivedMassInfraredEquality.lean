import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedMassFullVacuumOrthogonalNormDecay
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVariationalInfraredMassDerivedMass
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCorrelationInfraredLogDecay
import Mathlib.Tactic

/-!
# Equality of the derived Hamiltonian mass and the physical OS infrared mass

The preceding layer extends the sharp semigroup estimate

`‖T_t ψ‖ ≤ ‖ψ‖ * exp (-physicalYangMillsMass * t)`

to every vacuum-orthogonal vector in the completed physical Hilbert space.
For an inner-symmetric physical semigroup, the OS autocorrelation at even time
is exactly the squared norm at half time.  Hence

`C_ψ(2t) = ‖T_t ψ‖² ≤ ‖ψ‖² exp (-2 physicalYangMillsMass t)`.

Passing this estimate through `Real.log` gives, at every positive Euclidean
time, the lower bound

`physicalYangMillsMass ≤ normalizedLogDecayFromZero ψ t`.

The already constructed long-time limit therefore yields

`physicalYangMillsMass ≤ m_IR(ψ)`

for every nonzero vacuum-orthogonal physical state.  Taking the infimum over the
physical excitation sector gives the reverse comparison to the already merged

`physicalYangMillsOSInfraredMass ≤ physicalYangMillsMass`,

and therefore identifies the two variational masses exactly.

No spectral theorem, PVM hypothesis, spectral-attainment assumption,
functional-calculus identity `T_t = exp (-t H)`, numerical mass value, or new
physical axiom is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology Real
open scoped InnerProductSpace NNReal

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Full-sector semigroup norm decay gives the corresponding exponential upper
bound on the physical OS autocorrelation at even Euclidean time. -/
theorem physicalCorrelation_add_self_le_exp_neg_physicalYangMillsMass_sq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (psi : P.PhysicalHilbert)
    (horthogonal : inner ℝ psi P.vacuum = 0) :
    T.physicalCorrelation psi (t + t) ≤
      (‖psi‖ * Real.exp ((-T.physicalYangMillsMass) * (t : ℝ))) ^ 2 := by
  rw [T.physicalCorrelation_add_self_eq_norm_sq hSymmetric]
  have hnorm :=
    T.physicalOperator_norm_le_exp_neg_physicalYangMillsMass_of_inner_vacuum_eq_zero
      hP t psi horthogonal
  have hleft :
      0 ≤ ‖T.toPhysicalSemigroup.operator t psi‖ := norm_nonneg _
  have hright :
      0 ≤ ‖psi‖ * Real.exp ((-T.physicalYangMillsMass) * (t : ℝ)) :=
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  nlinarith

/-- The full-sector exponential autocorrelation envelope passes monotonically
through the physical OS logarithm. -/
theorem physicalCorrelationRealClampLog_add_self_le_log_exp_decayEnvelope
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) {psi : P.PhysicalHilbert}
    (horthogonal : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) :
    T.physicalCorrelationRealClampLog psi (((t + t : NNReal) : ℝ)) ≤
      Real.log
        ((‖psi‖ * Real.exp ((-T.physicalYangMillsMass) * (t : ℝ))) ^ 2) := by
  unfold physicalCorrelationRealClampLog
  rw [T.physicalCorrelationRealClamp_coe]
  exact
    Real.log_le_log
      (T.physicalCorrelation_pos_of_ne_zero hSymmetric (t + t) hpsi_ne)
      (T.physicalCorrelation_add_self_le_exp_neg_physicalYangMillsMass_sq
        hP hSymmetric t psi horthogonal)

/-- The logarithmic loss of the sharp exponential envelope, divided by the
even Euclidean time, is exactly the derived physical Yang--Mills mass. -/
theorem log_exp_decayEnvelope_div_add_self_time_eq_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (t : NNReal) {psi : P.PhysicalHilbert}
    (hpsi_ne : psi ≠ 0) (ht : 0 < t) :
    (T.physicalCorrelationRealClampLog psi 0 -
        Real.log
          ((‖psi‖ *
              Real.exp ((-T.physicalYangMillsMass) * (t : ℝ))) ^ 2)) /
        (((t + t : NNReal) : ℝ)) =
      T.physicalYangMillsMass := by
  have hnorm_pos : 0 < ‖psi‖ := norm_pos_iff.mpr hpsi_ne
  have hnorm_ne : ‖psi‖ ≠ 0 := ne_of_gt hnorm_pos
  have ht_ne : (t : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt ht)
  have hzero :
      T.physicalCorrelationRealClampLog psi 0 =
        2 * Real.log ‖psi‖ := by
    unfold physicalCorrelationRealClampLog
    have hclamp :
        T.physicalCorrelationRealClamp psi 0 = ‖psi‖ ^ 2 := by
      simpa using T.physicalCorrelationRealClamp_coe psi (0 : NNReal)
    rw [hclamp, Real.log_pow]
    norm_num
  have henvelope :
      Real.log
          ((‖psi‖ *
              Real.exp ((-T.physicalYangMillsMass) * (t : ℝ))) ^ 2) =
        2 *
          (Real.log ‖psi‖ +
            (-T.physicalYangMillsMass) * (t : ℝ)) := by
    rw [Real.log_pow,
      Real.log_mul hnorm_ne (Real.exp_ne_zero _), Real.log_exp]
    norm_num
  have htime :
      (((t + t : NNReal) : ℝ)) = 2 * (t : ℝ) := by
    norm_num
    ring
  rw [hzero, henvelope, htime]
  field_simp [ht_ne]
  ring

/-- At every positive even Euclidean time, the derived physical Yang--Mills mass
is a lower bound for the normalized physical OS logarithmic decay. -/
theorem physicalYangMillsMass_le_normalizedLogDecayFromZero_add_self
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) {psi : P.PhysicalHilbert}
    (horthogonal : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) (ht : 0 < t) :
    T.physicalYangMillsMass ≤
      T.physicalCorrelationRealClampNormalizedLogDecayFromZero
        psi (((t + t : NNReal) : ℝ)) := by
  have hmass :=
    T.log_exp_decayEnvelope_div_add_self_time_eq_physicalYangMillsMass
      t hpsi_ne ht
  have hlog :=
    T.physicalCorrelationRealClampLog_add_self_le_log_exp_decayEnvelope
      hP hSymmetric t horthogonal hpsi_ne
  have hnum :=
    sub_le_sub_left hlog (T.physicalCorrelationRealClampLog psi 0)
  have htau : 0 < t + t := add_pos ht ht
  have htauReal : 0 < (((t + t : NNReal) : ℝ)) := by
    exact_mod_cast htau
  rw [← hmass]
  unfold physicalCorrelationRealClampNormalizedLogDecayFromZero
  simp only [div_eq_mul_inv]
  exact
    mul_le_mul_of_nonneg_right hnum
      (inv_nonneg.mpr htauReal.le)

/-- The same lower bound holds at every positive Euclidean time by writing the
time as two equal half-times. -/
theorem physicalYangMillsMass_le_normalizedLogDecayFromZero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) {psi : P.PhysicalHilbert}
    (horthogonal : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) (ht : 0 < t) :
    T.physicalYangMillsMass ≤
      T.physicalCorrelationRealClampNormalizedLogDecayFromZero psi (t : ℝ) := by
  let s : NNReal := t / 2
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have h :=
    T.physicalYangMillsMass_le_normalizedLogDecayFromZero_add_self
      hP hSymmetric s horthogonal hpsi_ne hs
  have htime : (((s + s : NNReal) : ℝ)) = (t : ℝ) := by
    norm_num [s]
  rw [htime] at h
  exact h

/-- Consequently the derived physical Yang--Mills mass lies below the actual
long-time infrared logarithmic decay exponent of every nonzero
vacuum-orthogonal physical state. -/
theorem physicalYangMillsMass_le_physicalCorrelationRealClampInfraredEffectiveMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert}
    (horthogonal : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) :
    T.physicalYangMillsMass ≤
      T.physicalCorrelationRealClampInfraredEffectiveMass psi := by
  have hlim :=
    T.physicalCorrelationRealClampNormalizedLogDecayFromZero_shift_tendsto_infrared
      hSymmetric hpsi_ne
  have hneg := hlim.neg
  have hbound :
      -T.physicalCorrelationRealClampInfraredEffectiveMass psi ≤
        -T.physicalYangMillsMass := by
    apply le_of_tendsto hneg
    filter_upwards with u
    exact neg_le_neg
      (T.physicalYangMillsMass_le_normalizedLogDecayFromZero
        hP hSymmetric (u + 1) horthogonal hpsi_ne (by positivity))
  exact neg_le_neg_iff.mp hbound

/-- Taking the variational infimum over all nonzero vacuum-orthogonal physical
states gives the reverse comparison from the graph-closed Hamiltonian mass to
the state-independent physical OS infrared mass. -/
theorem physicalYangMillsMass_le_physicalYangMillsOSInfraredMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    T.physicalYangMillsMass ≤ T.physicalYangMillsOSInfraredMass := by
  unfold physicalYangMillsOSInfraredMass
  apply le_csInf W.osInfraredMassSet_nonempty
  intro r hr
  rcases hr with ⟨psi, hpsi_ne, horthogonal, rfl⟩
  exact
    T.physicalYangMillsMass_le_physicalCorrelationRealClampInfraredEffectiveMass
      hP hSymmetric horthogonal hpsi_ne

/-- The variational mass of the graph-closed physical Yang--Mills Hamiltonian is
exactly the state-independent infrared mass extracted from physical OS
correlations. -/
theorem physicalYangMillsOSInfraredMass_eq_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    T.physicalYangMillsOSInfraredMass = T.physicalYangMillsMass := by
  exact le_antisymm
    (T.physicalYangMillsOSInfraredMass_le_physicalYangMillsMass
      hP hSymmetric W)
    (T.physicalYangMillsMass_le_physicalYangMillsOSInfraredMass
      hP hSymmetric W)

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
