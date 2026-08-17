import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedMassInfraredEquality
import Mathlib.Tactic

/-!
# The physical Yang--Mills mass is the optimal uniform OS semigroup decay rate

The preceding layer identifies the variational mass of the graph-closed physical
Yang--Mills Hamiltonian with the state-independent OS infrared mass.  This file
closes the corresponding semigroup characterization.

A real number `r` is called a vacuum-orthogonal uniform exponential decay rate if

`‖T_t ψ‖ ≤ ‖ψ‖ * exp (-r t)`

for every nonnegative Euclidean time and every physical Hilbert vector orthogonal
to the vacuum.

The already merged full-sector estimate shows that `physicalYangMillsMass` is
such a rate.  Conversely, any such rate bounds every nonzero vacuum-orthogonal
OS autocorrelation by

`C_ψ(2t) ≤ ‖ψ‖² exp (-2 r t)`.

Passing this envelope through the unregularized logarithm and then through the
constructed long-time infrared limit gives `r ≤ m_IR(ψ)` for every excitation.
Taking the excitation-sector infimum and using

`physicalYangMillsOSInfraredMass = physicalYangMillsMass`

proves that no larger uniform rate exists.  Thus the physical Yang--Mills mass is
an actual greatest element, not merely a supremum, of the set of uniform
vacuum-orthogonal exponential decay rates.

No spectral theorem, PVM hypothesis, spectral-attainment assumption, numerical
mass value, functional-calculus identity `T_t = exp (-t H)`, or new physical
axiom is introduced.
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

/-- A uniform exponential norm-decay rate on the complete vacuum-orthogonal
physical Hilbert sector. -/
def PhysicalYangMillsUniformExponentialDecayRate
    (T : P.StronglyContinuousPhysicalSemigroup) (r : ℝ) : Prop :=
  ∀ (t : NNReal) (psi : P.PhysicalHilbert),
    inner ℝ psi P.vacuum = 0 →
      ‖T.toPhysicalSemigroup.operator t psi‖ ≤
        ‖psi‖ * Real.exp ((-r) * (t : ℝ))

/-- The variational physical Yang--Mills mass itself is a full-sector uniform
exponential decay rate. -/
theorem physicalYangMillsMass_uniformExponentialDecayRate
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized) :
    T.PhysicalYangMillsUniformExponentialDecayRate T.physicalYangMillsMass := by
  intro t psi horthogonal
  exact
    T.physicalOperator_norm_le_exp_neg_physicalYangMillsMass_of_inner_vacuum_eq_zero
      hP t psi horthogonal

/-- Any full-sector uniform exponential norm-decay rate gives the corresponding
squared exponential envelope for physical OS autocorrelations at even time. -/
theorem physicalCorrelation_add_self_le_exp_neg_uniformDecayRate_sq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {r : ℝ}
    (hRate : T.PhysicalYangMillsUniformExponentialDecayRate r)
    (t : NNReal) (psi : P.PhysicalHilbert)
    (horthogonal : inner ℝ psi P.vacuum = 0) :
    T.physicalCorrelation psi (t + t) ≤
      (‖psi‖ * Real.exp ((-r) * (t : ℝ))) ^ 2 := by
  rw [T.physicalCorrelation_add_self_eq_norm_sq hSymmetric]
  have hnorm := hRate t psi horthogonal
  have hleft :
      0 ≤ ‖T.toPhysicalSemigroup.operator t psi‖ := norm_nonneg _
  have hright :
      0 ≤ ‖psi‖ * Real.exp ((-r) * (t : ℝ)) :=
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  nlinarith

/-- The logarithm of the physical correlation lies below the logarithm of every
admissible uniform exponential envelope. -/
theorem physicalCorrelationRealClampLog_add_self_le_log_uniformDecayEnvelope
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {r : ℝ}
    (hRate : T.PhysicalYangMillsUniformExponentialDecayRate r)
    (t : NNReal) {psi : P.PhysicalHilbert}
    (horthogonal : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) :
    T.physicalCorrelationRealClampLog psi (((t + t : NNReal) : ℝ)) ≤
      Real.log ((‖psi‖ * Real.exp ((-r) * (t : ℝ))) ^ 2) := by
  unfold physicalCorrelationRealClampLog
  rw [T.physicalCorrelationRealClamp_coe]
  exact
    Real.log_le_log
      (T.physicalCorrelation_pos_of_ne_zero hSymmetric (t + t) hpsi_ne)
      (T.physicalCorrelation_add_self_le_exp_neg_uniformDecayRate_sq
        hSymmetric hRate t psi horthogonal)

/-- The normalized logarithmic loss of an exact exponential envelope with rate
`r` is exactly `r`. -/
theorem log_uniformDecayEnvelope_div_add_self_time_eq_rate
    (T : P.StronglyContinuousPhysicalSemigroup)
    (r : ℝ) (t : NNReal) {psi : P.PhysicalHilbert}
    (hpsi_ne : psi ≠ 0) (ht : 0 < t) :
    (T.physicalCorrelationRealClampLog psi 0 -
        Real.log ((‖psi‖ * Real.exp ((-r) * (t : ℝ))) ^ 2)) /
        (((t + t : NNReal) : ℝ)) = r := by
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
      Real.log ((‖psi‖ * Real.exp ((-r) * (t : ℝ))) ^ 2) =
        2 * (Real.log ‖psi‖ + (-r) * (t : ℝ)) := by
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

/-- Every admissible uniform exponential rate lies below the normalized
unregularized physical OS logarithmic decay at each positive even time. -/
theorem uniformExponentialDecayRate_le_normalizedLogDecayFromZero_add_self
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {r : ℝ}
    (hRate : T.PhysicalYangMillsUniformExponentialDecayRate r)
    (t : NNReal) {psi : P.PhysicalHilbert}
    (horthogonal : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) (ht : 0 < t) :
    r ≤ T.physicalCorrelationRealClampNormalizedLogDecayFromZero
      psi (((t + t : NNReal) : ℝ)) := by
  have hrate := T.log_uniformDecayEnvelope_div_add_self_time_eq_rate
    r t hpsi_ne ht
  have hlog :=
    T.physicalCorrelationRealClampLog_add_self_le_log_uniformDecayEnvelope
      hSymmetric hRate t horthogonal hpsi_ne
  have hnum :=
    sub_le_sub_left hlog (T.physicalCorrelationRealClampLog psi 0)
  have htau : 0 < t + t := add_pos ht ht
  have htauReal : 0 < (((t + t : NNReal) : ℝ)) := by
    exact_mod_cast htau
  rw [← hrate]
  unfold physicalCorrelationRealClampNormalizedLogDecayFromZero
  simp only [div_eq_mul_inv]
  exact
    mul_le_mul_of_nonneg_right hnum
      (inv_nonneg.mpr htauReal.le)

/-- The same bound holds at every positive Euclidean time, by using its positive
half-time in the even-time estimate. -/
theorem uniformExponentialDecayRate_le_normalizedLogDecayFromZero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {r : ℝ}
    (hRate : T.PhysicalYangMillsUniformExponentialDecayRate r)
    (t : NNReal) {psi : P.PhysicalHilbert}
    (horthogonal : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) (ht : 0 < t) :
    r ≤ T.physicalCorrelationRealClampNormalizedLogDecayFromZero psi (t : ℝ) := by
  let s : NNReal := t / 2
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have h :=
    T.uniformExponentialDecayRate_le_normalizedLogDecayFromZero_add_self
      hSymmetric hRate s horthogonal hpsi_ne hs
  have htime : (((s + s : NNReal) : ℝ)) = (t : ℝ) := by
    norm_num [s]
  rw [htime] at h
  exact h

/-- Every admissible uniform exponential decay rate lies below the actual
long-time infrared effective mass of each nonzero vacuum-orthogonal state. -/
theorem uniformExponentialDecayRate_le_physicalCorrelationRealClampInfraredEffectiveMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {r : ℝ}
    (hRate : T.PhysicalYangMillsUniformExponentialDecayRate r)
    {psi : P.PhysicalHilbert}
    (horthogonal : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) :
    r ≤ T.physicalCorrelationRealClampInfraredEffectiveMass psi := by
  have hlim :=
    T.physicalCorrelationRealClampNormalizedLogDecayFromZero_shift_tendsto_infrared
      hSymmetric hpsi_ne
  have hneg := hlim.neg
  have hbound :
      -T.physicalCorrelationRealClampInfraredEffectiveMass psi ≤ -r := by
    apply le_of_tendsto hneg
    filter_upwards with u
    exact neg_le_neg
      (T.uniformExponentialDecayRate_le_normalizedLogDecayFromZero
        hSymmetric hRate (u + 1) horthogonal hpsi_ne (by positivity))
  exact neg_le_neg_iff.mp hbound

/-- Hence every admissible full-sector uniform exponential decay rate lies below
the state-independent variational OS infrared mass. -/
theorem uniformExponentialDecayRate_le_physicalYangMillsOSInfraredMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    {r : ℝ}
    (hRate : T.PhysicalYangMillsUniformExponentialDecayRate r) :
    r ≤ T.physicalYangMillsOSInfraredMass := by
  unfold physicalYangMillsOSInfraredMass
  apply le_csInf W.osInfraredMassSet_nonempty
  intro q hq
  rcases hq with ⟨psi, hpsi_ne, horthogonal, rfl⟩
  exact
    T.uniformExponentialDecayRate_le_physicalCorrelationRealClampInfraredEffectiveMass
      hSymmetric hRate horthogonal hpsi_ne

/-- Therefore no uniform vacuum-orthogonal exponential decay rate can exceed the
variational mass of the graph-closed physical Yang--Mills Hamiltonian. -/
theorem uniformExponentialDecayRate_le_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    {r : ℝ}
    (hRate : T.PhysicalYangMillsUniformExponentialDecayRate r) :
    r ≤ T.physicalYangMillsMass := by
  rw [← T.physicalYangMillsOSInfraredMass_eq_physicalYangMillsMass
    hP hSymmetric W]
  exact T.uniformExponentialDecayRate_le_physicalYangMillsOSInfraredMass
    hSymmetric W hRate

/-- The set of all full-sector vacuum-orthogonal uniform exponential decay rates. -/
def physicalYangMillsUniformExponentialDecayRateSet
    (T : P.StronglyContinuousPhysicalSemigroup) : Set ℝ :=
  {r | T.PhysicalYangMillsUniformExponentialDecayRate r}

/-- The physical Yang--Mills mass is the greatest full-sector uniform exponential
decay rate.  In particular, the optimal rate is attained by the semigroup bound
proved from the actual graph-closed Hamiltonian variational mass. -/
theorem physicalYangMillsMass_isGreatest_uniformExponentialDecayRateSet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    IsGreatest T.physicalYangMillsUniformExponentialDecayRateSet
      T.physicalYangMillsMass := by
  constructor
  · simpa [physicalYangMillsUniformExponentialDecayRateSet] using
      T.physicalYangMillsMass_uniformExponentialDecayRate hP
  · intro r hr
    exact T.uniformExponentialDecayRate_le_physicalYangMillsMass
      hP hSymmetric W
      (by simpa [physicalYangMillsUniformExponentialDecayRateSet] using hr)

/-- After the OS infrared/variational identification, the same sharp exponential
norm decay can be written directly with the state-independent OS infrared mass. -/
theorem physicalOperator_norm_le_exp_neg_physicalYangMillsOSInfraredMass_of_inner_vacuum_eq_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (t : NNReal) (psi : P.PhysicalHilbert)
    (horthogonal : inner ℝ psi P.vacuum = 0) :
    ‖T.toPhysicalSemigroup.operator t psi‖ ≤
      ‖psi‖ * Real.exp ((-T.physicalYangMillsOSInfraredMass) * (t : ℝ)) := by
  rw [T.physicalYangMillsOSInfraredMass_eq_physicalYangMillsMass
    hP hSymmetric W]
  exact
    T.physicalOperator_norm_le_exp_neg_physicalYangMillsMass_of_inner_vacuum_eq_zero
      hP t psi horthogonal

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
