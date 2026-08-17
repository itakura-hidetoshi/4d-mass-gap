import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCorrelationInitialLogDecayRayleigh
import Mathlib.Tactic

/-!
# Finite-time OS effective mass bounded by the Hamiltonian Rayleigh rate

For a nonzero physical state in the canonical right-generator domain, the
merged initial endpoint theorem gives

`m_eff(0,t) -> <H_right psi, psi> / ||psi||^2`

as positive Euclidean time tends to zero.  Convexity of the unregularized
logarithmic OS correlation makes the fixed-left-endpoint secant decay rate
antitone in its right endpoint.  Passing that order relation to the initial
limit therefore gives the finite-time bound

`m_eff(0,t) <= <H_right psi, psi> / ||psi||^2`.

A second application of Mathlib's convex secant monotonicity moves the left
endpoint from zero to any later nonnegative time, yielding

`0 <= m_eff(s,t) <= <H_right psi, psi> / ||psi||^2`

for `0 <= s < t`.

No spectral theorem, PVM construction, self-adjointness hypothesis, decay
estimate, or additional physical assumption is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- With left endpoint fixed at zero, the unregularized effective mass is
antitone in the positive right endpoint.  This is exactly the negative of
`ConvexOn.secant_mono` from Mathlib. -/
theorem physicalCorrelationRealClampEffectiveMass_zero_antitone
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    T.physicalCorrelationRealClampEffectiveMass psi 0 t ≤
      T.physicalCorrelationRealClampEffectiveMass psi 0 s := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hsec :=
    (T.physicalCorrelationRealClampLog_convexOn_Ici hSymmetric hpsi).secant_mono
      (show (0 : ℝ) ∈ Ici 0 by simp)
      (show s ∈ Ici (0 : ℝ) by exact hs.le)
      (show t ∈ Ici (0 : ℝ) by exact ht.le)
      hs.ne'
      ht.ne'
      hst
  unfold physicalCorrelationRealClampEffectiveMass
  unfold MGAP4D.secantDecayRate
  calc
    (T.physicalCorrelationRealClampLog psi 0 -
        T.physicalCorrelationRealClampLog psi t) / (t - 0) =
        -((T.physicalCorrelationRealClampLog psi t -
            T.physicalCorrelationRealClampLog psi 0) / (t - 0)) := by ring
    _ ≤ -((T.physicalCorrelationRealClampLog psi s -
            T.physicalCorrelationRealClampLog psi 0) / (s - 0)) :=
      neg_le_neg hsec
    _ = (T.physicalCorrelationRealClampLog psi 0 -
          T.physicalCorrelationRealClampLog psi s) / (s - 0) := by ring

/-- Every positive zero-based unregularized effective-mass secant is bounded
above by the canonical right-Hamiltonian Rayleigh quotient. -/
theorem physicalCorrelationRealClampEffectiveMass_zero_le_rightHamiltonian_rayleigh
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : T.rightGeneratorDomain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (t : NNReal) (ht : 0 < t) :
    T.physicalCorrelationRealClampEffectiveMass
        (psi : P.PhysicalHilbert) 0 (t : ℝ) ≤
      ⟪T.rightHamiltonian psi,
          (psi : P.PhysicalHilbert)⟫_ℝ /
        ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
  have hlim :=
    T.physicalCorrelationRealClampEffectiveMass_zero_tendsto_rightHamiltonian_rayleigh
      hSymmetric psi hpsi
  have hpos :
      ∀ᶠ s : NNReal in nhdsWithin (0 : NNReal) (Ioi 0), 0 < s :=
    self_mem_nhdsWithin
  have hsmall :
      ∀ᶠ s : NNReal in nhdsWithin (0 : NNReal) (Ioi 0), s ≤ t := by
    have hid :
        Tendsto (fun s : NNReal => s)
          (nhdsWithin (0 : NNReal) (Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left inf_le_left
    exact hid.eventually_le_const ht
  apply ge_of_tendsto hlim
  filter_upwards [hpos, hsmall] with s hs hst
  exact
    T.physicalCorrelationRealClampEffectiveMass_zero_antitone
      hSymmetric hpsi (by exact_mod_cast hs) (by exact_mod_cast hst)

/-- Any ordered positive-time unregularized effective mass lies below the
Hamiltonian Rayleigh quotient.  The lower bound is the already merged
nonnegativity theorem. -/
theorem physicalCorrelationRealClampEffectiveMass_interval_rayleigh_sandwich
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : T.rightGeneratorDomain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    0 ≤ T.physicalCorrelationRealClampEffectiveMass
          (psi : P.PhysicalHilbert) s t ∧
      T.physicalCorrelationRealClampEffectiveMass
          (psi : P.PhysicalHilbert) s t ≤
        ⟪T.rightHamiltonian psi,
            (psi : P.PhysicalHilbert)⟫_ℝ /
          ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
  constructor
  · exact T.physicalCorrelationRealClampEffectiveMass_nonneg
      hSymmetric hpsi hst.le
  · have ht : 0 < t := lt_of_le_of_lt hs hst
    let tn : NNReal := ⟨t, ht.le⟩
    have hzero :
        T.physicalCorrelationRealClampEffectiveMass
            (psi : P.PhysicalHilbert) 0 t ≤
          ⟪T.rightHamiltonian psi,
              (psi : P.PhysicalHilbert)⟫_ℝ /
            ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
      have htn : 0 < tn := by
        exact_mod_cast ht
      simpa [tn] using
        T.physicalCorrelationRealClampEffectiveMass_zero_le_rightHamiltonian_rayleigh
          hSymmetric psi hpsi tn htn
    by_cases hs0 : s = 0
    · simpa [hs0] using hzero
    · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      have hsec :=
        (T.physicalCorrelationRealClampLog_convexOn_Ici hSymmetric hpsi).secant_mono_aux3
          (show (0 : ℝ) ∈ Ici 0 by simp)
          (show t ∈ Ici (0 : ℝ) by exact ht.le)
          hspos
          hst
      have hinterval :
          T.physicalCorrelationRealClampEffectiveMass
              (psi : P.PhysicalHilbert) s t ≤
            T.physicalCorrelationRealClampEffectiveMass
              (psi : P.PhysicalHilbert) 0 t := by
        unfold physicalCorrelationRealClampEffectiveMass
        unfold MGAP4D.secantDecayRate
        calc
          (T.physicalCorrelationRealClampLog (psi : P.PhysicalHilbert) s -
              T.physicalCorrelationRealClampLog (psi : P.PhysicalHilbert) t) /
              (t - s) =
              -((T.physicalCorrelationRealClampLog (psi : P.PhysicalHilbert) t -
                  T.physicalCorrelationRealClampLog (psi : P.PhysicalHilbert) s) /
                (t - s)) := by ring
          _ ≤ -((T.physicalCorrelationRealClampLog (psi : P.PhysicalHilbert) t -
                  T.physicalCorrelationRealClampLog (psi : P.PhysicalHilbert) 0) /
                (t - 0)) := neg_le_neg hsec
          _ = (T.physicalCorrelationRealClampLog (psi : P.PhysicalHilbert) 0 -
                T.physicalCorrelationRealClampLog (psi : P.PhysicalHilbert) t) /
                (t - 0) := by ring
      exact hinterval.trans hzero

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
