import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationUnregularizedEffectiveMass

/-!
# Discrete unregularized effective-mass sequence

Fix a positive Euclidean-time step `h` and a nonzero completed physical state.
Sampling the unregularized physical OS secant decay rate on successive equal
width intervals defines

`M_h(n) = m(nh, nh+h)`.

The merged unregularized equal-width decay-rate sandwich immediately implies
that this sequence is nonnegative and antitone.  This isolates the next
long-time problem as a purely order/topological statement about a bounded
monotone real sequence, now without fixed positive additive regularization.

No differentiability, spectral theorem, new decay estimate, or additional
physical assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Equal-width discrete sampling of the unregularized physical OS effective
mass. -/
def physicalCorrelationRealClampEffectiveMassSequence
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (h : ℝ) (n : ℕ) : ℝ :=
  T.physicalCorrelationRealClampEffectiveMass
    psi ((n : ℝ) * h) ((n : ℝ) * h + h)

/-- Every term of the discrete unregularized effective-mass sequence is
nonnegative for a nonzero physical state. -/
theorem physicalCorrelationRealClampEffectiveMassSequence_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    0 ≤ T.physicalCorrelationRealClampEffectiveMassSequence psi h n := by
  unfold physicalCorrelationRealClampEffectiveMassSequence
  apply T.physicalCorrelationRealClampEffectiveMass_nonneg
    hSymmetric hpsi
  linarith

/-- One-step decrease of the discrete unregularized effective-mass sequence. -/
theorem physicalCorrelationRealClampEffectiveMassSequence_succ_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {h : ℝ} (hh : 0 < h) (n : ℕ) :
    T.physicalCorrelationRealClampEffectiveMassSequence psi h (n + 1) ≤
      T.physicalCorrelationRealClampEffectiveMassSequence psi h n := by
  have hstep :=
    T.physicalCorrelationRealClampEffectiveMass_step_antitone
      hSymmetric hpsi (s := (n : ℝ) * h) (h := h)
      (by positivity) hh
  unfold physicalCorrelationRealClampEffectiveMassSequence
  convert hstep using 1 <;> norm_num <;> ring

/-- The discrete unregularized effective-mass sequence is antitone. -/
theorem physicalCorrelationRealClampEffectiveMassSequence_antitone
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {h : ℝ} (hh : 0 < h) :
    Antitone (T.physicalCorrelationRealClampEffectiveMassSequence psi h) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih =>
      exact le_trans
        (T.physicalCorrelationRealClampEffectiveMassSequence_succ_le
          hSymmetric hpsi hh n)
        ih

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
