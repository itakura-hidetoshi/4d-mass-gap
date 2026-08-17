import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRegularizedEffectiveMassSandwich

/-!
# Discrete regularized effective-mass sequence

Fix a positive Euclidean-time step `h`.  Sampling the regularized physical OS
secant decay rate on successive equal-width intervals defines

`M_{ε,h}(n) = m_ε(nh, nh+h)`.

The merged equal-width decay-rate sandwich immediately implies that this
sequence is nonnegative and antitone.  This isolates the remaining long-time
analysis as a purely order/topological statement about a bounded monotone real
sequence.

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

/-- Equal-width discrete sampling of the positive-regularized physical OS
effective mass. -/
def physicalCorrelationRealClampRegularizedEffectiveMassSequence
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (ε h : ℝ) (n : ℕ) : ℝ :=
  T.physicalCorrelationRealClampRegularizedEffectiveMass
    psi ε ((n : ℝ) * h) ((n : ℝ) * h + h)

/-- Every term of the discrete regularized effective-mass sequence is
nonnegative. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMassSequence_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε h : ℝ} (hε : 0 < ε) (hh : 0 ≤ h) (n : ℕ) :
    0 ≤ T.physicalCorrelationRealClampRegularizedEffectiveMassSequence
      psi ε h n := by
  unfold physicalCorrelationRealClampRegularizedEffectiveMassSequence
  apply T.physicalCorrelationRealClampRegularizedEffectiveMass_nonneg
    hSymmetric psi hε
  linarith

/-- One-step decrease of the discrete regularized effective-mass sequence. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMassSequence_succ_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h) (n : ℕ) :
    T.physicalCorrelationRealClampRegularizedEffectiveMassSequence
        psi ε h (n + 1) ≤
      T.physicalCorrelationRealClampRegularizedEffectiveMassSequence
        psi ε h n := by
  have hstep :=
    T.physicalCorrelationRealClampRegularizedEffectiveMass_step_antitone
      hSymmetric psi hε (s := (n : ℝ) * h) (h := h)
      (by positivity) hh
  unfold physicalCorrelationRealClampRegularizedEffectiveMassSequence
  convert hstep using 1 <;> norm_num <;> ring

/-- The discrete regularized effective-mass sequence is antitone. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMassSequence_antitone
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h) :
    Antitone
      (T.physicalCorrelationRealClampRegularizedEffectiveMassSequence psi ε h) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih =>
      exact le_trans
        (T.physicalCorrelationRealClampRegularizedEffectiveMassSequence_succ_le
          hSymmetric psi hε hh n)
        ih

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
