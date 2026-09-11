import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSharedPlaquetteActionDecomposition

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A uniform upper bound for every oriented plaquette-energy value. -/
def FiniteOrientedLatticeWilsonSystem.UniformPlaquetteEnergyUpperBound
    (L : FiniteOrientedLatticeWilsonSystem)
    (energyBound : ℝ) : Prop :=
  ∀ g : L.Gauge, L.plaquetteEnergy g ≤ energyBound

/-- Every uniform plaquette-energy upper bound is nonnegative. -/
theorem finite_oriented_uniformPlaquetteEnergyUpperBound_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (energyBound : ℝ)
    (hEnergy : L.UniformPlaquetteEnergyUpperBound energyBound) :
    0 ≤ energyBound :=
  le_trans (L.plaquetteEnergy_nonneg default) (hEnergy default)

/-- One shared plaquette contributes at most the uniform energy upper bound to
the absolute local-action response. -/
theorem finite_oriented_sharedPlaquetteEnergyDifference_abs_le
    (L : FiniteOrientedLatticeWilsonSystem)
    (energyBound : ℝ)
    (hEnergy : L.UniformPlaquetteEnergyUpperBound energyBound)
    (A : L.Configuration)
    (target source : L.Edge)
    (u g : L.Gauge)
    (p : L.Plaquette) :
    |L.plaquetteEnergy
          (L.plaquetteHolonomy (L.replaceLink A target u) p) -
        L.plaquetteEnergy
          (L.plaquetteHolonomy
            (L.replaceLink (L.replaceLink A source g) target u) p)| ≤
      energyBound := by
  have hLeft0 :=
    L.plaquetteEnergy_nonneg
      (L.plaquetteHolonomy (L.replaceLink A target u) p)
  have hRight0 :=
    L.plaquetteEnergy_nonneg
      (L.plaquetteHolonomy
        (L.replaceLink (L.replaceLink A source g) target u) p)
  have hLeftMax :=
    hEnergy (L.plaquetteHolonomy (L.replaceLink A target u) p)
  have hRightMax :=
    hEnergy
      (L.plaquetteHolonomy
        (L.replaceLink (L.replaceLink A source g) target u) p)
  apply abs_sub_le_iff.mpr
  constructor <;> linarith

/-- The absolute target-local action response is bounded by shared multiplicity
times the uniform energy upper bound. -/
theorem finite_oriented_targetLocalAction_sub_sourceReplace_abs_le_sharedCard_mul
    (L : FiniteOrientedLatticeWilsonSystem)
    (energyBound : ℝ)
    (hEnergy : L.UniformPlaquetteEnergyUpperBound energyBound)
    (A : L.Configuration)
    (target source : L.Edge)
    (u g : L.Gauge) :
    |L.targetLocalPlaquetteAction (L.replaceLink A target u) target -
        L.targetLocalPlaquetteAction
          (L.replaceLink (L.replaceLink A source g) target u) target| ≤
      ((L.sharedPlaquettes target source).card : ℝ) * energyBound := by
  rw [finite_oriented_targetLocalAction_sub_sourceReplace_eq_sum_shared]
  calc
    |∑ p ∈ L.sharedPlaquettes target source,
        (L.plaquetteEnergy
            (L.plaquetteHolonomy (L.replaceLink A target u) p) -
          L.plaquetteEnergy
            (L.plaquetteHolonomy
              (L.replaceLink (L.replaceLink A source g) target u) p))| ≤
      ∑ p ∈ L.sharedPlaquettes target source,
        |L.plaquetteEnergy
            (L.plaquetteHolonomy (L.replaceLink A target u) p) -
          L.plaquetteEnergy
            (L.plaquetteHolonomy
              (L.replaceLink (L.replaceLink A source g) target u) p)| :=
        finite_abs_sum_le_sum_abs
          (L.sharedPlaquettes target source)
          (fun p =>
            L.plaquetteEnergy
                (L.plaquetteHolonomy (L.replaceLink A target u) p) -
              L.plaquetteEnergy
                (L.plaquetteHolonomy
                  (L.replaceLink (L.replaceLink A source g) target u) p))
    _ ≤ ∑ _p ∈ L.sharedPlaquettes target source, energyBound := by
      apply Finset.sum_le_sum
      intro p _hp
      exact finite_oriented_sharedPlaquetteEnergyDifference_abs_le
        L energyBound hEnergy A target source u g p
    _ = ((L.sharedPlaquettes target source).card : ℝ) * energyBound := by
      simp [nsmul_eq_mul]

end

end MathlibAnalytic
end MGAP4D
