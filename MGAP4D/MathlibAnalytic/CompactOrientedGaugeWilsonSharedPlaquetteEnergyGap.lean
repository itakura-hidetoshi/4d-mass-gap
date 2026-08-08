import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonPlaquetteEnergyDifference

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Absolute value of a finite real sum is bounded by the sum of absolute
values, kept local to the compact Wilson spine. -/
theorem compact_abs_sum_le_sum_abs
    {α : Type*}
    (s : Finset α)
    (u : α → ℝ) :
    |Finset.sum s u| ≤ Finset.sum s (fun a => |u a|) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (abs_add_le _ _) (add_le_add (le_refl _) ih)

theorem compact_oriented_targetLocalAction_sub_sourceReplace_abs_le_sharedCard_mul
    (L : CompactOrientedGaugeWilsonSystem)
    (energyBound : ℝ)
    (hUpper : ∀ U : L.Gauge, L.plaquetteEnergy U ≤ energyBound)
    (A : L.Configuration)
    (target source : L.geometry.Edge)
    (u g : L.Gauge) :
    |L.targetLocalPlaquetteAction (L.replaceLink A target u) target -
        L.targetLocalPlaquetteAction
          (L.replaceLink (L.replaceLink A source g) target u) target| ≤
      ((L.sharedPlaquettes target source).card : ℝ) * energyBound := by
  rw [compact_oriented_targetLocalAction_sub_sourceReplace_eq_sum_shared]
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
        compact_abs_sum_le_sum_abs
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
      exact compact_oriented_sharedPlaquetteEnergyDifference_abs_le
        L energyBound hUpper A target source u g p
    _ = ((L.sharedPlaquettes target source).card : ℝ) * energyBound := by
      simp [nsmul_eq_mul]

end
end MathlibAnalytic
end MGAP4D
