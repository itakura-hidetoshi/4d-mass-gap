import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterMultilinearJetDirectionFamilyCore
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- The complete finite dependent joint multilinear jet inherits the canonical
finite-product CompleteSpace structure whenever its value space is complete. -/
@[implicit_reducible]
noncomputable instance continuousLinearMapJointMultilinearCarrierJetCompleteSpace
    (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (m order : ℕ) :
    CompleteSpace (ContinuousLinearMapJointMultilinearCarrierJet V W m order) :=
  inferInstance

/-- The finite Taylor-order by joint-order rectangular jet inherits the
canonical iterated finite-product CompleteSpace structure. -/
@[implicit_reducible]
noncomputable instance continuousLinearMapJointMultilinearCarrierRectangularJetCompleteSpace
    (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (m taylorOrder mixedOrder : ℕ) :
    CompleteSpace (ContinuousLinearMapJointMultilinearCarrierRectangularJet
      V W m taylorOrder mixedOrder) :=
  inferInstance

/-- The actual finite-product norm on a complete dependent jet is below a
positive threshold exactly when every multilinear component is. -/
theorem continuousLinearMapJointMultilinearCarrierJet_norm_lt_iff
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {m order : ℕ}
    (A : ContinuousLinearMapJointMultilinearCarrierJet V W m order)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ‖A‖ < epsilon ↔ ∀ n, ‖A n‖ < epsilon :=
  pi_norm_lt_iff hepsilon

/-- The norm distance of two complete dependent jets is componentwise the
maximum continuous-multilinear-map norm distance. -/
theorem continuousLinearMapJointMultilinearCarrierJet_sub_norm_lt_iff
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {m order : ℕ}
    (A B : ContinuousLinearMapJointMultilinearCarrierJet V W m order)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ‖A - B‖ < epsilon ↔ ∀ n, ‖A n - B n‖ < epsilon := by
  simpa using (pi_norm_lt_iff (x := A - B) hepsilon)

/-- The actual iterated finite-product norm on a rectangular jet is below a
positive threshold exactly when every Taylor-order/joint-order component is. -/
theorem continuousLinearMapJointMultilinearCarrierRectangularJet_norm_lt_iff
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {m taylorOrder mixedOrder : ℕ}
    (A : ContinuousLinearMapJointMultilinearCarrierRectangularJet
      V W m taylorOrder mixedOrder)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ‖A‖ < epsilon ↔ ∀ k n, ‖A k n‖ < epsilon := by
  constructor
  · intro h k n
    have hk := (pi_norm_lt_iff hepsilon).1 h k
    exact (pi_norm_lt_iff hepsilon).1 hk n
  · intro h
    apply (pi_norm_lt_iff hepsilon).2
    intro k
    apply (pi_norm_lt_iff hepsilon).2
    intro n
    exact h k n

/-- The norm distance of two rectangular jets is exactly controlled by all
Taylor-order/joint-order component distances. -/
theorem continuousLinearMapJointMultilinearCarrierRectangularJet_sub_norm_lt_iff
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {m taylorOrder mixedOrder : ℕ}
    (A B : ContinuousLinearMapJointMultilinearCarrierRectangularJet
      V W m taylorOrder mixedOrder)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ‖A - B‖ < epsilon ↔ ∀ k n, ‖A k n - B k n‖ < epsilon := by
  constructor
  · intro h k n
    have hk := (pi_norm_lt_iff hepsilon).1 h k
    have hkn := (pi_norm_lt_iff hepsilon).1 hk n
    simpa using hkn
  · intro h
    apply (pi_norm_lt_iff hepsilon).2
    intro k
    apply (pi_norm_lt_iff hepsilon).2
    intro n
    simpa using h k n

/-- The previous scalar complete-jet sup distance is equivalent, at every
positive scale, to the genuine finite-product norm distance. -/
theorem continuousLinearMapJointMultilinearCarrierJet_norm_sub_lt_iff_supDistance_lt
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {m order : ℕ}
    (A B : ContinuousLinearMapJointMultilinearCarrierJet V W m order)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ‖A - B‖ < epsilon ↔
      continuousLinearMapJointMultilinearCarrierJetSupDistance A B < epsilon := by
  rw [continuousLinearMapJointMultilinearCarrierJet_sub_norm_lt_iff A B hepsilon,
    continuousLinearMapJointMultilinearCarrierJetSupDistance_lt_iff A B epsilon]

/-- The previous rectangular scalar sup distance is equivalent, at every
positive scale, to the genuine iterated finite-product norm distance. -/
theorem continuousLinearMapJointMultilinearCarrierRectangularJet_norm_sub_lt_iff_supDistance_lt
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {m taylorOrder mixedOrder : ℕ}
    (A B : ContinuousLinearMapJointMultilinearCarrierRectangularJet
      V W m taylorOrder mixedOrder)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ‖A - B‖ < epsilon ↔
      continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance A B < epsilon := by
  rw [continuousLinearMapJointMultilinearCarrierRectangularJet_sub_norm_lt_iff
      A B hepsilon,
    continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance_lt_iff
      A B epsilon]

/-- Convergence in the complete dependent jet space is exactly componentwise
convergence of every continuous multilinear carrier. -/
theorem tendsto_continuousLinearMapJointMultilinearCarrierJet_iff
    {α V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {m order : ℕ} {l : Filter α}
    {A : α → ContinuousLinearMapJointMultilinearCarrierJet V W m order}
    {A0 : ContinuousLinearMapJointMultilinearCarrierJet V W m order} :
    Tendsto A l (𝓝 A0) ↔
      ∀ n, Tendsto (fun a => A a n) l (𝓝 (A0 n)) :=
  tendsto_pi_nhds

/-- Convergence in the rectangular jet space is exactly convergence of every
Taylor-order/joint-order multilinear component. -/
theorem tendsto_continuousLinearMapJointMultilinearCarrierRectangularJet_iff
    {α V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {m taylorOrder mixedOrder : ℕ} {l : Filter α}
    {A : α → ContinuousLinearMapJointMultilinearCarrierRectangularJet
      V W m taylorOrder mixedOrder}
    {A0 : ContinuousLinearMapJointMultilinearCarrierRectangularJet
      V W m taylorOrder mixedOrder} :
    Tendsto A l (𝓝 A0) ↔
      ∀ k n, Tendsto (fun a => A a k n) l (𝓝 (A0 k n)) := by
  constructor
  · intro h k n
    exact (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h k)) n
  · intro h
    apply tendsto_pi_nhds.2
    intro k
    apply tendsto_pi_nhds.2
    intro n
    exact h k n

private theorem continuous_resolventFamily_directionFamily_eval
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m taylorOrder : ℕ) (k : Fin (taylorOrder + 1)) :
    Continuous (fun p :
      (Fin (taylorOrder + 1) → (V →L[ℝ] V)) ×
        (Fin m → (V →L[ℝ] V)) => (p.1 k, p.2)) :=
  ((continuous_apply k).comp continuous_fst).prodMk continuous_snd

/-- The complete carrier jet is jointly continuous as a map into its genuine
finite-product normed space. -/
theorem continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierCompleteJetFromResolvent_directionFamily
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m order : ℕ) :
    Continuous (fun p :
      (V →L[ℝ] V) × (Fin m → (V →L[ℝ] V)) =>
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
        m (order + 1) p.2 p.1) :=
  continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent_directionFamily
    m (order + 1)

/-- A complete Taylor-order by joint-order carrier rectangle is jointly
continuous in its entire resolvent family and perturbation family. -/
theorem continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily_directionFamily
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m taylorOrder mixedOrder : ℕ) :
    Continuous (fun p :
      (Fin (taylorOrder + 1) → (V →L[ℝ] V)) ×
        (Fin m → (V →L[ℝ] V)) =>
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily
        m taylorOrder mixedOrder p.2 p.1) := by
  apply continuous_pi
  intro k
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily] using
    (continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent_directionFamily
      (V := V) m (mixedOrder + 1)).comp
        (continuous_resolventFamily_directionFamily_eval m taylorOrder k)

/-- A complete Taylor-order by joint-order Banach-valued response rectangle is
jointly continuous in the actual rectangular jet norm topology. -/
theorem continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily_directionFamily
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m taylorOrder mixedOrder : ℕ) :
    Continuous (fun p :
      (Fin (taylorOrder + 1) → (V →L[ℝ] V)) ×
        (Fin m → (V →L[ℝ] V)) =>
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily
        φ m taylorOrder mixedOrder p.2 p.1) := by
  apply continuous_pi
  intro k
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily] using
    (continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent_directionFamily
      φ m mixedOrder).comp
        (continuous_resolventFamily_directionFamily_eval m taylorOrder k)

/-- A complete Taylor-order by joint-order trace rectangle is jointly
continuous in the genuine finite-product Banach topology. -/
theorem continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily_directionFamily
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m taylorOrder mixedOrder : ℕ) :
    Continuous (fun p :
      (Fin (taylorOrder + 1) → (V →L[ℝ] V)) ×
        (Fin m → (V →L[ℝ] V)) =>
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
        V m taylorOrder mixedOrder p.2 p.1) := by
  apply continuous_pi
  intro k
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily] using
    (continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent_directionFamily
      V m mixedOrder).comp
        (continuous_resolventFamily_directionFamily_eval m taylorOrder k)

end MathlibAnalytic
end MGAP4D
