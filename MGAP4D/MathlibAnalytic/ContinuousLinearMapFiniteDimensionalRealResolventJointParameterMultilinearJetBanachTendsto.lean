import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterMultilinearJetBanachCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Joint convergence of a finite resolvent family and a finite direction
family induces convergence of the complete carrier rectangle in its genuine
finite dependent-product norm topology. -/
theorem tendsto_continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily_directionFamily
    {α V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {m taylorOrder mixedOrder : ℕ} {l : Filter α}
    {R : α → Fin (taylorOrder + 1) → (V →L[ℝ] V)}
    {R0 : Fin (taylorOrder + 1) → (V →L[ℝ] V)}
    {H : α → Fin m → (V →L[ℝ] V)} {H0 : Fin m → (V →L[ℝ] V)}
    (hR : Tendsto R l (𝓝 R0)) (hH : Tendsto H l (𝓝 H0)) :
    Tendsto (fun a =>
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily
        m taylorOrder mixedOrder (H a) (R a)) l
      (𝓝 (continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily
        m taylorOrder mixedOrder H0 R0)) := by
  apply tendsto_pi_nhds.2
  intro k
  apply tendsto_pi_nhds.2
  intro n
  have hRk : Tendsto (fun a => R a k) l (𝓝 (R0 k)) :=
    (tendsto_pi_nhds.1 hR) k
  simpa only [
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily,
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent,
      Function.comp_apply] using
    ((continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent_directionFamily
      (V := V) m n.1).tendsto (R0 k, H0)).comp (hRk.prodMk hH)

/-- Joint convergence of a finite resolvent family and a finite direction
family induces convergence of every Banach-valued complete response rectangle
in the genuine finite dependent-product norm topology. -/
theorem tendsto_continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily_directionFamily
    {α V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    {m taylorOrder mixedOrder : ℕ} {l : Filter α}
    {R : α → Fin (taylorOrder + 1) → (V →L[ℝ] V)}
    {R0 : Fin (taylorOrder + 1) → (V →L[ℝ] V)}
    {H : α → Fin m → (V →L[ℝ] V)} {H0 : Fin m → (V →L[ℝ] V)}
    (hR : Tendsto R l (𝓝 R0)) (hH : Tendsto H l (𝓝 H0)) :
    Tendsto (fun a =>
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily
        φ m taylorOrder mixedOrder (H a) (R a)) l
      (𝓝 (continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily
        φ m taylorOrder mixedOrder H0 R0)) := by
  apply tendsto_pi_nhds.2
  intro k
  apply tendsto_pi_nhds.2
  intro n
  have hRk : Tendsto (fun a => R a k) l (𝓝 (R0 k)) :=
    (tendsto_pi_nhds.1 hR) k
  simpa only [
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily,
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent,
      Function.comp_apply] using
    ((continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent_directionFamily
      φ m n.1).tendsto (R0 k, H0)).comp (hRk.prodMk hH)

/-- Joint convergence of a finite resolvent family and a finite direction
family induces convergence of the complete basis-independent trace rectangle
in the genuine finite dependent-product norm topology. -/
theorem tendsto_continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily_directionFamily
    {α V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {m taylorOrder mixedOrder : ℕ} {l : Filter α}
    {R : α → Fin (taylorOrder + 1) → (V →L[ℝ] V)}
    {R0 : Fin (taylorOrder + 1) → (V →L[ℝ] V)}
    {H : α → Fin m → (V →L[ℝ] V)} {H0 : Fin m → (V →L[ℝ] V)}
    (hR : Tendsto R l (𝓝 R0)) (hH : Tendsto H l (𝓝 H0)) :
    Tendsto (fun a =>
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
        V m taylorOrder mixedOrder (H a) (R a)) l
      (𝓝 (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
        V m taylorOrder mixedOrder H0 R0)) := by
  apply tendsto_pi_nhds.2
  intro k
  apply tendsto_pi_nhds.2
  intro n
  have hRk : Tendsto (fun a => R a k) l (𝓝 (R0 k)) :=
    (tendsto_pi_nhds.1 hR) k
  simpa only [
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily,
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily,
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent,
      Function.comp_apply] using
    ((continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent_directionFamily
      (continuousLinearMapTrace (V := V)) m n.1).tendsto (R0 k, H0)).comp
        (hRk.prodMk hH)

end MathlibAnalytic
end MGAP4D
