# P4-Q2-PZ37AJF — 真正元ZW源の選択単位top方向と追加top残余の厳密分解

2026年11月10日 JST。唯一のLean定理正本は itakura-hidetoshi/4d-mass-gap の formal/real-hilbert-uniform-coercive-strong-limit。以下は型検査済みの定理とGitHub検証来歴の説明記録であり、文章自体を形式証明として扱わない。

[定理PR #6590](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6590) MERGED。[統合済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/31145eea77605526aec2b57a201303387ac8f2ae/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSourceSelectedTopResidualV5_PZ37AJF.lean)。

## 1．真正の物理対象と分解の意味

元のSU(2) Wilson one-slab、両端halfweight、真正product-Haar確率、符号付き中心化ZW物理源 f₀,H、Gauss-law物理Hilbert空間、既存正規化transfer N_H,β、既存の**全top固有空間** Top_H,βを変更しない。各有限H∈ℕ・β>0で、既存の選択**単位top固有ベクトル** Ω_H,β ∈ Top_H,β、‖Ω_H,β‖=1を用いる。Ωの張る直線と全top空間を同一視しない。

AJDの元源top射影 Q_H,β f₀,Hを使い、選択top方向から外れる**追加top成分**を、真正元物理Hilbert空間内で
\[
r_{H,\beta}:=Q_{H,\beta}f_{0,H}
-\langle f_{0,H},\Omega_{H,\beta}\rangle\Omega_{H,\beta}
\]
と定義した。

次をLean4で証明した。
\[
\boxed{
r_{H,\beta}\in\mathrm{Top}_{H,\beta},
\quad\langle r_{H,\beta},\Omega_{H,\beta}\rangle=0,
}
\]
\[
\boxed{
\|Q_{H,\beta}f_{0,H}\|^2
=
|\langle f_{0,H},\Omega_{H,\beta}\rangle|^2
+
\|r_{H,\beta}\|^2.
}
\]

**第二項は未評価**である。r=0やtop eigenspaceの一次元性を新しい仮定として挿入していない。選択したΩへの元源内積のみを評価しても、追加top成分を隠して全top射影を抑えたことにはならない。

## 2．真正AJA Haar-L²証明書への接続

元AJAの正証明書 C_H,β=m_H,β² Measure.real μ_H(R_H,β)>0、およびAJCの真正正準top直交成分 u⊥,H,β は不変更。

AJDの本来の残余下界を以下の**完全な二寄与**で書き直した。
\[
\boxed{
C_{H,\beta}
-|\langle f_{0,H},\Omega_{H,\beta}\rangle|^2
-\|r_{H,\beta}\|^2
\le \|u_{\perp,H,\beta}\|^2.
}
\]

従って
\[
|\langle f_{0,H},\Omega_{H,\beta}\rangle|^2
+\|r_{H,\beta}\|^2<C_{H,\beta}
\]
が**独立に証明された場合のみ** u⊥,H,β ≠ 0 が従う。いずれの寄与も今回数値的に上から抑えていない。

逆に、既存選択Ωの内積二乗だけで C_H,β 以上なら、必要な**全top小条件**は成り立たないことを形式証明。この否定は、小top条件の不成立であって、励起成分がゼロであるとの結論ではない。

## 3．新規11宣言と構造

独立Lean leaf MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSourceSelectedTopResidualV5_PZ37AJF.lean を264行追加・既存Lean削除0。一般実Hilbert補題3、真正元物理対象について追加top定義1・定理7の計11宣言を実 #print axioms で監査した。

| 宣言suffix | 内容 |
| --- | --- |
| realHilbert_unitDirection_norm_sq_split | 既存単位ベクトル方向の一般Pythagoras |
| realHilbert_starProjection_unitDirection_norm_sq_split | 閉部分空間射影と選択単位ベクトルの二乗分解 |
| realHilbert_starProjection_unitDirection_residual_inner_zero | 選択単位方向への残余内積はゼロ |
| p4Q2PZ37AJF_originalSourceExtraTopComponent | 真正元ZW源の追加top残余定義 |
| p4Q2PZ37AJF_originalSourceExtraTop_mem | 追加残余は既存全topに属する |
| p4Q2PZ37AJF_originalSourceExtraTop_inner_selected_eq_zero | 追加残余と選択Ωとの直交 |
| p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra | 元源top射影ノルム二乗の選択+追加分解 |
| p4Q2PZ37AJF_originalOrthogonal_norm_sq_ge_certificate_sub_selected_extra | 真正Haar証明書から双方を控除した残余下界 |
| p4Q2PZ37AJF_originalOrthogonal_ne_zero_of_selected_extra_budget | 双方の上界が十分小さいときのみ直交非零 |
| p4Q2PZ37AJF_selected_overlap_sq_lt_certificate_of_fullTop_small | 全top小条件から選択Ω内積の必要小条件 |
| p4Q2PZ37AJF_no_fullTop_small_of_selected_overlap_large | 選択Ω内積が大きい場合の全top小条件の不可能性 |

元の物理作用素・源・Haar測度・top部分空間・仮定・Lean/mathlib pin・公開root/workflowは不変更。

## 4．Exact-source・統合後push・Gitの検証来歴

| 項目 | 認証済みの結果 |
| --- | --- |
| [Exact-source CI #42686668837](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42686668837) | pull_request／SUCCESS、独立receipt SUCCESS |
| [統合後push CI #42687789720](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42687789720) | push／SUCCESS、独立receipt SUCCESS |
| 認証source HEAD | 144ee091cf8821c417d0b54f73ee325d852f6c11 |
| 定理squash HEAD | 31145eea77605526aec2b57a201303387ac8f2ae |
| source／test-merge／squash同一Git tree | 49b452ae6e86781a43df75e5e0eb928b34c6a99f |
| Lean依存閉包 | 11,420／11,420 SUCCESS（両runの実ログ） |
| 新規11宣言の公理監査 | 11／11、propext・Classical.choice・Quot.sound のみ |
| 新規sorryAx | なし |
| 変更Lean warning／error | 0／0 |
| 最終Lean file blob | e62238b2f8867bcad364b3668fd6844c62b78ca8 |

二つのCIの実Lean出力において全11公理リストを確認した。独立receiptはCI完了受領であって第二のLean kernelによる再証明ではない。固定Lean v4.30.0-rc2、mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6。

## 5．未証明の二障害と次段AJG

(1) 追加top残余 r_H,β = 0 の証明、または元物理源に対するその厳密上界。(2) 元ZW源と選択Ωとの真正Wilson–Haar内積二乗のC_H,β未満の厳密上界。現行定理は上記二量の恒等式を証明するが**必要な評価値は構成していない**。

真のtop eigenspaceの単純性、元ZW源の全top直交性、無条件の励起sector非零・一様下界、全物理Hilbert coercivity、Hamiltonian spectral gap、4D連続体Yang–Mills mass gapはOPENのまま保持する。AJGでは元の対称・コンパクト・正作用素の真正top空間の多重度と、真正元Wilson–Haar内積の評価を分けて検証する。

append-only／tighten-only／overwrite-forbidden／same-root。
