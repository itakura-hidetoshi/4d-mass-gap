# P4-Q2-PZ37AJG — 真正中心化ZW源とtop真空のHaar定数偏差の厳密評価

2026年11月10日 JST。唯一のLean定理正本は itakura-hidetoshi/4d-mass-gap の formal/real-hilbert-uniform-coercive-strong-limit。本書は機械検証結果と来歴の記録であって文章自体は形式証明ではない。

[定理PR #6593](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6593) MERGED。[統合済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/76951507130749219e08c1b133eb596f633d43ca/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSourceConstantVacuumDeviationV5_PZ37AJG.lean)。

## 1．元の物理定義と新たな型付き接続

既存の完全SU(2) Wilson one-slab作用・両端halfweight・真正product-Haar確率・Gauss-law物理Hilbert空間・符号付き中心化ZW源f₀,H・既存の全top eigenspace・正規化物理transferは不変更。各有限H∈ℕ・β>0で同じ物理Hilbert空間を用いる。

元ZW定義を展開して、元のWilson物理源W_HとHaar定数単位ベクトルc_H（‖c_H‖=1）について
\[
f_{0,H}=\frac12\left(W_H-\langle W_H,c_H\rangle c_H\right),
\qquad
\boxed{\langle f_{0,H},c_H\rangle=0}
\]
を追加仮定なしで証明した。c_Hをβ>0のtop固有ベクトルと認定してはいない。

AJFで固定済みの**選択単位top固有ベクトル**Ω_H,βおよび**追加top残余**
\[
r_{H,\beta}=Q_{H,\beta}f_{0,H}
-\langle f_{0,H},\Omega_{H,\beta}\rangle\Omega_{H,\beta}
\]
を保持したまま、
\[
\langle f_{0,H},\Omega_{H,\beta}\rangle
=
\langle f_{0,H},
\Omega_{H,\beta}-\langle\Omega_{H,\beta},c_H\rangle c_H
\rangle
\]
および
\[
\boxed{
|\langle f_{0,H},\Omega_{H,\beta}\rangle|^2
\le \|f_{0,H}\|^2\left(1-|\langle\Omega_{H,\beta},c_H\rangle|^2\right)}
\]
を形式証明した。ここでのベクトル偏差は元の**真正物理ノルム**で測る。

## 2．真正全topとAJA残余下界の接続

AJFの正確な分解
\[
\|Q_{H,\beta}f_{0,H}\|^2 =
|\langle f_{0,H},\Omega_{H,\beta}\rangle|^2+\|r_{H,\beta}\|^2
\]
から
\[
\boxed{
\|Q_{H,\beta}f_{0,H}\|^2
\le\|f_{0,H}\|^2(1-|\langle\Omega_{H,\beta},c_H\rangle|^2)+\|r_{H,\beta}\|^2
}
\]
を証明。AJA真正正Haar-L²証明書 C_H,β=m_H,β² Measure.real μ_H(R_H,β)>0 に対して、**右辺がC_H,β未満であるという別途の真の上界が与えられた場合のみ**、元正規化ZW源像の全top直交成分が非零となる条件付き定理を得た。

今回は Ω_H,β と c_H の近さ、または r_H,β の小ささの**数値的証人は構成していない**。AJGをもって無条件の励起sector非零性やH一様ギャップと読むことはできない。

## 3．Lean leaf全文・10宣言と証明境界

追加leafは MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSourceConstantVacuumDeviationV5_PZ37AJG.lean。最終255行追加・既存ファイル削除0。一般実Hilbert補題4件と真正元物理対象6定理の**計10宣言**。それぞれに実際の #print axioms を持つ。

| 宣言suffix | 形式化された内容 |
| --- | --- |
| realHilbert_centered_inner_eq_direction_deviation | 中心化源の真空偏差との内積恒等式 |
| realHilbert_centered_inner_abs_le_direction_deviation_norm | 偏差に対するCauchy–Schwarz上界 |
| realHilbert_unitDirection_deviation_norm_sq | 単位2ベクトルの偏差二乗ノルム公式 |
| realHilbert_centered_selected_overlap_sq_le_deviation | 元の偏差を用いた内積二乗上界 |
| p4Q2PZ37AJG_originalCenteredZWSource_inner_constant_eq_zero | 元ZW物理源とHaar定数単位方向の真正直交性 |
| p4Q2PZ37AJG_originalSource_selectedTop_inner_eq_constantDeviation | 元源の選択top内積を定数方向偏差で表現 |
| p4Q2PZ37AJG_originalSource_selectedTop_overlap_abs_le_constantDeviation | 真正元源と選択topの内積絶対値上界 |
| p4Q2PZ37AJG_originalSource_selectedTop_overlap_sq_le_constantDeviation | 同じ内積の二乗上界 |
| p4Q2PZ37AJG_originalFullTop_norm_sq_le_constantDeviation_add_extra | 元源全top射影の真空偏差+追加top上界 |
| p4Q2PZ37AJG_originalOrthogonal_ne_zero_of_constantDeviation_extra_budget | **条件付き**真正直交成分非零 |

既存元ZW定義・AJFの全top/追加top残余・固定mathlibの内積APIを依存元とし、物理定義・root・Lean/mathlib pin・既存Leanファイル・workflowを変更していない。

## 4．失敗したCIも保存する来歴

初回source a84bf533e01eb79e34ef7cdd8403856779a8352f の[CI #42689972569](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42689972569)はFAILURE。任意の実数内積絶対値に対する mul_nonneg/abs_nonneg の暗黙項が確定しなかったほか、スカラー倍と減法内積の rw、および add_le_add_right の辺順の不一致があった。

次のsource 7a58f10fe79c0b5d7a3379fe35271e848ef79a26 の[CI #42691058717](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42691058717)もFAILURE。局所中心化補題の inner_sub_left が、表示上は同じ見た目の対象式で rewrite パターンを照合できないことが実ログで判明した。

最終source 9975cad37f9af393fcd40905df475341c3e89247 では、具体的な W,c に対して inner_sub_left と real_inner_smul_left の**型付き証明項を明示的に構成**し、calc で同一式へ接続する方法に改めた。真の中心化とHilbert条件は不変。いずれの初回失敗も証明済みとは扱わず履歴に保持する。

## 5．Exact-source／統合後pushの最終認証

| 対象 | 結果 |
| --- | --- |
| 修正版Exact-source CI | [#42692558676](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42692558676) completed／SUCCESS |
| 統合後push CI | [#42693592821](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42693592821) completed／SUCCESS |
| 最終認証source HEAD | 9975cad37f9af393fcd40905df475341c3e89247 |
| 定理squash HEAD | 76951507130749219e08c1b133eb596f633d43ca |
| source／test-merge／squash 共通Git tree | 8bc702e4107d1af14e58d2ff9f4b080254a96068 |
| Lean依存閉包 | 11,421／11,421 SUCCESS |
| 新規宣言公理監査 | 10／10、propext／Classical.choice／Quot.sound のみ |
| 新規sorryAx | なし |
| 変更Lean warning/error | 0／0 |
| 独立completion receipt | 両run SUCCESS、pushの実ログ確認 |
| 最終Lean blob | 60e985366368bb87da48df8bd24c6903e54f46b3 |

ReceiptはCI完了の独立受領記録であって二つ目のLean kernel証明ではない。Lean v4.30.0-rc2、mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6を固定。

## 6．AJHへ残す障害

Ω_H,β とc_Hの**真正物理Hilbert偏差**の具体的なH・β依存上界、AJF由来の追加top残余の二乗ノルム上界、AJA証明書を下回る両者の合計の証明は未認証。top eigenspaceの一次元性、体積一様coercivity、Hamiltonian spectral gap、非自明4D連続体Yang–Mills mass gapも未証明。

次は、元作用素・正性・Haar恒等式に照らして両障害を別個に評価する。append-only／tighten-only／overwrite-forbidden／same-root。
