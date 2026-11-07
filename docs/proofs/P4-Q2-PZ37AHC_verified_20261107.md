# P4-Q2-PZ37AHC 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。`main` は文書ミラーで、両分岐の旧履歴は同一視・上書きしない。

## Exact-source Lean検証・正本

| 項目 | 検証結果 |
| --- | --- |
| 定理PR | [#6424](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6424) **MERGED** |
| 検証source HEAD | `11336a72813797c47f363f5b3a605423981b0be1` |
| test-merge SHA | `106b35d9a2ce06a6ad28d9dfffcde76121e58d55` |
| 定理squash SHA | `afe1e0e47ed243e2d2ef5b7aa292a574a4b539db` |
| source/test-merge/squash共通Git tree | `9da2c909a00d06d6876dc11229b30c376fcff777` |
| [Exact-source CI #42316089429](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42316089429) | workflow completed / **SUCCESS** |
| Changed Lean job `128228912854` | completed / SUCCESS |
| 依存閉包 | **11,364 / 11,364 SUCCESS** |
| 新規定理公理監査 | **11宣言、`propext`・`Classical.choice`・`Quot.sound` のみ** |
| sorryAx / 変更Lean warning / error | **なし / 0 / 0** |
| 独立completion receipt job `128230712114` | completed / SUCCESS |
| 差分 | **新規Leanファイル1件のみ・既存Lean変更なし・削除0** |

GitHub MCPの `lean-fast-check-log` artifactを回収・解析し、最終ビルド `Build completed successfully (11364 jobs).` と新規11宣言の `#print axioms`、変更ファイルwarning/error 0/0を独立照合。旧依存Leanファイルの非fatal linter warningは新規ファイルのwarningと区別する。Lean `v4.30.0-rc2`／固定mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` は従来通り。別のStrict Lean／Governance workflowを実行したとは主張しない。

## CLOSED — 真正元AGV/AGN係数の次数非依存上界

元signed transferのAGY既証明誤差評価を変更せず、

\[
\operatorname{width}(I_H)\le
\frac{p_H}{2}\left(\Delta K_{\max}+\frac{\Delta F}{2}\right)
+2L_H(m)R+2M_H(m,n)\varepsilon
\]

を出発点とする。`p_H=AGN_countRational H` は元空間plaquetteの正確な個数。AGVの元rational slopeは

\[
L_H(m)=6+13\beta_m^{\mathrm{upper}}\frac{p_H}{2}.
\]

AHBで既証明の `0≤AGK_upper(m)≤1` から

\[
\boxed{L_H(m)\le\bar L_H:=6+\frac{13p_H}{2}}
\]

をLean4で形式証明。AGNの元global signed-transfer半径は既証明 `AGN_transferRadius_le_quarterCount` より

\[
\boxed{M_H(m,n)\le\bar M_H:=\frac{p_H}{4}}.
\]

`p_H`、`barL_H`、`barM_H` は非負の真正物理上界で、`m,n` や右境界の選び方から独立する。元source、Haar、kernel、floor、transferの再定義は行わない。

## CLOSED — 一つの有理meshによる4種類の誤差の分配

正有理目標幅 `η>0` に対し、物理係数から

\[
C_H=p_H+2\bar L_H+2\bar M_H+1>0,\qquad
\boxed{q_H(\eta)=\frac{\eta}{4C_H}>0}
\]

を構成し、`C_H q_H(η)=η/4` もLean4で証明した。符号付きの元AGV/AGN誤差計算には有理Haar質量下端の非負性を追加仮定せず、元Haarの真の質量和1・AGIのsigned min/maxを保持する。

全ての実際のkernel/floor誤差およびAGU精度予算が

\[
\Delta K_{\max}\le q,\quad \Delta F\le q,\quad
0<R\le q,\quad 0<\varepsilon\le q
\]

を満たすとき、Lean4の新しい有理不等式 `threeErrorBudget_le` とAGY既証明評価から

\[
\boxed{
\operatorname{width}(I_H)
\le\left(p_H+2\bar L_H+2\bar M_H\right)q
}
\]

を示した。有限セル数による粗い増幅因子を新たに導入しない。

## CLOSED — 元signed-transferの固定体積任意精度

AHBの最終定理 `exists_originalKernelFloor_precision` は、固定H・任意正有理qに対し、真正AGU精度格子・右境界から独立な共通次数 `m,n` を与え、

\[
\Delta K_{\max}(H,d,B,m,n)<q,\qquad
\Delta F(H,m,n)<q.
\]

これを `q=q_H(η)` で呼び出し、元AGUの選択 `R=eps=q` と同時に使用。したがって、右境界を選ぶ前に精度パラメータを選び、

\[
\boxed{
\begin{aligned}
&\forall H,\ \forall\eta\in\mathbb Q_{>0},\
\exists R,\varepsilon\in\mathbb Q_{>0},\ m,n\in\mathbb N,\ n>0,\\
&\quad \forall B\text{（元AGL有理座標証拠付き）},\\
&\qquad \operatorname{width}\!\left(
p4Q2PZ37AGU\_fineOriginalTransferInterval
(H,R,\varepsilon,B,m,n)\right)<\eta .
\end{aligned}}
\]

をLean4形式証明した。区間は`p4Q2PZ37AFV_verifiedInterval`であり、元の物理的signed-transfer値を証明付きで含む。有限体積ごとのパラメータ依存性と、元AGU Borel格子の古典的・非計算的選択はそのまま保持する。数値的な大体積テーブルを作成・実行したという主張ではない。

数式上は実際に

\[
\operatorname{width}(I_H)
\le(C_H-1)q_H(\eta)
\le C_Hq_H(\eta)=\eta/4<\eta
\]

まで示している。

## CI全文点検と最小修正

初回CI #42315506537 の唯一の変更Leanエラーは、`field_simp`で有理分母の整理・証明が完了した直後に置かれた`ring`が `No goals to be solved` を出したこと。これは数学的評価の欠陥ではなく、Lean4 tactic sequenceの到達性の問題。AHC全文・既存AGY/AGV/AHB依存定義・固定mathlibの証明項を確認し、`ring` 1行のみ削除した。最終検証source HEAD `11336a72813797c47f363f5b3a605423981b0be1` のCI #42316089429 で全宣言の証明・標準公理依存・変更warning/error0/0が成功した。

## OPEN — AHD以降の物理的障害

AHCが証明するのは**固定HかつAGL有理座標証拠付き右境界に対する、同一元signed-transfer値の有理認証区間幅の任意精度**である。任意の非有理実右境界の証拠、有限の具体的大体積Haar表、真正transferの正または負の**非零符号を与える構成的証人**は、ここから自動的には得られない。まして元transferのtwo-threshold shell、H一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills mass gapは未証明である。

**NEXT — AHD:** 元signed-transferを区間評価したまま、非零符号を得るにはどの構成的な物理的符号証拠・有限評価がなお必要かを形式的に特定する。区間を任意に狭くできることと、中心値が0でないことを区別する。元物理model・元Type値証明履歴・root・pinを変更しない。

[AHC Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/afe1e0e47ed243e2d2ef5b7aa292a574a4b539db/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSignedTransferArbitraryWidthV5_PZ37AHC.lean)。
