# P4-Q2-PZ37AHM — 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。Lean定理の唯一の正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。Append-only／tighten-only／overwrite-forbidden／same-root。**元ZW Gauss-law centered physical source・元完全SU(2) Wilson one-slab kernel・元空間積Haar測度・ADK弦距離・AHL真正球質量・すべての過去Lean/Type値証拠**を保持する。

## Exact-source検証と統合

| 項目 | 確定値 |
| --- | --- |
| [AHM定理PR #6454](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6454) | **MERGED** |
| AHL継承canonical | `b43d9cfddfa1df94709d0357a21ab6295f84c483` |
| 最終exact-source HEAD | `1fec9accd20093f37e68e29f435abead9c5dcf83` |
| PR test-merge HEAD | `3fbf6d07974637d3c1f211db4a8ccee453d4f66a` |
| 定理squash SHA | `1cf05ffe1a4c9bef55e281a5965de0a4172e0c26` |
| 共通source/test-merge/squash Git tree | `c1f8a55e75521cfc2ad289d4f5b7118a2cb1f578` |
| [Exact-source CI #42358265298](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42358265298) | **completed / SUCCESS** |
| Changed Lean job | `128360984370` completed / SUCCESS |
| 独立MCP completion receipt | `128362153197` completed / SUCCESS |
| Lean依存閉包 | **11,374 / 11,374 SUCCESS** |
| 公理監査 | **新規12定理**、`propext`／`Classical.choice`／`Quot.sound` のみ |
| `sorryAx` | **なし** |
| 変更AHM Lean warning／error | **0／0** |
| ソース変更 | 新規Lean1ファイル、313行追加。既存Leanの変更・削除0 |

GitHub MCPから最終診断artifact `13568269679` (`lean-fast-check-log`) を回収し、`lean-fast.log` の `Build completed successfully (11374 jobs).`、全12件の `#print axioms`、`sorryAx`不在、変更AHM warning/error 0/0を照合した。source/test-merge/squash Git treeは完全一致。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` は不変更。別のStrict Lean/Governance workflow実行を主張しない。

## CLOSED — 元の全空間リンク弦距離と真のBorel符号集合

AHK/AHLの元の全空間リンク弦距離 `D_sp(B,C)=∑_{e∈Link_H} d_J(B_e,C_e)` は、元ADKの正規化SU(2)実数特徴ベクトル `J` を用い、元の連続な積位相に対して `C↦D_sp(B,C)` が連続とLean4で証明した。したがって `Ball_sp(B,R)={C:D_sp(B,C)<R}` は元の位相でOPENである。

同じ元物理量の実数符号積を `g_H(C)=f_H(C)T_H(C)` とする。AHLで証明済みの

```text
|g_H(B)-g_H(C)| <= [6*p_H+(13/512)*p_H^2] * D_sp(B,C)
```

から、**任意の実数閾値s**に対して真のsuperlevel `{C:s<g_H(C)}` は元位相でOPENである。正の有理qに限ったAHLの実際の集合 `{C:q<g_H(C)}` もOPEN、よってBorel可測。この全実数superlevel族を使い、元の `g_H` 自身の `Measurable` を `measurable_of_Ioi` で形式証明した。新しい確率分布や離散トポロジーはない。

## CLOSED — 元の符号積のHaar可積分性と真の正部分

AGNの元source半幅 `|f_H(B)|<=p_H/2` とAHJの元transfer半幅 `|T_H(B)|<=p_H/2` を同じ元配置上で乗算し、

```text
forall B, |f_H(B)*T_H(B)| <= p_H^2/4
```

を証明した。前段で証明した可測性と、元の正規化空間積Haarが有限測度であることから、真正符号積 `g_H` がHaar可積分であると示した。

さらに**別の非負関数** `g_H^+(B)=max(g_H(B),0)` を定義し、そのMeasurable性・Integrable性・Haar積分非負性を個別に形式証明した。元の符号付き相関 `∫g_H\,dμ_H` はAHKの独立な物理量として維持し、正部分へ置換しない。

## CLOSED — 明示的なHaar正部分第一モーメントの正の下界

AHLは元の真正空間積Haar上の符号整合領域について、各Hで有理 `q>0`、実半径 `R>0`、元配置中心 `B` の存在と、

```text
forall C in Ball_sp(B,R), q < f_H(C)*T_H(C),
kappa(R/(card(Link_H)+1))^card(Link_H)
  <= Measure.real muH {C: q < f_H(C)*T_H(C)}
```

を既に証明している。AHMはこれを新しく証明したBorel性・可積分性に接続し、元の正部分積分に対して積分単調性と `setIntegral_le_integral` を適用した。

\[
\boxed{
\begin{gathered}
\forall H,\quad\exists q\in\mathbb Q_{>0},\ B\in\mathrm{Cfg}_H,\ R>0,\\
\forall C\in\mathrm{Ball}_{sp}(B,R),\quad q<f_H(C)T_H(C),\\
0<
q\,\kappa\left(\frac{R}{p_H+1}\right)^{p_H}
\le\int_{\mathrm{Cfg}_H}
\max\{f_H(C)T_H(C),0\}\,d\mu_H(C).
\end{gathered}
}
\]

これが今回の主結果。元の参照Haar物理空間、元完全Wilson核、元centered ZW sourceだけで得た、**非負の第一Haarモーメントに対する明示的な真の下界**である。指数は元の空間リンク数 `p_H` で、無関係な二境界pair-Haarの `2*p_H` ではない。元の正負符号が相殺するsigned integralから「負部を消した数値」を捏造せず、正部分の積分として明確に定義している。

## CI初回失敗と理由・修正

- 初回source `78331602b8289b97633e0a68cc38ea3dff880b5c` のCI `42357018893`：元 `p_H/2` の非負性を局所notationだけから `positivity` が展開できなかった。元plaquette個数の定義を明示して `hpHalf:0<=p_H/2` を証明し、積の上界へ渡した。この未完了定理由来の下流sorryAxは修正で消失した。
- 次source `2e2b9b11e8d9583dd69e5a7a2c453521659dd049` のCI `42357471224`：Lean 11,374 SUCCESS、新規12定理標準公理のみ・sorryAxなし。ただし定理文で存在量化した元中心Bが未使用という警告があった。**球内安定性の型付き証拠を定理文へ残す**ようにtightenし、追加した証拠の取り出し順序を下流系で更新して解決。
- 最終source `1fec9accd20093f37e68e29f435abead9c5dcf83` のCI `42358265298`：**11,374/11,374、warning/error 0/0、12定理全標準公理のみ、sorryAxなし、独立receipt SUCCESS**。

すべての修正は新規AHMファイル内のみ。元物理量、仮定、固定Lean/mathlib、過去の定理本文と証拠履歴は変更していない。

## OPEN / NEXT — AHN

AHL→AHMで、正の元Wilson作用–transfer整合域の真の空間Haar測度下界から、真の正部分第一モーメントの正の下界への接続がCLOSEDになった。

**依然未実施**：具体的な元有理境界ラベル・符号枝・q,Rの数値評価、元AGPのHaarセル質量の数値区間、実際にtrueと評価されたcheckerの実行ログ、正負二符号殻、体積一様Haar質量・coercivity、Hamiltonian gap、連続体4D Yang–Mills mass gap。QとRは存在量化であり数値証明書ではない。

次AHNは元Wilson kernelの低次Haarモーメントから作用–transfer相関の有理な**計算可能下界**が得られるかを検討し、非零定理・正部分定理から実際のsign branchと有限表の実行可能な証人抽出へ進む。正部分を元のsigned correlationへ無条件同一視しない。

[AHM Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1cf05ffe1a4c9bef55e281a5965de0a4172e0c26/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalBorelPositivePartHaarMomentV5_PZ37AHM.lean)。正式記録は新規Markdownファイルのみ追加。旧README/ROADMAP・全過去定理と履歴は保持する。docs-onlyのためStrict Leanは起動しない。
