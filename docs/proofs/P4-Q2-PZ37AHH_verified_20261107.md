# P4-Q2-PZ37AHH 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。`main` は文書ミラー。元Wilson作用・ZW centered physical source・kernel・floor・真正Haar測度・既存Type値証拠・公開root・固定Lean/mathlibを変更しない。

## Exact-source検証・統合

| 項目 | 確認結果 |
| --- | --- |
| [AHH定理PR #6439](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6439) | **MERGED** |
| AHG継承基点 | `44704cf1a38ae9f51e3ab78e51795ce2a2595b9a` |
| 最終exact-source HEAD | `9098e818be779e8e9588cb72ab0189badb21b8ce` |
| test-merge SHA | `f60add2ede40b8181ae51f3ee04fec4fef670055` |
| theorem squash SHA | `05d90bc00df3ad492aadd2fb00288cd620a5c4fc` |
| source/test-merge/squash共通Git tree | `dad16b6124148fbb591af2f400cd4bb45579fc31` |
| [Exact-source CI #42332257438](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42332257438) | workflow completed / **SUCCESS** |
| Changed Lean job | `128281202203` completed / SUCCESS |
| Lean依存閉包 | **11,369 / 11,369 SUCCESS** |
| 公理依存確認 | **14宣言（13定理・1座標証拠構成）**、標準3公理のみ |
| sorryAx / 変更Lean warning / error | **なし / 0 / 0** |
| 独立completion receipt | job `128282999853` completed / SUCCESS |
| 変更 | 新規Lean1件・282追加行、既存Lean変更・削除0 |

GitHub MCPで最終 `lean-fast-check-log` artifact `13557788300` を回収し、実ログ `Build completed successfully (11369 jobs).`、全14件の公理依存が `propext`・`Classical.choice`・`Quot.sound` のみであること、ログ全体のsorryAxなし、変更AHHのwarning/error 0/0を確認した。固定Leanは `v4.30.0-rc2`、mathlibは `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。別のStrict Lean/Governance workflowが実行されたとの主張はしない。

## CLOSED — 現在の元ZW sourceそのものの非零性

対象は `p4Q2PZ37ZW_originalCenteredPhysicalDirection H`。JUの別のanchored sourceへ置き換えない。AFZの連続代表と元Gauss-law物理L2 sourceの厳密な対応、およびAGNの元Haar平均の正確な値から

```text
f_H(A) = (W_H(A)-p_H)/2,
f_H(identity configuration) = -p_H/2 < 0.
```

AHGで証明済みの `p_H>0` を使い、元の連続代表 `f_H != 0` を外部仮定なしで証明した。これは連続代表の点値であり、任意に選んだL2同値類代表の点値は用いない。**sourceの恒等配置での負値を、transferの恒等右境界での負値に読み替えない。**

## CLOSED — 各有限体積における元physical transferの非零存在

既存LJの厳密正値性は、元Wilson crossing核だけでなく、左右両方の正の空間half-Boltzmann重みを含む完全one-slab核についての定理である。これを現在の元ZW sourceへAFZの証拠付き対応で接続し、すべての `H : Nat` に対して

```text
0 < integral_A integral_B K_H(A,B)*f_H(A)*f_H(B) dmu_H(B) dmu_H(A),
exists B : original Cfg_H, T_H(B) != 0
```

を証明した。source非零、transfer非零、injectivity/rankなどを新しい仮定として追加していない。

ここで得るのは各Hごとの厳密正値性であり、Hに一様な下界ではない。

## CLOSED — 明示的AHG族内の有理右境界にも非零値が存在

元AEVの一リンク弦距離評価をAGGの有限座標telescopingで合成し、同じ元transferについて

```text
C_H = 13*beta_0*originalCenteredSourceHaarL1Mass_H >= 0,
|T_H(B)-T_H(C)| <= C_H * D_sp(B,C)
```

を証明した。AHGの指定済み有理中心族により、任意のN>0について、実際の右境界を有理ラベル配置 `a : Link_H -> AHG_meshIndex N` で近似し、誤差を

```text
|T_H(B)-T_H(B_(N,a))| <= C_H * card(Link_H) * 4/N
```

で制御した。既に存在が証明された非零値の絶対値の半分より小さくする有限Nを選ぶことで

```text
exists N>96, exists a, T_H(B_(N,a)) != 0
```

を得た。すべてのリンクは元AGLの有理座標Type証拠を持つ。N=128で十分とは主張せず、Nおよびラベル配置は数値的に抽出していない。

## CLOSED — 真正有限signed-Haar符号証明書の無条件な存在

上記の元有理右境界での非零存在に、AHEの条件付き完全性を適用した。結果として、すべてのHについて、**正判定または負判定がtrueとなる元AGU/AGP有限有理Haar表が存在する**ことを、非零transferを仮定せずに証明した。

```text
exists B, exists original rational-coordinate evidence b,
exists d : original AGP_gridData H, exists m n, exists hn : 0<n,
  0 < (AGP_originalTable H d B b m n hn).lower
    OR
  (AGP_originalTable H d B b m n hn).upper < 0.
```

展開された精度証明書では、元AGU左積分格子の半径R・質量精度eps・結合近似次数m・Taylor次数nを保持する。AHFを適用し、その受理表の左積分半径が `R<p_H/24` を満たすことも同時に証明した。

**右境界を近似するAHGメッシュと、左Haar積分を認証するAGU格子は別の有限データである。** 後者がAHGの同じ格子・同じ次数であるとは主張しない。AHFのliteral original24に対する全次数棄却とも矛盾しない。

## 存在証明と評価済み証人の境界

AHG以前に未接続だった「元ZW transferが非零となる有理境界の存在」と「真正有限符号証明書の存在」は、AHHによりCLOSEDとなった。過去記録は当時の状態として保持する。

一方、以下は今回未実行・未証明である：具体的な境界ラベルとNの数値抽出、正負どちらかの枝の特定、Haar質量区間の数値計算、具体的な判定器の実行によるtrue確認、恒等右境界でのtransferの符号、二符号殻、H一様coercivity、Hamiltonian gap、連続体4D Yang–Mills質量ギャップ。

本結果は単なる条件付き同値ではないが、存在量化された証人をすべて数値として提示した結果でもない。

## 初回CIと修正

初回CI `42331700919` は `originalSource_ne_zero` の `congrArg` による関数評価式が未正規化のため、続く `rw` が対象を認識できず1件失敗した。`change fCont identity = 0 at hAt` で定義上同じ命題へ正規化してから既証明の恒等配置値を書換えるよう修正した。1行を2行へ変更しただけで、定理文・仮定・元物理定義は不変更。初回失敗に由来した下流sorryAx依存が最終ログに残っていないことを確認した。

## NEXT — AHI

次は存在量化された結果から、具体的な元右境界・符号枝・有理下界または上界を得る段階である。元Haarモーメントと相殺構造を用いた定量的評価、または実際の有限データ評価を進める。固定体積での存在を一様coercivityや連続体の結論へ昇格しない。

[AHH Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/05d90bc00df3ad492aadd2fb00288cd620a5c4fc/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNonzeroRationalSignExistenceV5_PZ37AHH.lean)。本記録は新規追加。今回はREADME・ROADMAPを更新せず旧本文と過去の正式証明記録を保持する。文書専用PRでStrict Leanは起動しない。
