# P4-Q2-PZ37AIY — 元の正規化ZW物理源像の真正Haar-L²非零性

2026年11月9日 JST。正本は `itakura-hidetoshi/4d-mass-gap` の `formal/real-hilbert-uniform-coercive-strong-limit`。

[統合済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/0c3413dd7b619918fbfd9de1b51d7238f8e6c7cf/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNormalizedSourceHaarL2NonvanishingV5_PZ37AIY.lean) ／ [Lean定理PR #6569](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6569)。

本書は機械的に検査された定理の内容と実行来歴を記述する。文章自体は証明ではなく、対象の条件を拡張しない。

## 1．元の物理対象

対象は元の完全 SU(2) Wilson one-slab 作用、両端の空間halfweight、真正空間Haar確率測度、符号付きZW物理L²源 `p4Q2PZ37ZW_originalCenteredPhysicalDirection H`、元の物理transfer `P_{H,β}` と既存の物理ノルム正規化 `N_{H,β}=P_{H,β}/||P_{H,β}||` である。元のAIGの厳密負領域を保持し、Gauss-law physical submoduleのL²クラスとして出力を評価する。

記号 `Cfg_H` と `mu_H` はそれぞれ既存のH依存境界空間とその正規化Haar確率である。`f_{0,H}` は既存の真正ZW源、`u_{H,β}(B)` はAIWが定義した元の積分代表を既存物理ノルムで割った連続実数値関数、`m_H(β)` は同じノルムで割った元AIG余裕である。各有限HのHilbert空間は異なり、共通空間・極限作用素を仮定しない。

## 2．実際にLeanで証明した数学

**全有限H、β≥0**に対して元の物理Hilbertノルムについて

\[
\boxed{
\|N_{H,\beta}f_{0,H}\|_{L^2}
=\frac{\|P_{H,\beta}f_{0,H}\|_{L^2}}
{\|P_{H,\beta}\|}
\le \|f_{0,H}\|_{L^2}.
}
\]

ここで `N` は既存の作用素であり、元の物理ノルム `||P||>0` と `||N||=1` を使う。別のkernel、規格化やmeasureへ置き換えていない。

**各有限H、0<β≤c_H**、ただし (c_H=1+p_H/4)、(p_H=24(H+1)^3) とする。AITの元の全余裕負領域

\[
R_{H,\beta}
=\{B\in\mathrm{Cfg}_H:
u_{H,\beta}(B)<-m_H(\beta)\}
\]

は元のAIG領域と等しく、その真正Haar測度は `mu_H(R) ≥ 1/2`。元の証明書は `m_H(β)>0` である。

AIWのa.e.等式により `u_{H,β}` は既存正規化物理作用素 `N_{H,β} f_{0,H}` の真正Haar-L²代表である。もしL²出力が零元なら、指定された積分代表はHaar-a.e.で0。しかし `R_{H,β}` は正Haar測度を持つ厳密負領域なので、a.e.零と矛盾する。これは `MeasureTheory.measure_eq_zero_iff_ae_notMem` を用いてLean4で閉じている。

従って

\[
\boxed{
0<\|N_{H,\beta}f_{0,H}\|_{L^2}
\le\|f_{0,H}\|_{L^2},
\qquad H\in\mathbb N,\quad0<\beta\le1+\frac{p_H}{4}.
}
\]

さらに、元のAITのcutoff下界から**すべての有限H・0<β≤7**で非零が成立し、実際の体積成長cutoff `c_H` でも成立する。**固定した任意のβ>0**については、あるN以降のすべてのHで真正L²源像のノルムが正である。

## 3．ここからは導かない結論

今回の結果は**L²クラスの非零性**であって、体積一様な正の振幅下限を与えない。AIXで証明済みの元の正規化余裕証明書 `m_H(β_H)→0`（正結合window内）とも両立する。実際の振幅 `||N f0||` の体積極限が0か正か、βの許容範囲外の一様非零性、元のZW源がtop固有空間の直交補空間へ属するか、励起sector contractionからの一様gap、共通Hilbert空間上のcoercivity、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapは未認証とする。

L²出力のa.e.代表を使って示した非零性を、任意代表の全境界におけるpointwise符号と同一視しない。

## 4．新規Lean宣言（9定理）

全件の名前空間は `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`。

| 宣言のsuffix | 証明内容 |
|---|---|
| `p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_eq_ratio` | 真正物理L²ノルムの厳密正規化比 |
| `p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_le_input` | 元のZW源ノルムによる上界 |
| `p4Q2PZ37AIY_originalNormalizedPhysicalSource_ne_zero_of_regionMeasure` | 非零Haar領域からL²非零への降下 |
| `p4Q2PZ37AIY_originalNormalizedPhysicalSource_ne_zero_of_halfHaar` | 元AIT半Haar領域による非零性 |
| `p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_of_halfHaar` | L²ノルムの厳密正値 |
| `p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_le_seven` | 全有限Hの0<β≤7 |
| `p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_at_cutoff` | 元の体積成長上端での非零性 |
| `p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_eventually` | 固定β>0でのeventual非零性 |
| `p4Q2PZ37AIY_originalNormalizedPhysicalSource_norm_pos_le_source` | 同一条件で厳密正値と真正L²上界 |

新規leafは219行追加・削除0。新定理9件、追加定義0件。元の物理定義・既存証明・公開root・固定環境・workflowは変更していない。全9宣言と完全修飾名の `#print axioms` が一対一である。

## 5．固定環境・importsとLean4監査

- Lean `v4.30.0-rc2`。mathlib pinned `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。
- `autoImplicit false`、`maxHeartbeats 3900000`、`synthInstance.maxHeartbeats 1050000`。
- 新規leaf `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNormalizedSourceHaarL2NonvanishingV5_PZ37AIY.lean`。
- 直接importは既存AIX `PhysicalYangMillsWilsonSU2OriginalNormalizedMarginCouplingWindowV5_PZ37AIX` のみ。依存先のAIW正規化a.e.橋、AIT半Haar定理、AIG元の領域と余裕、既存物理作用素の署名を照合した。
- 初回source `174d093ada9c4eac2d49b427e7e85b7beb90ef8e` はLean成功（9定理・標準3公理のみ、sorryAx0、Lean error0）だが、123行の `change` が何もしないとの **変更warning1件** があった。修正source `82ee5d0811b2cf4e33a85cf9e3a166235c3a4da0` ではその1行だけを削除し、すべての宣言署名・仮定・imports・options・監査命令を保存して再認証した。

## 6．修正版Exact-sourceと定理squash自動push認証

| 項目 | 修正版Exact-source | 統合後自動push |
|---|---|---|
| GitHub Actions | [#42584457250](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42584457250) | [#42585431281](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42585431281) |
| イベント／結果 | pull_request / SUCCESS | push / SUCCESS |
| 認証SHA | `82ee5d0811b2cf4e33a85cf9e3a166235c3a4da0` | `0c3413dd7b619918fbfd9de1b51d7238f8e6c7cf` |
| 主Lean job | `129050817566` SUCCESS | `129053998212` SUCCESS |
| 独立receipt job | `129053111643` SUCCESS | `129056859208` SUCCESS |
| 依存閉包 | 11,413／11,413 SUCCESS | 11,413／11,413 SUCCESS |
| 実公理出力 | 9／9・標準3公理のみ | 9／9・標準3公理のみ |
| sorryAx / Lean error / 変更warning | 0 / 0 / 0 | 0 / 0 / 0 |
| artifact ID | `13658626716` | `13659401395` |
| artifact ZIP bytes | 133126 | 135237 |
| artifact ZIP SHA256 | `003a58c7a160e44d00fe4895307accbd3e6d59b74dd0b306701d51bb847d08ae` | `8f94bfe64b25fbc34f57b8572725013e7258272b461804ef9ea4c417cad07874` |
| artifact log bytes | 1998294 | 2005286 |
| artifact log SHA256 | `727d5d52726a6f32783152cdda0f8d4316df9303570ee1572044d98657222c12` | `d0a45af5b6eeb0cad577dbd5ea428b4bb16f78e94e48a7a9ab85d60a5ece6810` |

主jobの実ログとartifact ZIPの実bytesを別々に照合し、固定mathlib・Lean検証step・公理全9件・sorryAx・Lean error・変更warningを監査した。artifactのZIP SHA256はGitHub digestと一致。既存依存warning624行と新規warning0行を区別する。独立receiptは別Lean kernelでの再証明を意味しない。

```text
[mcp-receipt] event=pull_request exact_sha=82ee5d0811b2cf4e33a85cf9e3a166235c3a4da0 source_result=success run=42584457250 attempt=1
[mcp-receipt] event=push exact_sha=0c3413dd7b619918fbfd9de1b51d7238f8e6c7cf source_result=success run=42585431281 attempt=1
```

## 7．Git source／test-merge／squashの来歴

| 対象 | SHA |
|---|---|
| 開始formal HEAD | `bf2762587b1d7344d2f7a789637f0b99a224daad` |
| 初回warning付きsource | `174d093ada9c4eac2d49b427e7e85b7beb90ef8e` |
| 修正版認証source | `82ee5d0811b2cf4e33a85cf9e3a166235c3a4da0` |
| 実test-merge | `497000b8d8171c0c82389d917926bfe397822751` |
| 定理squash | `0c3413dd7b619918fbfd9de1b51d7238f8e6c7cf` |
| source/test-merge/squash共通tree | `e4420fa7158a3708eea9f87eb935ee8100623ab0` |
| 新規Lean blob | `4a9574764694ac78fb99f6e8c3585d9a5502675e` |

本件は独立Leanファイル1件追加だけの変更。squashの親は開始formal HEADであり、全文のbyte一致も照合済み。文書専用PRはStrict Leanを手動起動しない。

## 8．次段の研究対象

次段 AIZ の候補は、既存LJの元の完全Wilson kernel正定値性を元のGauss-law物理作用素の内積へ接続して、有限H・任意β>0の真正L²源像非零性へ広げること。また、真正L²振幅に定量的下界を与える場合には、AIG余裕証明書・元のHaar領域とLpノルムを型付きで接続する。元の源のtop固有空間直交性は未証明のまま残し、仮定として追加しない。
