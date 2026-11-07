# P4-Q2-PZ37AHJ — 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。定理の唯一の正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。append-only / tighten-only / overwrite-forbidden / same-root。既存Lean・Wilson物理定義・元ZW source・核・床関数・真正Haar測度・AGP/AGU/AGL履歴は変更しない。

## 完了したLean4検証・統合

| 項目 | 検証結果 |
| --- | --- |
| [定理PR #6445](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6445) | **MERGED** |
| 継承元AHI正本 | `d51e75d4a266f4580ae16e327eb01ccff89ff6c1` |
| 最終exact-source HEAD | `5a1c24c6eb3cd50e577628768494d859e586a47d` |
| test-merge HEAD | `5d49e20a032cfef6b79471cd567628bd510190c5` |
| squash HEAD | `2c3e4bedee902073808691ceb28b0c4d35188efa` |
| 共通 source/test-merge/squash Git tree | `0d408e81b17f07dd7e0753d61361f34c7469f47e` |
| [Exact-source CI #42339879243](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42339879243) | **completed / SUCCESS** |
| Changed Lean job | `128305007837` completed / SUCCESS |
| 独立completion receipt | `128306481556` completed / SUCCESS |
| Lean依存閉包 | **11,371 / 11,371 SUCCESS** |
| 新規定理公理監査 | 9定理、`propext` / `Classical.choice` / `Quot.sound` のみ |
| `sorryAx` / 変更Lean warning / error | **なし / 0 / 0** |
| 変更 | 新規Leanファイル1件・311追加行、既存Lean変更なし |

GitHub MCPで最終 `lean-fast-check-log` artifact `13560823040` を直接回収し、実ログの `Build completed successfully (11371 jobs).`、AHJの9定理に対する `#print axioms`、`sorryAx` 0件、変更Leanの警告・エラー0を確かめた。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。独立Strict Lean / Governance workflowをこのdocs-only更新で実行したとは主張しない。

## CLOSED — 同じZW sourceの真正Haar半幅評価

元AGNにある連続代表の厳密な点wise評価
`|fCont_H(A)| <= p_H/2`
を使用した。AFZの真正Gauss-law L2 sourceと連続代表との型付き同一性を使い、L2同値類の任意代表をpointwise同一視することなく、元空間Haar測度に関するほとんど至る所の上界を証明した。元Haar測度が確率測度であることから、

```text
Msrc_H = integral_A |(f0_H : Lp R 2 muH) A| dmuH <= p_H/2
```

をLean4で証明した。AFZの従来上界 `Msrc_H <= p_H` を tighten-only で改善し、元のsourceやHaar lawは変更しない。

元の完全one-slab Wilson kernelの `0<K<=1` を使い、同じ非正値成分も許したsigned transfer自体に対して

```text
forall B, |T_H(B)| <= p_H/2
```

も形式証明した。正値核であっても符号付きsourceを非負と扱う誤りは犯していない。

## CLOSED — 右境界Lipschitz係数と有理メッシュ誤差の半減

元固定結合 `beta0=log(3/2)/64<=1/128`、元AEVの真のsource依存一リンク勾配、今回のHaar L1上界を合成し

```text
13 * beta0 * Msrc_H <= (13/256)*p_H
```

を証明した。元AHFの `card(Link_H)=p_H`、元AHGの一リンク有理立体射影メッシュの半径 `4/N`、元AHHの全リンク変動評価をそのまま利用し、

```text
forall H B N>0,
exists a : Link_H -> AHG_meshIndex N,
  |T_H(B)-T_H(B_(N,a))| <= (13/64)*p_H^2/N
```

を形式証明した。これはAHIの `(13/32)*p_H^2/N` から50%縮小した明示的な有理係数の厳密証明書である。左Haar積分のAGU/AGP格子と右境界近似のAHGメッシュを同一視しない。

## CLOSED — signed Haar表の端点による正負margin保存

元AGPの真正Haar質量を含むsigned tableで `lower>=q>0` が証明できた場合、元AGP物理包含定理から `T_H(B)>=q` である。

```text
(13/64)*p_H^2/N < q/2
    ==> exists a, T_H(B_(N,a)) > q/2.
```

負側の真正AGP `upper<=-q` についても

```text
(13/64)*p_H^2/N < q/2
    ==> exists a, T_H(B_(N,a)) < -q/2.
```

を同様に形式証明した。負のsource係数やmass min/maxによる向きは保存した。

## CLOSED — 一符号の「すべての十分大きな次数」への強化

AHHによる真正AGPの厳密符号表の**無条件な存在**と、証明済みの単調な実数分母評価を合成し、各有限Hについて

```text
exists q : Rat, 0<q and
  ((exists N0>96, forall N>=N0, exists a, q < T_H(B_(N,a)))
   or
   (exists N0>96, forall N>=N0, exists a, T_H(B_(N,a)) < -q)).
```

を形式証明した。AHIの「任意のMより大きい、あるN」から、「**あるN0以降のすべてのN**で同じ正の有理marginを保持する構成が存在」へ量化子を強めた。境界ラベル配置aはNごとに異なってよい。一つの符号枝のみの定理であって、正負両方や同じ単一境界での全次数評価は証明していない。

## CI初回失敗の構造的原因

初回 `#42339471807` はAHJの最後のdenominator補題でLeanの固定 `div_lt_iff₀` が返す積の順序を取り違え、2箇所型不一致となった。Leanは `C < s*N0` を返すため、`N0*s` とした局所式を `s*N0` に正規化し、単調性にも `mul_le_mul_of_nonneg_left` を使った。**定理文、仮定、元Haar法則・物理定義は不変更**。最終CIで下流 `sorryAx` の消失を独立確認した。

## OPEN / NEXT — AHK

今回のAHJは、実数幅係数の厳密な改善と、存在量化された有理marginの全次数安定性を与えた。具体的な受理した表のHaar質量数値区間、右境界ラベル、Hごとの正負符号枝、N0とqの数値評価は実施していない。二符号殻、H一様coercivity、Hamiltonian gap、連続体4D Yang–Mills質量ギャップも未証明のまま維持する。

次は元Haarモーメント・相殺構造あるいは体積に依らない厳密定量法によって、実行可能な正負符号下界と具体的境界証人への経路を評価する。

[AHJ Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/2c3e4bedee902073808691ceb28b0c4d35188efa/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTrueHaarHalfSourceSignStabilityV5_PZ37AHJ.lean)。本記録は新規ファイルのみ追加。README / ROADMAP、既存formal proofs、旧Type値証拠を変更しない。docs-onlyでStrict Leanは起動しない。
