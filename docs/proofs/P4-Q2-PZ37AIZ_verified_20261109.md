# P4-Q2-PZ37AIZ — 全正結合における元の正規化ZW物理源像の真正Haar-L²非零性

2026年11月9日 JST。唯一のLean定理正本は `itakura-hidetoshi/4d-mass-gap` の `formal/real-hilbert-uniform-coercive-strong-limit`。

[統合済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/dc334fa6d68eee8f0d75f4c236f02be92b6f14a1/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNormalizedSourceAllPositiveCouplingV5_PZ37AIZ.lean) ／ [定理PR #6572](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6572)。

この記録は形式検証された定理の適用範囲と来歴を記載するものであり、文章自体が証明を構成するわけではない。

## 1．元の物理対象と量化

元の完全 SU(2) Wilson one-slab 作用、両端の空間halfweight、真正product-Haar確率測度、符号付きZW Gauss-law物理L²源 `f_{0,H}`、既存物理作用素 `P_{H,β}` と既存物理ノルム正規化 `N_{H,β}=P_{H,β}/‖P_{H,β}‖` を保持した。境界配置と物理Hilbert空間は有限体積Hごとに異なる。

新しい結論は **全H∈ℕおよび全β>0** に成立する。既存AITの半Haar下界が成立する結合範囲を全正結合へ拡大したという主張ではない。全結合で使用するのはAIGの **正Haar測度** のみである。

## 2．Leanで機械的に検証された接続

- **AIG**：各有限H、β>0の元の厳密全余裕負領域 `R_{H,β}` の真正Haar測度 `μ_H(R_{H,β})>0`。
- **AIW**：上記元の領域と、**同じ既存物理作用素ノルム**で割った元の連続正規化積分代表 `u_{H,β}` の厳密負領域 `{B : u_{H,β}(B)<-m_{H,β}}` が集合として等しい。L²クラスと指定積分代表とのHaar-a.e.橋は既存のものを使用する。
- **AIY**：同じ指定積分代表の厳密負領域が非零Haar測度を持てば、既存Gauss-law物理Hilbert空間で `N_{H,β} f_{0,H}≠0`。L²の任意代表に全点での符号を付与しない。

この三つを同一H・同一β・同一元source・同一measureで接続し、次を証明した。

\[
\boxed{\forall H\in\mathbb N,\ \forall\beta>0,\quad
0<\|N_{H,\beta}f_{0,H}\|_{L^2}
\le\|f_{0,H}\|_{L^2}.}
\]

同時に、元の非正規化物理作用素について

\[
\boxed{\forall H\in\mathbb N,\ \forall\beta>0,\quad
0<\|P_{H,\beta}f_{0,H}\|_{L^2}.}
\]

既存AIYの厳密ノルム比 `‖N f₀‖=‖P f₀‖/‖P‖` を用いて後者も証明した。すべての正の結合列 `β_H>0` に対して各有限Hごとの源像が非零である。AITの体積成長上端を1だけ超える結合でも同じ結果が成立する。一方、その結合で半Haar質量を主張しない。

## 3．新規Lean宣言10件

全宣言は `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` 名前空間に属する。

| 宣言のsuffix | 結果 |
|---|---|
| `p4Q2PZ37AIZ_originalNormalizedNegativeRegion_HaarMeasure_pos` | AIG/AIWから元の正規化負領域の正Haar質量 |
| `p4Q2PZ37AIZ_originalNormalizedPhysicalSource_ne_zero_allPositive` | 全正結合での既存Nによる真正L²源像非零 |
| `p4Q2PZ37AIZ_originalNormalizedPhysicalSource_norm_pos_allPositive` | 同L²ノルムの正値 |
| `p4Q2PZ37AIZ_originalRawPhysicalSource_ne_zero_allPositive` | 既存Pによる真正L²源像非零 |
| `p4Q2PZ37AIZ_originalRawPhysicalSource_norm_pos_allPositive` | 同raw L²ノルムの正値 |
| `p4Q2PZ37AIZ_originalNormalizedPhysicalSource_pos_le_input_allPositive` | 正のL²下端と元ZW源ノルム上界 |
| `p4Q2PZ37AIZ_originalNormalizedPhysicalSource_positiveSchedule` | 任意の正結合列で各HのN源像非零 |
| `p4Q2PZ37AIZ_originalPositiveCoupling_physicalNormAndRegion` | 同じH・βにおける源像正値、`‖N‖=1`、領域正測度 |
| `p4Q2PZ37AIZ_originalNormalizedPhysicalSource_norm_pos_above_AIT_cutoff` | AIT結合上端の外でも非零 |
| `p4Q2PZ37AIZ_originalRawPhysicalSource_positiveSchedule` | 任意正結合列で各HのP源像非零 |

各宣言に独立の実際の `#print axioms` を付した。新規定義0件。新規Leanファイル1件207行追加、削除0。

## 4．固定環境・型付き依存関係

- Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。
- `autoImplicit false`、`maxHeartbeats 3900000`、`synthInstance.maxHeartbeats 1050000`。既存の元物理定義・source・measure・root・manifest・workflowは変更していない。
- 新規Leanパス：`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNormalizedSourceAllPositiveCouplingV5_PZ37AIZ.lean`。
- 唯一の直接import：`MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalNormalizedSourceHaarL2NonvanishingV5_PZ37AIY`。先行AIG/AIW/AIYの署名を使用し、新たな物理公理・スペクトル仮定は導入していない。

## 5．Exact-source・squash後push CI認証

| 検証 | 修正版Exact-source | 統合後push |
|---|---|---|
| GitHub Actions | [#42600834308](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42600834308) | [#42603169982](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42603169982) |
| イベント／判定 | pull_request / SUCCESS | push / SUCCESS |
| HEAD | `94f896b1d0cd82b78377384040b7c7e766c3355d` | `dc334fa6d68eee8f0d75f4c236f02be92b6f14a1` |
| 主Lean job | `129104584221` / SUCCESS | `129112361722` / SUCCESS |
| 独立receipt job | `129106376750` / SUCCESS | `129115047903` / SUCCESS |
| Lean依存閉包 | 11,414 / 11,414 SUCCESS | 11,414 / 11,414 SUCCESS |
| 新規公理出力 | 10 / 10 | 10 / 10 |
| 依存公理 | `propext`、`Classical.choice`、`Quot.sound` のみ | 同左 |
| AIZ変更warning/error、AIZ sorryAx | 0 / 0、なし | 0 / 0、なし |

Lean構築の実ログに対して新規AIZ宣言10件の公理出力を照合した。独立completion receiptのSUCCESSも確認した。receiptは別Lean kernelによる二重証明を意味しない。文書専用PRでStrict Leanを手動起動しない。

## 6．初回失敗と修正の来歴

- 初回source `7bf7fcc1f0d8e8c775eb43f8f3421a415bf440c2`：初回CI [#42598574702](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42598574702) はLean型検査が成功したが、冗長な `simpa` に変更warningが1件あったため認証しなかった。
- 途中source `ce5eb985080c727e02430716161222690ac58c3c`、警告修正source `3d91ad2dbd347a65f7b96846acb4d7f1a589d0c2`：CI [#42599489122](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42599489122) で `simpa [hz] using ...` を `simp [hz] using ...` に誤変換したため、105・108行に構文／未解決goalエラーを生じた。エラー回復に由来する下流 `sorryAx` 出力は未認証の失敗履歴である。
- 最終source `94f896b1d0cd82b78377384040b7c7e766c3355d`：元の物理L²ノルム比を `rw [hz, norm_zero, zero_div] at hRatio` として明示的に書き換え、既存の正規化源像厳密正値と矛盾させた。署名・物理対象・仮定の弱化なし。修正後CIは10件すべて認証済み。

## 7．Git source・test-merge・squash来歴

| 対象 | SHA |
|---|---|
| AIZ前formal HEAD | `9ad9ff806ab826bc5f0d9009c7d3f3d95cc60ff8` |
| 最新認証source | `94f896b1d0cd82b78377384040b7c7e766c3355d` |
| 実test-merge | `da0e340d692c7cc45ab05762593478a5405a8e0e` |
| squash統合コミット | `dc334fa6d68eee8f0d75f4c236f02be92b6f14a1` |
| 上記source/test-merge/squashの共通Git tree | `86f6816c1139a92aee72549ce081d3377e206ae9` |
| 新規Lean blob | `ec1141993dbe725985ea536f0d3c519f7e394d40` |

squashの親は元のformal HEAD。source/test-merge/squashのGit tree一致により、認証済みと統合後のファイル状態を照合した。

## 8．未認証事項と次段AJA

**証明されたのは各有限H・各β>0での真正物理L²源像の非零性である。** 任意正結合列での各点非零性から、同じ下界での体積一様正振幅・励起sector直交性・正規化coercivity・共通Hilbert空間上の極限作用素・Hamiltonian spectral gap・連続体4D Yang–Mills mass gapは導かない。

次段AJA候補では二つの独立ゲートを区別する。(1) 元の指定連続代表・真正Haar質量・正規化余裕から有限H,βごとの **定量的L²下界** を型付きで構成する。(2) 元のtop固有空間への射影を既存物理Hilbert空間の真正射影と接続する。いずれも証明までは未認証。AIGの正Haar測度を任意正結合の半Haar測度へ昇格させず、体積一様性やspectral gapを仮定として追加しない。
