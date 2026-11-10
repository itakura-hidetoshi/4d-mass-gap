# P4-Q2-PZ37AJJ — 真正Wilson Haar定数残差・全top距離と選択top多重度残余の形式証明

2026年11月10日 JST。定理の唯一の正本は `itakura-hidetoshi/4d-mass-gap` の `formal/real-hilbert-uniform-coercive-strong-limit`。本書は機械検証済みLeanソースとCIの来歴記録であり、本書自体は証明ではない。

[AJJ定理PR #6602](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6602) **MERGED**。[統合済みLean leaf](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/2857d5b2a566a28b32f0268333d684d1f24d829d/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHaarConstantTopResidualV5_PZ37AJJ.lean)。

## 1. 元の物理対象・仮定と範囲

各固定有限体積 `H` と `β>0` について、元のSU(2)完全Wilson one-slab、両端halfweight、真正積Haar確率、Gauss-law実物理Hilbert空間、元の中心化符号付きZW源 `f₀,H`、元の対称・正・コンパクト・ノルム1正規化物理transfer `S` を不変更とする。全top固定部分空間 `F=ker(S−I)`、その正準直交射影 `Q`、直交補への制限 `R`、既存の選択単位topベクトル `Ω` と真正Haar定数単位ベクトル `c` を用いる。

既存形式証明の**固定H,βごと**の `‖R‖<1` を使用。top一次元性、`Sc=c`、`Qc=Ω`、追加top成分の消失、体積一様な縮小率、無条件のAJA予算成立を追加仮定しない。

## 2. 形式化された上界と厳密分解

全top直交補への射影 `Qᗮ` について、一般実Hilbert定理と元SU(2)物理への適用から

```text
(1 − ‖R‖) ‖Qᗮ c‖ ≤ ‖c − S c‖
‖Qᗮ c‖ ≤ ‖c − S c‖ / (1 − ‖R‖)
```

を証明した。右辺分母の正値性は固定H,βの既存の `‖R‖<1` による。

選択top方向だけを残すことの危険を避けるため、**独立した定数側追加top残余**を

```text
rᶜ := Qc − ⟨c,Ω⟩ Ω
D := 1 − ⟨Ω,c⟩²
D = ‖Qᗮ c‖² + ‖rᶜ‖²
D ≤ (‖c−Sc‖/(1−‖R‖))² + ‖rᶜ‖²
```

と分解する。`rᶜ∈F` も証明した。内積は実Hilbertで、`‖c‖=‖Ω‖=1` を使用する。

既存AJFの**ZW源側追加top残余** `rᶠ:=Qf₀−⟨f₀,Ω⟩Ω` を別に保ち、AJGと接続して

```text
‖Q f₀‖² ≤ ‖f₀‖²[
  (‖c−Sc‖/(1−‖R‖))² + ‖rᶜ‖²
] + ‖rᶠ‖²
```

を真正の元Wilson物理定義から導いた。左辺が厳密AJA正Haar-L²証明書 `C_AJA` を下回り、元の直交ZW源が非零となるのは、上の**三寄与の和 < C_AJA** が別途証明された場合に限る。厳密不等式自体は未証明であり、この条件を成立済みの事実としては扱わない。

## 3. Lean4成果物・宣言と公理監査

追加は `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHaarConstantTopResidualV5_PZ37AJJ.lean` の**391行・1新規leafのみ**。実ファイル392行（末尾改行を含む数え方）。既存ソース削除・変更0、物理定義・Lean/mathlib pin・公開root・workflow変更0。

13宣言すべてに独立の `#print axioms` を設置した。

| 宣言名（共通名前空間を省略） | 証明内容 |
| --- | --- |
| realHilbert_fullTop_gap_mul_distance_le_defect_ajj | 実Hilbertでのgap×全top距離 ≤ defect |
| realHilbert_fullTop_distance_le_defect_div_gap_ajj | 正のgapで割った上界 |
| realHilbert_unitConstant_selectedTop_deviation_sq_split_ajj | 選択方向偏差の二乗厳密分解 |
| realHilbert_selectedTop_deviation_sq_le_defect_extra_ajj | defectと定数側追加top残余による上界 |
| p4Q2PZ37AJJ_originalHaarConstantExtraTopComponent | 定数側追加top残余の定義 |
| p4Q2PZ37AJJ_originalHaarConstantExtraTop_mem | 同残余が全topに属する |
| p4Q2PZ37AJJ_originalFullTopResidualGap_pos | 元物理gap分母の正値 |
| p4Q2PZ37AJJ_originalHaarConstant_gap_mul_fullTopDistance_le_defect | 真正物理へのgap×距離評価 |
| p4Q2PZ37AJJ_originalHaarConstant_fullTopDistance_le_defect_div_gap | 真正物理の距離上界 |
| p4Q2PZ37AJJ_originalSelectedVacuumDeviation_eq_fullTop_add_extra | 元選択Ω偏差の厳密分解 |
| p4Q2PZ37AJJ_originalSelectedVacuumDeviation_le_defect_extra | 元偏差のdefect上界 |
| p4Q2PZ37AJJ_originalSourceFullTop_norm_sq_le_defect_extra_const_source | 真正ZW源の3項上界 |
| p4Q2PZ37AJJ_originalOrthogonal_ne_zero_of_defect_extra_budget | **未証明の厳密予算を前件とする**条件付き非零性 |

最後の9宣言は `GroundStatePosteriorJoint` 名前空間。13宣言の使用公理は標準の `propext`、`Classical.choice`、`Quot.sound` のみ。新規 `sorryAx` なし。

## 4. CI失敗と修正の履歴を保存

- 初回source `acfe9ad3…`、[CI #42718290328](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42718290328)：FAILURE。117行の `linarith` が必要な代数関係を閉じられず、159行と316行の加法不等式の左・右の順序が `add_le_add_right` の返す型と不一致。314行では `norm_nonneg` に関数ノルムのような引数の付け方をして型不一致。
- 第2 source `e04be563…`、[CI #42719671153](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42719671153)：FAILURE。120行の同一偏差分解における `linarith` の未解決ゴールが残存。
- 最終source `c1c116a2f3de28104b411614e2070de975c321b0`：投影Pythagorasと単位方向分解を `simp only` 等で正規化し、`linarith [hP,hQ]` に必要な関係を与えた。二乗上界には非負性を明示した `nlinarith`、加法単調性には期待する辺の順序に合う `add_le_add_left` と明示的 `calc` を使用。仮定・元の物理対象・Lean pinを変更しない修正で通過。

## 5. 最終Exact-sourceの認証と統合

| 観測項目 | 認証結果 |
| --- | --- |
| Exact-source CI | [#42720802925](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42720802925) completed／SUCCESS |
| Lean依存閉包 | **11,424／11,424 SUCCESS** |
| 新規公理監査 | **13／13、標準3公理のみ** |
| 新規sorryAx／変更warning・error | なし／0・0 |
| 独立completion receipt | completed／SUCCESS、exact sourceに紐付く |
| PR source | `c1c116a2f3de28104b411614e2070de975c321b0` |
| AJJ統合PR | [#6602](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6602)、MERGED（2026-11-10 JST） |
| formalマージcommit | `2857d5b2a566a28b32f0268333d684d1f24d829d` |
| 定理変更差分 | 新規Lean 1件、+391／−0 |
| formal統合後push CI | **別途再観測対象**。未認証のままSUCCESSとは書かない |

修正sourceを直接指すCI run／receiptとマージ結果を区別した。原引継ぎにあるtest-merge tree `87c66075dce504a016dd5f456d939587cb439f0c` は履歴として残すが、ここではGitHub MCPで新たに3者のtree SHAを独立取得していないため、三者tree一致の再認証とは表現しない。

## 6. 次段AJKに残す真正obstruction

`‖c−Sc‖` の固定H,βでの有効な上界、`‖rᶜ‖²`、`‖rᶠ‖²` の**独立した**定量上界と、その合計が元AJAの正証明書 `C_AJA` より厳密に小さいことは未証明。全top eigenspaceの一次元性、真正ZW源の無条件top直交性、励起sector非零、体積一様coercivity、Hamiltonian spectral gap、4D連続体Yang–Mills mass gapも未証明。

AJKでは3項をそれぞれ真正元Wilson定義から評価するか、評価できない項を明示的obstructionとして残す。一般Hilbertの局所上界や条件付き十分条件を全有限H一様の物理定理へ格上げしない。append-only／tighten-only／overwrite-forbidden／same-root、Lean v4.30.0-rc2、mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6。
