# P4-Q2-PZ37AJN — 元Wilson冪の直交ノルム二乗恒等式とAJA厳密予算の条件付き検査

2026年11月10日 JST。Lean4の唯一の定理正本：`itakura-hidetoshi/4d-mass-gap` / `formal/real-hilbert-uniform-coercive-strong-limit`。この正式記録は一次Lean source、kernel検証、Git来歴、数学的解釈を区別する。説明文書そのものを証明とみなさない。

## 1. 元物理定義と依存閉包

固定有限体積 H∈ℕ と β>0 の真正SU(2) Wilson normalized one-slab、元のGauss-law物理実Hilbert、Haar定数単位方向 c、符号付き中心化ZW source f₀、選択単位topベクトル Ω、全top固定空間 F、正射影 Q、全top直交補制限 R を不変更とする。

AJHの対称transferによる全top射影の冪不変性、AJIの正真正銘の元Wilson冪の全top収束と誤差、AJFの選択top/追加top Pythagoras、AJJのHaar定数側別残余、AJMの有限冪二側評価を継承。top一次元性、追加top残余ゼロ、数値的AJA予算成立、H一様ギャップは仮定しない。Lean v4.30.0-rc2、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、元物理源・root・仮定は変更なし。

## 2. 認証済み形式結果

選択topベクトル Ω∈F に対し、実Hilbertの元演算子SがFを不変に固定し対称であるとき、任意のn∈ℕ、xについて

```text
‖S^n x − ⟨x,Ω⟩ Ω‖²
  = ‖Qx − ⟨x,Ω⟩ Ω‖² + ‖S^n x − Qx‖²
```

が**等号で**成り立つ。AJMの三角不等式より強く、両項は正規直交top成分と元Wilson冪の真の直交減衰成分である。n>0ではさらに

```text
r(x)² ≤ d_n(x)² ≤ r(x)² + (‖R‖^n ‖Q⊥x‖)²
```

を証明。元Haar定数cと元中心化符号付きZW源f₀に別々に適用して、両者の残余は異なるType値であることを保持した。

元AJAの正真正銘の下限予算B = m_H² μ_H({u_H < −m_H})を用い、中心化ZW源について以下を条件付きで検査する。

- 元の選択冪残差の実観測 `⟨f₀,Ω⟩² + d_n(f₀)² < B` が存在すれば、`‖Qf₀‖² < B` が成立し、元AJDの励起直交source非零へ進む。ただし、この実測条件の成立は未認証。
- 逆に `B + (‖R‖^n ‖Q⊥f₀‖)² ≤ ⟨f₀,Ω⟩² + d_n(f₀)²` なら、`‖Qf₀‖² < B` は不可能。元AJA証明書のこの特定の**厳密小条件**を遮断するのであって、励起の消失や質量ギャップの不存在を証明しない。

## 3. Lean leafと公理監査

[定理PR #6620](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6620) **MERGED**。

`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalOrthogonalPowerSquareBudgetV5_PZ37AJN.lean` を新規323行追加、既存ファイル変更・削除0。定理7宣言・実行時`#print axioms`7件。

宣言：

1. `realHilbert_fixedSubspace_selectedPower_sq_split_ajn`
2. `realHilbert_fullTop_selectedPower_sq_interval_ajn`
3. `p4Q2PZ37AJN_originalHaarConstant_powerDeviation_sq_eq_extra_add_orth`
4. `p4Q2PZ37AJN_originalSource_powerDeviation_sq_eq_extra_add_orth`
5. `p4Q2PZ37AJN_originalSource_powerDeviation_sq_interval`
6. `p4Q2PZ37AJN_originalSource_selectedPower_sq_budget_implies_excitation`
7. `p4Q2PZ37AJN_originalSource_selectedPower_sq_budget_obstruction`

## 4. Lean4失敗と修正の来歴

初回source `2961b074f369e8d4b53502026440cca76040fc02`、[CI #42760340150](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42760340150)はcompleted／FAILURE。変更ファイル全文・imports・依存定理・固定mathlib APIを照合し、次の4件の構造原因を特定：

- 54行：`real_inner_comm a b`の定理等式の向きが逆。宣言値が要求する向きへ`.symm`を適用。
- 121行：`add_le_add_left hTailSq`が加算項の位置と異なる。期待式の左側固定項に合わせ`add_le_add_right`へ修正。
- 162、192行：元物理top空間の`HasOrthogonalProjection`はambient Hilbert完全性だけでは推論されない。既存AJFと固定mathlibの`HasOrthogonalProjection.ofCompleteSpace`に沿い、元物理topがclosedゆえCompleteSpaceである局所インスタンスを追加。

失敗時の`sorryAx`表示は未成立定理からの連鎖であり、形式認証ではない。既存定理文・物理仮定・固定Lean/mathlibを一切変更せず、新規leafだけ修正した。

## 5. Exact-source・統合認証

- 修正source `47f5a1aa4e3b80f9113204d8252042deffd090b6`。
- [Exact-source CI #42805725280](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42805725280)：**completed／SUCCESS**、Lean依存閉包 **11,428／11,428 SUCCESS**、変更Lean warning/error 0／0、7/7実公理監査は`propext`、`Classical.choice`、`Quot.sound`のみ、新規`sorryAx`なし。
- 独立completion receipt：completed／SUCCESS、`event=pull_request exact_sha=47f5a1aa4e3b80f9113204d8252042deffd090b6 source_result=success run=42805725280 attempt=1`。commit status`chatgpt-ci-receipt/PR Lean Fast Check`はSUCCESS。
- 正式マージ：PR #6620 MERGED、`ef62746f1abbe37f960d6967aa93865fa1e31859`。修正sourceと正式mergeのLeanファイルGit blobが`40dd45d72282ca0743e4f36e0a33cc37fd34f2bd`で一致。
- 定理統合後push CI [#42809741159](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42809741159)：**記録作成時点はin_progress／未認証**。完了後の実ログと独立receiptを再観測してから追記する。

## 6. 未解決の証明条件（OPEN）

元AJA厳密予算Bに入る具体的有限冪証人、追加top残余の数値的消失・上界、top一次元性、無条件の元ZW励起sector非零性、体積H一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills mass gap はなお **OPEN**。局所有限H・βの条件付き関係を全体の物理的結論へ昇格させない。

運用：append-only／tighten-only／overwrite-forbidden／same-root。docs-onlyではStrict Leanを再実行しない。
