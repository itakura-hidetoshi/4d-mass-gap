# P4-Q2-PZ37AJM — 元Wilson有限冪の二側残余境界とAJA厳密小条件の必要障害

2026年11月10日 JST。一次正本は `itakura-hidetoshi/4d-mass-gap` の `formal/real-hilbert-uniform-coercive-strong-limit`。本記録はLean4形式結果と独立CIの来歴を区別する。記録自体を物理的証明と混同しない。

## 1. 不変の物理源と条件

固定有限体積H、β>0で、元のSU(2) Wilson one-slab transfer `S`、Gauss-law実物理Hilbert空間、Haar定数単位方向 `c`、符号付き中心化ZW源 `f₀`、選択単位top固有ベクトル `Ω`、全固定top空間 `F`、直交射影 `Q`、直交補制限 `R` を元定義のまま用いる。元の両端halfweight、積Haarと正規化は変更しない。固定されたLean v4.30.0-rc2、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、rootと仮定も不変更。

AJI/AJJ/AJK/AJLで認証した `‖R‖<1`、全top強収束、元Wilson冪の誤差境界、別々の二種類の追加top残余を利用する。

## 2. Lean4で認証された数学的命題

任意の元物理ベクトルx、整数n>0について、選択Ωに関する有限冪偏差、追加top残余、全top直交冪tailをそれぞれ

- `dₙ(x)=‖Sⁿx−⟨x,Ω⟩Ω‖`
- `r(x)=‖Qx−⟨x,Ω⟩Ω‖`
- `tₙ(x)=‖R‖ⁿ ‖Q⊥x‖`

とする。一般実Hilbert定理は、二方向の実際の有限冪誤差境界

`dₙ(x)≤r(x)+tₙ(x)` と `r(x)≤dₙ(x)+tₙ(x)`

を形式証明する。これは同値な `|dₙ(x)−r(x)|≤tₙ(x)` の二側境界である。

真正Haar定数では独立に `tₙ(c)≤‖R‖ⁿ‖c−Sc‖/(1−‖R‖)` を適用し、真正中心化ZW源では `tₙ(f₀)=‖R‖ⁿ‖Q⊥f₀‖` の別個のtailを保持した。Haar定数側の尾部評価をZW源側の物理評価へ置換していない。

元ZW源の追加top残余 `rᶠ=Qf₀−⟨f₀,Ω⟩Ω` と元全top射影には、AJFの直交分解から `‖rᶠ‖²≤‖Qf₀‖²` が成り立つ。

元AJA Haar-L²下限予算を `B=(m_H)² μ_H{u_H<−m_H}` と書く。もし `B≤‖rᶠ‖²` なら、元AJAに接続する厳密条件 `‖Qf₀‖²<B` は不可能である。さらに、n>0と非負の数Tについて `B≤T²`、`T+tₙ(f₀)≤dₙ(f₀)` が与えられれば、同じ厳密小条件の不成立が従う。

**論理範囲:** これらは条件付きの*必要障害*であり、元AJAの予算条件の数値成立／不成立や、真正励起sectorの消失／非零を決定しない。選択topと全topを同一視せず、追加top残余がゼロ・小さいとは仮定しない。

## 3. 成果物・7宣言・Lean核の監査

[統合済み定理PR #6615](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6615) MERGED。新規Lean leaf:

`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFinitePowerTopBudgetObstructionV5_PZ37AJM.lean`

新規317行、既存ファイル変更・削除ゼロ。次の全7宣言に `#print axioms` を配置した。

1. `realHilbert_selectedPowerDeviation_norm_le_extraTop_add_tail_ajm`
2. `realHilbert_selectedPowerDeviation_norm_twoSided_ajm`
3. `p4Q2PZ37AJM_originalHaarConstant_powerDeviation_twoSided`
4. `p4Q2PZ37AJM_originalSource_powerDeviation_twoSided`
5. `p4Q2PZ37AJM_originalSourceExtraTop_sq_le_fullTop_sq`
6. `p4Q2PZ37AJM_originalSourceExtraTop_blocks_fullTopSmall`
7. `p4Q2PZ37AJM_originalSourceFinitePower_blocks_fullTopSmall`

実際のkernel公理監査は7/7で、使用公理は標準の `propext`、`Classical.choice`、`Quot.sound` のみ。新規 `sorryAx` なし。変更Lean error/warning 0/0。

## 4. 失敗原因と修正の来歴

初回source `cc25a41ab3dc6cbadf331285cadfff894efc914e` に対する [CI #42757038071](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42757038071) はFAILURE。新規leafの75行、186行で、加法不等式をtransでつなぐ際に「左項に付加する」形 `add_le_add_left` を誤使用していた。修正では同型の185行も予防的に含め、3箇所のみ `add_le_add_right` にした。定理文、仮定、元Wilson物理定義、固定ツールチェーンは変更していない。

## 5. Exact-source、正式統合と受領

- 修正source：`eeee78092d89093d63f8d9d8c0436b7f0c59a39e`
- [Exact-source CI #42757780577](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42757780577)：**completed／SUCCESS**。変更Lean依存閉包 **11,427／11,427 SUCCESS**、7/7標準3公理のみ、変更warning/error 0/0、新規`sorryAx`なし。
- 独立受領ジョブ：**completed／SUCCESS**。`event=pull_request exact_sha=eeee78092d89093d63f8d9d8c0436b7f0c59a39e source_result=success run=42757780577 attempt=1`。commit status `chatgpt-ci-receipt/PR Lean Fast Check` SUCCESS。
- 定理PR #6615：**MERGED**。正式merge commit `0ebbab58cae7f42043f61392dba40020380df37d`。
- 修正sourceとmerge上のLeanファイルGit blobは共に `be7824ea909751b81bf8c1accb1ff8391bf84a23`。一次Lean内容の同一性をGitHub MCPで独立照合済み。
- 統合後push CI #42758364446：**この記録作成時点は未認証／実行中**。完了後に実ログと受領書を独立再観測して追記する。未完了をSUCCESSとしない。

## 6. 未解決の障害（OPEN）

元AJAの厳密予算を満たす具体的有限冪証人、追加top残余の数値的な大小または消失、全top一次元性、無条件の真正励起sector非零性、体積Hに一様な強制性とHamiltonian spectral gap、連続体4D Yang–Mills質量ギャップはいずれも**OPEN**。条件付き不可能性定理を質量ギャップ問題の不可能性へ拡大解釈しない。

運用はappend-only／tighten-only／overwrite-forbidden／same-root。文書を追加するだけでLean再検証を不要に実行せず、docs-only Strict LeanはSKIPPEDのはずである（CI結果とは区別）。 

## 7. 統合後push CIの独立完了認証（追記）

定理merge `0ebbab58cae7f42043f61392dba40020380df37d` に対する [push CI #42758364446](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42758364446) は **completed／SUCCESS**。GitHub MCPで実行イベント、二つのジョブの完了、Lean実ログ、公理監査の7出力、独立completion receipt、GitHub commit status を再観測した。

- `Changed Lean fast check`: completed／SUCCESS。Lean依存閉包 **11,427／11,427 SUCCESS**。7宣言の実公理監査はすべて標準の `propext`、`Classical.choice`、`Quot.sound` のみ、新規 `sorryAx` なし、変更Lean warning/error 0／0。
- `Publish MCP CI completion receipt`: completed／SUCCESS。実ログ `event=push exact_sha=0ebbab58cae7f42043f61392dba40020380df37d source_result=success run=42758364446 attempt=1`。同コミットの `chatgpt-ci-receipt/PR Lean Fast Check` は `state=success`。
- 第5節の「統合後push CI未認証」は当時の観測を保存した履歴であり、この追記で**独立再認証済み**に更新する。受領書はLean定理ではない。

依然として元AJA厳密予算証人、残余ゼロ・大小、top一次元性、無条件励起sector非零性、H一様coercivity、Hamiltonian gap、4次元連続体Yang–Mills質量ギャップは **OPEN**。
