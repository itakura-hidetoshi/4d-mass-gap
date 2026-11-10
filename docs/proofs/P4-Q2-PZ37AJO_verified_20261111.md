# P4-Q2-PZ37AJO — 正真正銘の二時点Wilson冪による追加top残余の挟み込みとAJA条件付き予算障害

2026年11月11日 JST。定理正本は `itakura-hidetoshi/4d-mass-gap` の `formal/real-hilbert-uniform-coercive-strong-limit`。この文書はLeanコードとGitHub Actionsの受領記録を説明するものであり、新たな数学的証明ではない。

## 1. 既存定義と対象

有限 H∈ℕ、β>0、元SU(2) Wilson正規化one-slab物理transfer `S`、Gauss-law実Hilbert、Haar定数cと元の中心化ZW物理源 f₀、選択単位top Ω、元の全top固定空間 F、その正射影 Q、全top直交補制限 Rを変更せず継承する。 q=‖R‖<1 は各固定有限H,βで既証明であり、Hに一様な下界ではない。

AJIから元の冪と全top直交補の制限の可換性を、AJNから真正二乗直交分解を取り込む。Dₙ(x)=‖Sⁿx−⟨x,Ω⟩Ω‖²、r(x)²=‖Qx−⟨x,Ω⟩Ω‖²と置く。

## 2. Lean kernelで検証済みの式

まず真正冪の直交tailについて `‖Sⁿ⁺¹x−Qx‖≤q‖Sⁿx−Qx‖` と二乗版を証明した。AJNの直交分解に代入することによって、選択Ωが全topの唯一の方向であると仮定せず、

```text
D_(n+1)(x) - q² D_n(x) ≤ (1-q²) r(x)²
r(x)² ≤ D_(n+1)(x)
```

を証明した。これを元中心化ZW源 f₀に適用した。よって q<1 の固定H,βでは、二時点の有限冪量が未知の追加top残余を下側からも制限する。ただしこれらの量の実数値や非自明な予算内証人は未提供。

元AJAの正真正銘のHaar予算 `B=m_H² μ_H({u_H<−m_H})` と `α=⟨f₀,Ω⟩` に対し、次を条件付きで証明した。

- 十分条件：`α² + D_(n+1)(f₀) < B` なら、元の励起直交源は非零。
- 必要障害：`(1−q²) B ≤ (1−q²)α² + D_(n+1)(f₀)−q² D_n(f₀)` なら、元AJAの厳密小条件 `‖Qf₀‖² < B` は不可能。

いずれも元AJA予算の条件付き判定であり、証人の存在・不在、励起sectorの無条件非零、質量ギャップを確定しない。

## 3. 新規形式宣言と公理監査

[定理PR #6623](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6623) MERGED。新規ファイル `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTwoStepResidualBudgetV5_PZ37AJO.lean` 1件（GitHub差分318行追加）、6宣言、実行時 `#print axioms` 6件、既存ファイルの変更・削除0。

宣言は `realHilbert_fullTop_power_tail_step_norm_le_ajo`、`realHilbert_fullTop_power_tail_step_sq_le_ajo`、`realHilbert_selectedPower_sq_twoStep_bracket_ajo`、`p4Q2PZ37AJO_originalSource_twoStep_selected_sq_bracket`、`p4Q2PZ37AJO_originalSource_nextPower_sq_budget_implies_excitation`、`p4Q2PZ37AJO_originalSource_twoStep_sq_budget_obstruction`。

## 4. 初回失敗と修正（修正履歴は消さない）

初回source `872b385db8aed6dfc5952ba8f3417338f5b29325` の [CI #42811595277](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42811595277) はcompleted/FAILURE。変更leaf全文・imports・依存するAJI/AJN署名・固定Lean/mathlibを照合した。276行 `norm_nonneg _` の `_` が作用素のnormed型クラスを確定できず `Type mismatch`。このため最後の1宣言には一時的に `sorryAx` が表示され、認証には至らなかった。

修正は新規leafの1行のみ：`norm_nonneg _` → `norm_nonneg (RO beta hbeta.le)`。定理文、元Wilson作用素、仮定、既存コード、Lean/mathlib pin、rootを変更していない。

## 5. 正式認証・統合証拠

- 修正source `6c8014755dbf0753d74847766dc57abbe670c374`。
- [Exact-source CI #42877533307](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42877533307) completed/SUCCESS、**11,429/11,429** Lean依存閉包、6/6実公理は `propext`・`Classical.choice`・`Quot.sound` のみ。新規`sorryAx`なし、変更Lean warning/error 0/0。
- 独立completion receipt completed/SUCCESS: `event=pull_request exact_sha=6c8014755dbf0753d74847766dc57abbe670c374 source_result=success run=42877533307 attempt=1`。commit status `chatgpt-ci-receipt/PR Lean Fast Check` SUCCESS。
- [PR #6623](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6623)正式MERGED、formal HEAD `c6612ee088e9938dadf1d011b8e0451c28f4bcf8`。
- 認証sourceと正式統合後の新規LeanファイルのGit blobは同じ `9d1b502c66191e5992da5bb3a6fa8787ab3e7648`。
- 統合後push [CI #42897129027](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42897129027) はこの文書作成時点で **in_progress／独立未認証**。完成後の実ジョブ、公理出力、独立receiptを観測したのちに履歴として追記する。

## 6. 未解決（OPEN）

AJAの厳密小予算Bを満たす元Wilson冪の具体的有限証人、二時点量の独立数値的評価、元ZW源追加top残余ゼロまたは十分な上界、top一次元性、無条件励起非零、H一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは未証明。各固定有限H,βの既証明評価は全体への降下や権限を与えない。

固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、append-only／tighten-only／overwrite-forbidden／same-root。docs-only PRではStrict Leanを再実行しない。


## 7. AJO統合後push CIの独立完了認証（2026-11-11追記）

第5節でin_progress／未認証と記した真正定理merge `c6612ee088e9938dadf1d011b8e0451c28f4bcf8` の [push CI #42897129027](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42897129027) はGitHub MCPの再観測で **completed/SUCCESS**。二ジョブ `Changed Lean fast check` と `Publish MCP CI completion receipt` は共にcompleted/SUCCESS。依存閉包 **11,429/11,429**、変更AJO Lean6/6公理監査は `propext`、`Classical.choice`、`Quot.sound` のみ、sorryAxなし、変更Lean warning/error0/0。独立receipt `event=push exact_sha=c6612ee088e9938dadf1d011b8e0451c28f4bcf8 source_result=success run=42897129027 attempt=1` と、同じcommitに付された `chatgpt-ci-receipt/PR Lean Fast Check` successを確認。旧未認証表記は観測時の履歴として残す。物理的未証明条件はそのままOPEN。
