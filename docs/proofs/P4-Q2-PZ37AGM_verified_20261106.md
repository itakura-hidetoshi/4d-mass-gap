# AGM 正式証明記録

記録日：2026-11-06 JST。唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。mainに置く本書は文書ミラーであり、Lean定理の正本ではない。

## 確定した状態

| 項目 | 確認結果 |
|---|---|
| 定理PR | [#6380](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6380) MERGED |
| 検証済みsource | `48f47c8143aba1ec3ce4766615eaf94cbf20a6ac` |
| CI checkoutのtest-merge | `0f62a4e659e9c981324082fa549c126647d890e3` |
| 定理squash | `99b1b2b2e9b27f6a61d5199271632ece4100acfc` |
| 3 commit共通Git tree | `ff9b5391d4bea5ae8e3b0e38942823ba939fcc1e` |
| exact-source CI | [#42158675778](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42158675778) completed / SUCCESS |
| Lean job / step | `127698833985` / Run changed Lean fast check：completed / SUCCESS |
| 依存閉包のビルド | 11,346 jobs成功 |
| 公理依存確認 | 新規9宣言、`propext`・`Classical.choice`・`Quot.sound`のみ |
| sorryAx | 全job log中に出現なし |
| 変更Lean warning/error | 0/0 |
| 独立completion receipt job | `127700342171` completed / SUCCESS |
| sourceへのreceipt status | `chatgpt-ci-receipt/PR Lean Fast Check` SUCCESS |
| 新規Leanファイル | 1ファイル・185行 |

[AGM Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/99b1b2b2e9b27f6a61d5199271632ece4100acfc/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAutoscaledKernelV5_PZ37AGM.lean)。元SU(2)・Wilson作用・核・固定結合beta0・Haar・Perron・中心化source・transfer・FF・公開rootを変更していない。固定環境はLean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

## 数学的内容

AGLは真正有理座標配置における元one-slab作用の厳密有理値を与え、AGKは元固定結合beta0を精密化可能な有理区間で包囲する。AGMは両者をAGJの指数Taylor区間へ接続し、必要な整数尺度と端点条件を入力データから構成した。

任意の有理指数端点lo,hiについて

`k = Nat.ceil (max |lo| |hi|) + 1`

と置くと、`k>0`、`|lo/k|<=1`、`|hi/k|<=1` が成立する。尺度を外から仮定する必要はない。元作用の非負性から厳密有理作用値の非負性も証明し、作用区間の下端非負条件を満たす。

元作用のsingleton区間をs、AGKの結合包囲を[b_lower,b_upper]として、指数端点を `lo=-(b_upper*s.upper)`、`hi=-(b_lower*s.lower)` と定める。結合次数m、正のTaylor次数nと上のkにより、実際の元核 `K_H(A,B)` のAFV `verifiedInterval` を構成する。元核の正値性・上界1を使い、端点を `[max(0,lower),min(1,upper)]` に狭める。

真正AFQの24中心を各元空間リンクへ割り当てた任意の左右配置へ自動的に適用できる。作用値oracleや指数の大きさに関する外部証明は不要であり、数値入力はm,nとn>0だけである。元の核を含む両側不等式と、AGAの元値に対する有理球も得られる。

零端点ではk=1、端点(-3/2,7/3)ではk=4という回帰命題を同じLeanビルドで検証した。

## 検証の根拠

GitHub MCPにより終了済みworkflow・Lean job・Lean step・独立receiptと、検証済みsourceへのstatusを再確認した。Lean job全文を検査し、9件の公理依存、ビルド成功、変更AGMのwarning/error 0/0を確認した。source、実際にcheckoutされたtest-merge、squashのGit treeをGitHub APIから個別取得して一致を確認した。

CIのartifactは[13476106392](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42158675778/artifacts/13476106392)。アップロードlogに記録されたSHA-256は `fbc0234965b2533277f477bf62f76c0fbff63cd73778fd6e44a9fbf3c4754cce`。本記録の独立再確認はjob log全文によるものであり、このartifact ZIPを再ダウンロードしてdigestを再計算したという主張はしない。

## AGM時点の残る課題

元の有限リンク列挙は非計算的なため、大体積の数値表を実行したことは意味しない。結合次数・Taylor次数・空間分割を同時に精密化した際の核区間幅の収束率は、本モジュールの結果に含まれない。

次段階は元Haarセル質量と中心化sourceの平均に対する具体的包囲を構成し、AGMの核区間をAGIの符号保持transfer証明書へ接続すること。実際の非零signed transfer符号、二閾値殻非空、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは、このAGMでは未証明。

AGK・AGLの独立証明記録は [P4-Q2-PZ37AGK-AGL_verified_20261106.md](P4-Q2-PZ37AGK-AGL_verified_20261106.md) を参照。本書は独立した追補であり、以前の記録を書き換えない。
