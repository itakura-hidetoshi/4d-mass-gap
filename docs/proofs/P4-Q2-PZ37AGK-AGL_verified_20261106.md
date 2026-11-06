# AGK・AGL 正式証明記録

記録日：2026-11-06 JST。
唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。mainに置く本書は文書ミラーであり、Lean定理の正本ではない。

## 確定した状態

| 項目 | AGK | AGL |
|---|---|---|
| 定理PR | [#6376](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6376) MERGED | [#6377](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6377) MERGED |
| 検証済みsource | `82b128c4ef62d68238dea0e1d61d1d6b3271d9a3` | `8e0b710c81e800789f8c14f0ea64c4052f2b9153` |
| 定理squash | `85f6a66ee5d347f87af63860ee36b381776bc758` | `03764ecd21ff080352af1adabea1bcf455aab5e4` |
| exact-source CI | [42152887002](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42152887002) SUCCESS | [42156812601](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42156812601) SUCCESS |
| 依存閉包のビルド | 11,344 jobs成功 | 11,344 jobs成功 |
| 公理依存確認 | 17宣言、標準公理のみ | 17宣言、標準公理のみ |
| sorryAx | なし | なし |
| 変更ファイルwarning/error | 0/0 | 0/0 |
| 独立completion receipt job | `127681986134` SUCCESS | `127694754905` SUCCESS |
| 新規Leanファイル | 245行 | 284行 |

元SU(2)・Wilson作用・核・固定結合beta0・Haar・Perron・中心化source・transfer・FF・公開rootを変更していない。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持。

## AGK — 元結合の精密化可能な有理包囲

元の `exp(64 beta0)=3/2` と固定mathlibの対数級数の上下界を接続した。

`a_n=(sum_{j<n}(1/5)^(2j+1)/(2j+1))/32`

`e_n=(5/768)*(1/25)^n`

に対して `a_n<=beta0<=a_n+e_n`。既存AGJの `[1/160,13/2048]` と交差させた端点 `lower_n=max(1/160,a_n)`、`upper_n=min(13/2048,a_n+e_n)` は元beta0を含み、`0<=upper_n-lower_n<=e_n`。幅の0への収束、任意正精度を満たす有限次数の存在、有理数だけの精度判定まで形式証明した。

4項での幅は `1/60000000`、8項の誤差上限は `1/23437500000000`。beta0の値自体を小数近似に置換していない。AGJの元Boltzmann核区間へ、結合の精密化次数と指数Taylor次数を独立に接続した。結合の固定包囲幅による制約を除いたが、作用区間・指数打切り・Haar質量・中心化平均の誤差も同時に解消したという主張ではない。

## AGL — 真正有理座標から元Wilson作用の厳密値

元SU(2)行列は `[[x0+i*x1,-x2+i*x3],[x2+i*x3,x0-i*x1]]`。この実際の行列規約から積・逆元の座標則を導き、元の群要素についての有理座標証拠を合成した。異なる符号規約の四元数を代入していない。

元Wilsonエネルギー `E(g)=1-x0` を使い、実際の4リンクplaquette積と時間方向相対積を評価する。元の有限plaquette列・リンク列を保持し、空間作用・crossing作用・one-slab作用が各有理評価に等しいことを証明した。

AFXが与える真正AFQ・24中心の有理座標を適用し、各元空間リンクへ中心を割り当てた任意の左右配置に対して、元作用の幅ゼロAFV区間 `[q_H(A,B),q_H(A,B)]` を構成した。作用値を外部oracleとして入力する必要はない。一方、元の有限列列挙は非計算的なため、大体積の数値表の実行・計算量評価まで完了したことを意味しない。

## 全文確認とLean4エラー修正

AGL全文、ADRの元行列・座標、AFXの真正中心、AGJ、元空間plaquetteの積順序・作用定義、固定mathlibを照合した。

1. 固定 `Mathlib/Data/Fin/VecNotation.lean` では `cons_val_two` と `cons_val_three` は自動simp属性を持たない。外側の `fin_cases` だけでは内側の有理ベクトルの2・3成分が残ったため、両補題を `norm_num` に明示した。方向・逆元の回帰命題は不変更。
2. 有限和の帰納法で `| cons ... => simpa ... using` の継続行が構文上の項として受理されず、関数と証明の型不一致およびunexpected tokenが生じた。複数行の分岐に直し、`map_cons`、`sum_cons`、`Rat.cast_add`、各項の等式、帰納法仮定による `simp only` で閉じた。定理文は不変更。
3. Wilsonエネルギーのsimp証明は既に完結していたため、不要な後続ringを除去した。linterの無効化ではない。

有限和証明の失敗から後続作用定理へ伝播していたsorryAxも、修正後の全17宣言で解消した。公式Leanの構文・tactic資料と固定ソースの違いを区別し、実際の適合性は固定環境CIで判定した。

参考：
- https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/
- https://lean-lang.org/doc/reference/latest/The-Simplifier/Simp-sets/
- https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Fin/VecNotation.lean

## 検証の同一性と診断ファイル

AGKのsource・test-merge `2ab5efcc2884304cf9f496097dcf63aab58a9e26`・squashは共通Git tree `c3ac4058e4360c31b849010ff2d3c809bb53ae81`。artifact `13472719150` のSHA-256は `79946663cbce49c38c45e867983952f68c981b83a5024fef69f4d55c22d6905d`。

AGLのsource・test-merge `0eb5b3522f5a6514392f0bcce5ecd623f2e40bab`・squashは共通Git tree `367191adc3751df78bff5f0c02d3d3dd8121490b`。artifact `13475037147` のSHA-256は `6a043898fe69dc3298f42f1de422155135be224a8e6f488f67012f02d87bcfca`。

両ZIPのdigestとlean-fast.logを実検査した。workflow・Lean job・Lean step・独立receiptの終了後に判定し、検証済みHEAD指定でマージした。AGKをAGLへ取り込む際も両親commitを保持し、force-pushで履歴を書き換えていない。

## 未解決事項と次段階

次段はAGLの厳密有理作用をAGKの精密結合・AGJの指数区間へ統合し、指数尺度条件を有理データから自動保証すること。真正Haarセル質量、中心化平均の具体的区間は別途必要。実際の非零signed transfer符号、二閾値殻非空、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは未証明。

本書は独立した追補であり、既存README・ROADMAPを上書きしない。今回のroot README・ROADMAPへの同期は未実施。文書更新用補助workflowの追加が制限されたため、通常のGitHub文書追加だけで本書を保存している。
