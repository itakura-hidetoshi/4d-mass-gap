# P4-Q2-PZ37AIJ — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。mainは正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元の完全SU(2) Wilson一スラブ作用と両端halfweight、ZW符号付き物理L²源とその連続代表、元の空間積Haar、仮定、固定Lean/mathlib、workflow、証明履歴を変更していない。

## 1．検証済みソースと実際の統合

| 項目 | 確認した値 |
| --- | --- |
| 定理PR | [#6524](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6524)、MERGED |
| 基礎canonical formal HEAD | `ecffee9e5aa9ace93b7d5663130990d9607b05db` |
| exact-source HEAD | `d04e4e45914a8f8cd9067b205c28ffe67bc1b4c4` |
| CIが検査したtest-merge HEAD | `a945bc8747c0b624648db238817c114d2e565781` |
| 定理squash | `4a6ac19850cbe30a5d2621efd78c25515dcb151f` |
| source／test-merge／squash共通Git tree | `d86ee66768d46248b08d2900984fefceb93e5bfc` |
| source／squash共通Lean blob | `ca1c3b44007fdb9d1d8ac4c8af51753c3f224a10` |
| 変更範囲 | 新規Lean 1件・332行、17定理＋3定義、既存ファイル変更0、削除0 |
| [Exact-source CI #42481374808 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42481374808/attempts/1) | workflow completed／SUCCESS |
| 必須Lean job | `128733840029`、completed／SUCCESS |
| 必須Lean step 17 | Run changed Lean fast check、completed／SUCCESS |
| Lake依存閉包 | **11,398／11,398 SUCCESS** |
| 新規AIJ leaf実ビルド | **15秒**、元のheartbeat上限のまま |
| 公開宣言／print命令／実際のaxiom出力 | **20／20／20**、一対一一致 |
| 公理出力の欠落／余剰／重複 | **0／0／0** |
| 公理依存 | 全20件が `propext`・`Classical.choice`・`Quot.sound` のみ |
| 完成した診断ログのsorryAx | **0件** |
| 変更AIJ Lean warning／error | **0／0** |
| 独立completion receipt job | `128735206232`、completed／SUCCESS |
| receipt実出力 | `exact_sha=d04e4e45914a8f8cd9067b205c28ffe67bc1b4c4 source_result=success run=42481374808 attempt=1` |
| exact-head commit status | `chatgpt-ci-receipt/PR Lean Fast Check`、SUCCESS |
| diagnostic artifact | `13617317592`、`lean-fast-check-log`、129734 bytes |
| archive SHA256（実取得bytesとGitHub metadata一致） | `53c8eeeb898d52ae2de6fd953120cabc59417002e1a1f3852c86fc8790c8e379` |
| 展開したlean-fast.log | 1889353 bytes |
| 展開ログSHA256 | `1d2ba0d666155d6553892cc180cbc2d7e41b3dad26209dd4fce7cc12a1d5dd27` |

[検証済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/4a6ac19850cbe30a5d2621efd78c25515dcb151f/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPrimitiveNegativeHaarFloorV5_PZ37AIJ.lean)。直接importはPZ37AII。固定環境はLean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。`maxHeartbeats 3900000`、`synthInstance.maxHeartbeats 1050000` を保持した。

workflow・job・必須Lean stepの完了後に、実際の診断ログを取得してSHA256を再計算し、20宣言・20公理出力、sorryAx、変更ファイルのwarning/errorを検査した。独立receiptとは、元Leanジョブの終了を受けてexact-source結果を記録する別CIジョブであり、別の人間やsubagentによるコードレビューを意味しない。ソースの全文と直接利用する依存署名は実装担当側で照合したが、歴史的な全推移依存定理を別途全面監査したとは主張しない。

sourceとtest-mergeのGit treeをGitHub MCPで取得し、実際のsquash後にもtreeとLean blobを再取得して一致を確認した。初回candidate・初回CI attemptで成功し、Leanソース修正、仮定の追加・弱化、heartbeat増加、workflow変更は不要だった。変更ファイルの警告0は、再生された依存ファイルの全ログが警告0という意味ではない。初期PRの未認証台帳は保存し、完了時の検証記録を別のコメントとして追記している。

## 2．引き継いだ物理対象

任意の有限体積パラメータ \(H\in\mathbb N\) に対し、元の空間リンク型の要素数を

\[
n_H=\operatorname{Nat.card}(\mathrm{Link}_H)
\]

とする。\(p_H\) は元の空間plaquette数、\(\mu_H\) は同じ元の正規化空間積Haar確率測度。\(f_{0,H}\) はZW物理L²源、\(f_H\) は既証明の連続代表、\(V_H=\int f_H^2\,d\mu_H\)、\(M_H=\int|f_{0,H}|\,d\mu_H\)。\(t_{H,\beta}(B)\) は両端の空間halfweightを保持した元の完全Wilson一スラブtransferである。

\(\kappa(r)\) は既存ADQの `p4Q2PZ37ADQ_sphereRadiusFraction r`。既存の幾何的下界であって、本成果で数値評価した球の質量ではない。新規の測度・物理源・カーネルは導入していない。

## 3．交差Haar分配積分と源分散の下界

元の一リンクWilsonエネルギーは \(E(g)\le2\)。\(\beta\ge0\) の下で指数関数の単調性から

\[
e^{-2\beta}\le e^{-\beta E(g)}
\]

を得る。AIFの元の一リンク積分の可積分性と正規化Haar確率を用いて積分すると

\[
e^{-2\beta}\le Z_1(\beta).
\]

AIFの元の交差分配積分は厳密に \(Z_{\mathrm{cross},H}(\beta)=Z_1(\beta)^{n_H}\) である。非負な実数の累乗の単調性と、自然数帰納法で証明した指数の累乗恒等式により

\[
\boxed{e^{-2\beta n_H}\le Z_{\mathrm{cross},H}(\beta)}\qquad(\beta\ge0)
\]

となる。`Fintype.card_eq_nat_card` は有限型構造の表示差を除くためだけに使用し、リンク型・Haar測度を変えていない。

AHNの元の恒等配置箱における源分散下界を

\[
\boxed{v_H=\left(\frac{3p_H}{8}\right)^2\kappa(1/96)^{n_H}>0}
\]

と新たに名前付けし、\(v_H\le V_H\) を既証明のAHNから運ぶ。この正性は元の \(p_H>0\) と \(\kappa(1/96)>0\) に由来し、追加の非零源仮定を置かない。

## 4．未評価の元積分を含まない余裕と半径

AIGの元の余裕は変更しない。

\[
\varepsilon_{H,\beta}
=\frac{\beta Z_{\mathrm{cross},H}(\beta)e^{-2\beta p_H}V_H}{2}.
\]

AIJでは別の量として

\[
\boxed{\delta_{H,\beta}
=\frac{\beta}{2}e^{-2\beta(n_H+p_H)}v_H}
\]

を定義する。\(\beta>0\) で \(\delta>0\)、\(\beta=0\) で \(\delta=0\)、\(\beta\ge0\) で

\[
\delta_{H,\beta}\le\varepsilon_{H,\beta}
\]

を証明した。指数の積への分解と、前節の2つの下界を非負係数で掛け合わせる構成である。

AIHの元の境界変動係数は \(\Lambda_H(\beta)=13\beta M_H\)。既証明の \(M_H\le p_H/2\) から

\[
2(\Lambda_H(\beta)+1)\le13\beta p_H+2
\]

が得られる。そこで

\[
\boxed{r_H(\beta)=\frac{\delta_{H,\beta}}{13\beta p_H+2}}
\]

を定義する。\(\beta>0\) では両分母が正であることを明示し、交差乗算で

\[
\boxed{0<r_H(\beta)\le
R_H(\beta):=\frac{\varepsilon_{H,\beta}}{2(\Lambda_H(\beta)+1)}}
\]

を証明した。新しい分子は小さく、分母は大きいという両方の方向を保持している。新しい \(v_H,\delta_{H,\beta},r_H(\beta)\) の式に、交差分配・源分散・源L¹の未評価積分は現れない。ただし既存の幾何定数 \(\kappa\) の数値評価までは行っていない。

## 5．同じ全余裕負領域に対する真正Haar下界

AIIが構成した元の境界中心 \(B_H\) は

\[
t_{H,\beta}(B_H)<-3\varepsilon_{H,\beta}/2
\]

を満たし、元の距離 \(D_{\mathrm{sp},H}\) による半径 \(R_H(\beta)\) の球では全点で \(t<-\varepsilon\) となる。上の半径比較により、小さい半径 \(r_H(\beta)\) の**同じ元の空間球**も含まれる。

AIGの元の全余裕領域を

\[
\mathcal N_{H,\beta}=\{C:t_{H,\beta}(C)<-\varepsilon_{H,\beta}\}
\]

としたまま、AHLの真正Haar球定理を新しい正の半径 \(r_H\) に直接適用すると

\[
\boxed{
0<q_H(\beta):=\kappa\!\left(\frac{r_H(\beta)}{n_H+1}\right)^{n_H}
\le\mu_H^{\mathrm{real}}(\operatorname{Ball}_H(B_H,r_H(\beta)))
\le\mu_H^{\mathrm{real}}(\mathcal N_{H,\beta}).
}
\]

ここで \(q_H\) は本記録の略記である。\(\kappa\) の単調性を仮定して旧下界から新下界へ移したのではなく、新半径で既存Haar球定理を直接使った。

また \(\delta\le\varepsilon\) より

\[
\mathcal N_{H,\beta}\subseteq\{C:t_{H,\beta}(C)<-\delta_{H,\beta}\}
\]

なので、完全に新しい余裕式を閾値に使う後者のより大きな集合にも同じ下界が成立する。後者はAIGの元の領域の再定義ではない。

AIIの既存下界を \(Q_H(\beta)=\kappa(R_H(\beta)/(n_H+1))^{n_H}\) と書くと、さらに

\[
\max\{q_H(\beta),Q_H(\beta)\}\le\mu_H^{\mathrm{real}}(\mathcal N_{H,\beta})
\]

を証明した。既存のより強い情報を捨てず、2つの \(\kappa\) 値の大小関係は仮定しない。

## 6．20公開宣言と公理監査

すべて名前空間 `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`、共通prefix `p4Q2PZ37AIJ_`。

| 宣言末尾 | 種別・役割 |
| --- | --- |
| originalSingleLinkPartition_ge_exp | 定理。一リンク元Haar分配の下界 |
| expPower_eq | 定理。有限累乗の指数恒等式 |
| originalCrossingPartition_ge_expCount | 定理。元の交差Haar分配下界 |
| sourceVarianceFloor | 定義。AHN源分散の幾何的下界 |
| sourceVarianceFloor_pos | 定理。分散下界の正性 |
| sourceVarianceFloor_le_original | 定理。元分散との比較 |
| primitiveNegativeMargin | 定義。\(\delta\) |
| primitiveNegativeMargin_pos | 定理。正結合で余裕が正 |
| primitiveNegativeMargin_zero | 定理。零結合で余裕は零 |
| primitiveNegativeMargin_le_original | 定理。\(\delta\le\varepsilon\) |
| primitiveNegativeBallRadius | 定義。\(r\) |
| primitiveNegativeBallRadius_pos | 定理。新半径の正性 |
| primitiveNegativeBallRadius_le_original | 定理。\(r\le R\) |
| primitiveNegativeBall_subset_original | 定理。元の球同士の包含 |
| primitiveNegativeBall_fullMargin_stable | 定理。新球内で元の全余裕負性 |
| primitiveNegativeBall_mass_ge_explicit | 定理。新半径の真正Haar球下界 |
| originalTransfer_exists_primitiveNegativeHaarBall | 定理。元中心・正半径・負球・Haar下界を同時構成 |
| originalFullNegativeRegion_primitiveMass | 定理。元AIG全余裕領域への下界 |
| primitiveNegativeRegion_mass | 定理。別の \(-\delta\) 閾値領域への下界 |
| originalFullNegativeRegion_combinedMass | 定理。既存下界と新下界のmaxを保持 |

各宣言の `#print axioms` は実ログと一対一で一致し、全20件が標準3公理のみである。

## 7．到達範囲と残る障害

結論は各有限 \(H\)、各 \(\beta>0\) についての元の負領域の定量評価である。\(\delta\) や \(r\) の式を具体化したことを、\(H\) に一様な下界へ昇格させない。

正のtransfer境界・正負両符号のHaar領域・二殻、具体的な境界リンク値と数値符号表、\(\kappa\) の数値評価、体積一様な負値幅・半径・質量下界、uniform coercivity、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapは、本成果では未証明・未評価のまま残る。

本記録は定理のexact-source成功および実squashの一致確認後に、別のdocs-only PRで新規追加する。mainへのミラーも同じ記録Git blobを使用する。文書専用PRではStrict Leanを手動dispatchしない。
