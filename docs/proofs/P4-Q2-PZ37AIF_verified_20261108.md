# P4-Q2-PZ37AIF — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。mainは正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元の完全SU(2) Wilson一スラブ作用、両端halfweight、ZW signed source、空間積Haar、物理的transfer、型付き証明履歴、固定Lean/mathlibおよびworkflowを保持する。

## 1．Exact-source形式証明台帳

| 項目 | 確定値 |
| --- | --- |
| [AIF定理PR #6511](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6511) | MERGED |
| 継承したcanonical formal HEAD | `ea107dac1b534ef29dc1d6d862fc67a9d42e2f6b` |
| 最終exact-source HEAD | `1f854a0c4009e61e14b8776c4e03c3a037a76587` |
| 最終test-merge HEAD | `0dea7bde2809f43e901202ab664056c599068540` |
| 定理squash／定理統合時formal HEAD | `1e6d445dcc4a3bc98448f70a0fa460e4190b426b` |
| source・test-merge・squash共通Git tree | `d33bf6b9456bc7fac68656d9d815d4ecb996d647` |
| 最終Lean Git blob | `a3a0899a9688479e49b605c0051cb5050f489d89` |
| [最終exact-source CI #42467926115 attempt 4](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42467926115/attempts/4) | completed／SUCCESS |
| Changed Lean job | `128696231689`、completed／SUCCESS |
| 必須Lean step 17 | completed／SUCCESS |
| 独立completion receipt job | `128697280635`、completed／SUCCESS |
| Receipt実ログ | `exact_sha=1f854a0c4009e61e14b8776c4e03c3a037a76587 source_result=success run=42467926115 attempt=4` |
| Commit status context | `chatgpt-ci-receipt/PR Lean Fast Check`、SUCCESS |
| Strict Lean依存閉包 | **11,394／11,394 SUCCESS** |
| 主要宣言公理検証 | **20／20**、標準 `propext`・`Classical.choice`・`Quot.sound` のみ |
| 公理出力の欠落／重複／余剰 | 0／0／0 |
| sorryAx | **なし** |
| 変更Lean warning／error | **0／0** |
| 最終diagnostic artifact | `13613635129`、`lean-fast-check-log` |
| 最終artifact digest | `sha256:8b95481152d9e537b638b7e22998b91d65254ccb5b8e7a1e5036e1779c5d839b` |
| 新規Leanファイル | 1件・337行、17定理＋3定義 |
| 既存Lean／物理定義／仮定／workflow変更 | なし |

Leanは `v4.30.0-rc2`（CI実行バイナリcommit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`）、mathlibは `5450b53e5ddc75d46418fabb605edbf36bd0beb6` で固定。完成Leanログの全20公理出力を、最終ファイルの17定理・3定義および20個の出力命令と一対一で照合した。source/test-merge/squashの同一treeと定理統合後formalファイルの同一blobをGitHub MCPで読み戻して確認した。

[Lean4定理全文（検証済みsquash）](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1e6d445dcc4a3bc98448f70a0fa460e4190b426b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCrossingHaarTransferAverageV5_PZ37AIF.lean)

## 2．元の対象と今回の到達点

元の空間配置を \(A,B\in\mathcal C_H\)、元の積Haar確率測度を \(\mu_H\)、元の空間Wilson作用を \(W_H\)、元plaquette countを \(p_H\) とする。元ZWの物理的L2 sourceは既存の連続代表

\[
f_H(A)=\frac{W_H(A)-p_H}{2}
\]

とHaar-a.e.で一致する。元のtransferの正確な積分代表は

\[
t_{H,\beta}(B)
=\int f_H(A)K_{H,\beta}(A,B)\,d\mu_H(A).
\]

AHPの既証明定理を使い、この式を元の `decomposableOneSliceTransferIntegral H 2 beta f0 B` に、すべての右境界 \(B\) について接続する。任意に選んだL2代表の一点での値を仮定しない。

AIEで証明済みだったsource-only Haar–Laplace相関の負性を継承し、今回新しく、真正crossing正規化とFubiniを経由して**元の完全物理transferの負境界の存在**に到達する。

## 3．各リンクの真正Haar正規化

元の実装の相対holonomyは厳密に \(a^{-1}b\) である。\(G=SU(2)\)、元の正規化Haar確率測度 \(\nu\)、元Wilson energy \(E\) に対して

\[
z(\beta)=\int_G e^{-\beta E(g)}\,d\nu(g)
\]

を定義する。元energyの連続性、SU(2)のcompact性から被積分関数の可積分性を証明し、正の指数関数と非零Haar測度から

\[
\boxed{z(\beta)>0\qquad(\beta\in\mathbb R)}
\]

を得る。

固定された \(a\in G\) について、元の左Haar不変性と固定mathlibの `integral_mul_left_eq_self` を \(a^{-1}\) に適用し、

\[
\boxed{\int_G e^{-\beta E(a^{-1}b)}\,d\nu(b)=z(\beta)}
\]

を証明する。定数の独立性を仮定していない。

## 4．元の有限積Haarとcrossing partition

\(\mathcal E_H\) を元の空間リンク型、\(n_H=|\mathcal E_H|\) とする。元のcrossing kernelは全リンクの真の相対Wilson kernelの有限積である。

\[
K^{\mathrm{cross}}_{H,\beta}(A,B)
=\prod_{e\in\mathcal E_H}e^{-\beta E(A(e)^{-1}B(e))}.
\]

元の `Finset.univ.toList` による積を `Finset.prod_map_toList` で忠実に書き換え、元の `Measure.pi` に有限積Fubini `integral_fintype_prod_eq_prod` を適用する。前節の各リンク積分を代入して

\[
\boxed{
\int K^{\mathrm{cross}}_{H,\beta}(A,B)\,d\mu_H(B)
=Z_{\mathrm{cross},H}(\beta)
:=z(\beta)^{n_H}>0
}
\]

を全 \(H\)、全実数 \(\beta\)、全左境界 \(A\) について証明した。さらに既存の元kernel＝元crossing作用のBoltzmann指数の恒等式を介して、

\[
\int e^{-\beta S_H^{\mathrm{cross}}(A,B)}\,d\mu_H(B)
=Z_{\mathrm{cross},H}(\beta)
\]

も別の定理として記録した。新たな測度や独立模型を導入していない。

実装上、元kernelのリンク列は標準積型の `Fintype` を使い、元Haar測度は既存の `oneSlabHaarL2SpatialLinkFintype H := Fintype.ofFinite _` を使う。importされた文脈ではさらに別の既存Fintypeが推論され得る。これらを定義的に同一視せず、固定mathlibの `Subsingleton (Fintype Link)` から有限列挙構造の等式を証明し、`congrArg` で `Measure.pi` へ移送する。局所等式 `hMeasure` が元のHaar測度そのものとFubiniで使う表示の一致を保証する。さらに `Finset.prod_congr` と `Finset.mem_univ` により、両方の列挙が同じ全リンク集合を表すことを証明し、元kernelの積とFubiniで使う積の点ごとの等式 `hKernel` を得る。新しい有限列挙の補助インスタンスは設けない。

## 5．両端halfweightとFubini

完全作用とkernelは元のまま

\[
S_H(A,B)=W_H(A)/2+S_H^{\mathrm{cross}}(A,B)+W_H(B)/2,
\]

\[
K_{H,\beta}(A,B)
=e^{-\beta W_H(A)/2}\,K^{\mathrm{cross}}_{H,\beta}(A,B)\,e^{-\beta W_H(B)/2}
\]

である。右の重みを掛けると、点ごとに

\[
e^{\beta W_H(B)/2}K_{H,\beta}(A,B)
=e^{-\beta W_H(A)/2}K^{\mathrm{cross}}_{H,\beta}(A,B)
\]

となることを証明する。

符号付きのjoint integrand

\[
F(A,B)=f_H(A)e^{-\beta W_H(A)/2}K^{\mathrm{cross}}_{H,\beta}(A,B)
\]

は元のcompact積配置空間で連続である。これから \(\mu_H\otimes\mu_H\) に関する可積分性を明示的に証明した。`Integrable.integral_prod_right` は右境界での重み付きtransferの可積分性を与え、`integral_integral_swap` が正当な積分順序交換を与える。

したがって、要求された元の右境界平均

\[
\mathcal A_H(\beta)
=\int e^{\beta W_H(B)/2}t_{H,\beta}(B)\,d\mu_H(B)
\]

に対して

\[
\boxed{
\mathcal A_H(\beta)
=Z_{\mathrm{cross},H}(\beta)
\int f_H(A)e^{-\beta W_H(A)/2}\,d\mu_H(A)
}
\]

を証明した。

## 6．AIEとの接続・厳密負性・元負境界

元sourceの正確なcenteringから

\[
W_H(A)/2=f_H(A)+p_H/2.
\]

この等式を指数関数に代入し、真の積分の中から定数因子を取り出すと

\[
\boxed{
\mathcal A_H(\beta)
=Z_{\mathrm{cross},H}(\beta)e^{-\beta p_H/2}L_H(\beta),
\quad
L_H(\beta)=\int f_H(A)e^{-\beta f_H(A)}\,d\mu_H(A)
}
\]

となる。この恒等式自体は全実数 \(\beta\) で成立する。

AIEは元の真正Haar平均零と正のHaar分散から、全 \(\beta>0\) で \(L_H(\beta)<0\) を証明済みである。前節までで証明した二つの正因子を掛けて

\[
\boxed{\forall H\in\mathbb N,\ \forall\beta>0,\quad\mathcal A_H(\beta)<0}
\]

を得る。

もし元の全右境界で \(t_{H,\beta}(B)\ge0\) ならば、重み \(e^{\beta W_H(B)/2}>0\) により平均も非負となり、上式と矛盾する。よって

\[
\boxed{\forall H\in\mathbb N,\ \forall\beta>0,\quad
\exists B\in\mathcal C_H:\ t_{H,\beta}(B)<0}
\]

を形式証明した。既存の \(\beta_0=\log(3/2)/64>0\) を代入した平均の負性と負境界の存在も、それぞれ明示的な定理にした。

存在証明は平均の符号に基づく。具体的な負境界の座標と、その点での数値的transfer評価は未確定である。

## 7．宣言・imports・固定API

新規の主要宣言は次の20件（17定理・3定義）。すべて `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` のnamespaceにあり、各宣言に `#print axioms` を付している。別に元のSU(2)位相・測度構造、元Haar確率構造を既存証明から構成する `local instance` が7件ある。

| No. | 宣言 | 種別 | 完成ログの公理出力 |
|---|---|---|---|
| 1 | `p4Q2PZ37AIF_originalSingleLinkPartition` | 定義 | `propext, Classical.choice, Quot.sound` |
| 2 | `p4Q2PZ37AIF_originalSingleLinkPartition_integrable` | 定理 | `propext, Classical.choice, Quot.sound` |
| 3 | `p4Q2PZ37AIF_originalSingleLinkPartition_pos` | 定理 | `propext, Classical.choice, Quot.sound` |
| 4 | `p4Q2PZ37AIF_originalSingleLinkKernel_haarIntegral` | 定理 | `propext, Classical.choice, Quot.sound` |
| 5 | `p4Q2PZ37AIF_originalCrossingPartition` | 定義 | `propext, Classical.choice, Quot.sound` |
| 6 | `p4Q2PZ37AIF_originalCrossingPartition_pos` | 定理 | `propext, Classical.choice, Quot.sound` |
| 7 | `p4Q2PZ37AIF_originalCrossingKernel_haarIntegral` | 定理 | `propext, Classical.choice, Quot.sound` |
| 8 | `p4Q2PZ37AIF_originalCrossingBoltzmann_haarIntegral` | 定理 | `propext, Classical.choice, Quot.sound` |
| 9 | `p4Q2PZ37AIF_originalWeightedCrossing_jointIntegrable` | 定理 | `propext, Classical.choice, Quot.sound` |
| 10 | `p4Q2PZ37AIF_originalKernel_rightWeightCancellation` | 定理 | `propext, Classical.choice, Quot.sound` |
| 11 | `p4Q2PZ37AIF_originalRightWeightedTransfer_eq_crossingIntegral` | 定理 | `propext, Classical.choice, Quot.sound` |
| 12 | `p4Q2PZ37AIF_originalRightWeightedTransfer_integrable` | 定理 | `propext, Classical.choice, Quot.sound` |
| 13 | `p4Q2PZ37AIF_originalRightWeightedTransferAverage` | 定義 | `propext, Classical.choice, Quot.sound` |
| 14 | `p4Q2PZ37AIF_originalRightWeightedTransferAverage_eq_crossingPartition` | 定理 | `propext, Classical.choice, Quot.sound` |
| 15 | `p4Q2PZ37AIF_originalLeftHalfweightSource_eq_Laplace` | 定理 | `propext, Classical.choice, Quot.sound` |
| 16 | `p4Q2PZ37AIF_originalRightWeightedTransferAverage_eq_Laplace` | 定理 | `propext, Classical.choice, Quot.sound` |
| 17 | `p4Q2PZ37AIF_originalRightWeightedTransferAverage_neg` | 定理 | `propext, Classical.choice, Quot.sound` |
| 18 | `p4Q2PZ37AIF_originalTransfer_exists_negativeBoundary` | 定理 | `propext, Classical.choice, Quot.sound` |
| 19 | `p4Q2PZ37AIF_originalFixedRightWeightedTransferAverage_neg` | 定理 | `propext, Classical.choice, Quot.sound` |
| 20 | `p4Q2PZ37AIF_originalFixedTransfer_exists_negativeBoundary` | 定理 | `propext, Classical.choice, Quot.sound` |

直接importsは4件：

- `MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSourceHaarLaplaceAnticorrelationV5_PZ37AIE`
- `Mathlib.MeasureTheory.Group.Integral`
- `Mathlib.MeasureTheory.Integral.Pi`
- `Mathlib.Tactic`

固定mathlib SHA `5450b53e5ddc75d46418fabb605edbf36bd0beb6` の実ファイルを読み、以下のsignatureを照合した：

- `MeasureTheory.integral_mul_left_eq_self` — 元の左Haar不変性による1リンク正規化。
- `MeasureTheory.integral_exp_pos` — 可積分な実指数関数の非零測度上の厳密正積分。
- `Finset.prod_map_toList` — 元link listの積と同じfinite setの積の一致。
- `MeasureTheory.integral_fintype_prod_eq_prod` — 元の有限積Haarの積分分解。
- `Fintype.subsingleton` と `Subsingleton.elim` — 元Haar側とFubini文脈の有限列挙構造の等式。`congrArg` で元の `Measure.pi` の等式に移送。
- `Finset.prod_congr` と `Finset.mem_univ` — 元kernel側とFubini文脈の全リンク有限集合の一致に基づく、点ごとの積の一致。
- `MeasureTheory.Integrable.integral_prod_right` — 元のjoint可積分性から右境界平均の可積分性。
- `MeasureTheory.integral_integral_swap` — joint可積分性を前提にするBochner Fubini。

固定APIの一次資料：

- [Group/Integral.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Group/Integral.lean)
- [Integral/Pi.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Pi.lean)
- [Integral/Prod.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Prod.lean)
- [Integral/Bochner/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean)
- [Finset/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean)
- [Fintype/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/Fintype/Defs.lean)
- [Constructions/Pi.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Constructions/Pi.lean)

既存側ではOneSlabKernel、OneSlabHaarL2Transfer、AGNの正確なsource centering、AHPの元physical transfer積分代表、AIEの厳密負性を確認した。新規Lean全文、imports、依存signature、全公理出力と独立receiptを照合した。

## 8．検証履歴

初回source `269c70f726e5614a06e3c245131f0426aac72747` の [CI #42463956617](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42463956617) はcompleted／FAILURE。変更Leanに根本エラー2件と、それに伴う下流warning7件があった。

| 箇所 | 構造的原因 | 修正 |
|---|---|---|
| 初回127行 | 汎用 `rw [integral_fintype_prod_eq_prod]` の積分パターンが元Cfgの積分へ照合されず、リンク添字・座標関数族の対応が確定しなかった | 元 `Link` と `G` に型を固定し、元測度族 `μ := fun _ : Link => nu` と各リンク関数を明示した定理項をcalc内で適用 |
| 初回144行 | `muH.prod` がlocal notationの展開を経ず、修飾識別子として読まれた | `Measure.prod muH muH` で元積測度を明示 |

後者がjoint integrability定理の型のelaborationを壊したため、依存する平均・存在定理の診断に `sorryAx` が現れた。ソース中に `sorry` を書いたものではない。根本2箇所を修正し、型付きの元測度・元関数を指定した。定理の数学的条件や元の物理定義、20宣言の目的、imports、toolchain、workflowは変更していない。修正版sourceは `349d8c635410122accc03f7989b2bf6fd0cc5181`、321行、Git blob `ae7bcd5c6c0cc89a45e72e4a62c97231c8f2f18e`。

修正版 [CI #42464461277 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42464461277/attempts/1) は、elan配布バイナリの取得がHTTP504で5回連続して失敗し、環境準備step12で停止した。Lean検証step17はskippedであり、この試行を修正版証明の成否判断に用いていない。同じsource HEADを保持してGitHub MCPから失敗ジョブを再実行した。workflowや固定toolchainは変更していない。

[同attempt 2](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42464461277/attempts/2) もcompleted／FAILURE。elan配布バイナリのHTTP504が全5回の内部再試行で発生し、step12失敗・Lean step17 skippedという同一の環境障害だった。同一sourceに対する失敗ジョブを再度実行した。

[同attempt 3](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42464461277/attempts/3) はelan導入step12に成功したが、固定Lean `v4.30.0-rc2` 本体の取得がHTTP504で全5回失敗し、バージョン確認step13で停止した。Lean step17はskipped。同一sourceのまま失敗ジョブを再実行した。

同CIの [attempt 4](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42464461277/attempts/4) はツールチェーン導入を通過してLeanを実行し、completed／FAILUREとなった。残る根本エラーは1件、変更Lean warningは0件だった。元kernelの全リンク積は既存の積型 `instFintypeProd` による `Finset.univ` を使う一方、新規local instanceの `Fintype.ofFinite _` は別の列挙を選ぶため、calcの式が定義的に一致しなかった。local instanceを `by classical infer_instance` に替える候補を作成した。元の型・測度・kernel・仮定・定理statementは不変。独立レビューでもインスタンスの整合性を確認した。

この補助instance経由の候補sourceは `219f22f0f02214dbd400a65ae74fa094bae5c439`、323行、Git blob `68bb5f46f4dac3ad52580e53604d184b6fd754e9`。[CI #42466484813](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42466484813) はcompleted／FAILUREで、同じcalcの有限列挙不一致が1件残った。変更Lean warningは0件。補助instance経由の定義的等しさは採用しなかった。

元Haarの実定義と固定mathlibの `Measure.pi` を再確認し、両者に取り込まれたFintype表現の違いを明示的な等式で処理した。新規リンクFintype instanceを削除し、元HaarのFintypeとFubini側で推論されるFintypeの等式を `Subsingleton.elim` で証明、`congrArg` で元積Haar測度の等式 `hMeasure` に移送してからFubiniを適用する候補を作成した。この候補sourceは `425a459c4f6a74d30879c3ba6862b815f2b0ed03`、329行、Git blob `382c9494f98719507521975c2ca6dd92cef02b95`。

[CI #42467274347](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42467274347) はcompleted／FAILURE、変更Lean error1・warning0。`hMeasure` に診断はなく、残ったcalcの診断は、import経由で推論された既存 `p4Q2PZ37ABD2_linkFintype` と元kernelの積型Fintypeとの全リンク有限集合の不一致だった。そこで、元kernelの有限積を `Finset.prod_congr` で比較し、両側の `univ` の等しさを `Finset.mem_univ` から明示的に証明する局所等式 `hKernel` を追加した。これにより、測度側と被積分関数側の両方を命題的等式でFubiniの表示に接続する。修正は独立レビューでも確認した。

最終検証sourceは `1f854a0c4009e61e14b8776c4e03c3a037a76587`、337行、Git blob `a3a0899a9688479e49b605c0051cb5050f489d89`。17定理・3定義・20件の公理出力対象を保持する。

この候補の [CI #42467926115 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42467926115/attempts/1) は固定Lean本体のHTTP504取得障害により全5回の内部再試行が失敗し、step13失敗・Lean step17 skippedで終了した。同じsource HEADを保って失敗ジョブを再実行した。

[同attempt 2](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42467926115/attempts/2) も固定Lean本体のHTTP504が全5回続き、step13失敗・Lean step17 skippedで終了した。同じsourceで再度実行した。

[同attempt 3](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42467926115/attempts/3) はelan配布バイナリのHTTP504が全5回続き、step12失敗・Lean step17 skippedで終了した。同じsourceで失敗ジョブを再実行した。

最終exact-source [CI #42467926115 attempt 4](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42467926115/attempts/4) はcompleted／SUCCESS。Changed Lean job `128696231689` と必須Lean step17はいずれもcompleted／SUCCESSであり、最終AIFモジュールは依存閉包の11394番目として実際にBuiltされ、`Build completed successfully (11394 jobs).` を確認した。20件の実際の公理出力はすべて標準3公理のみで、`sorryAx` はなく、変更Lean warning／errorは0／0。独立receipt job `128697280635` の実ログは、同じsource HEAD・run・attempt4・`source_result=success` を記録し、対応するcommit statusもSUCCESSだった。

定理PR #6511を検証済みHEADのlease付きでsquash mergeし、squash `1e6d445dcc4a3bc98448f70a0fa460e4190b426b` のtree `d33bf6b9456bc7fac68656d9d815d4ecb996d647` がsourceとtest-mergeのtreeに完全一致することを確認した。元のfailed CI、途中候補の公理出力、Leanがスキップされた環境障害、receipt jobの成功だけを証明成功の根拠にしていない。

最終337行全文の独立数学レビューでは、元の相対holonomy、有限積Haar、`hMeasure` と `hKernel` による表示の整合性、正規化の正値性、元L2 sourceのa.e.橋渡し、両halfweight、Fubiniの前提と交換方向、source centeringの係数、全正結合と固定beta0の負境界存在を点検し、数学的な問題を認めなかった。独立に再計算したGit blobも最終候補と一致した。Haar担当と物理/Fubini担当の独立調査とも整合した。独立レビューと実際のLeanコンパイル成功は別々に確認している。


## 9．残る課題

今回解決したのは、元の全正結合における**負の物理的transfer境界の存在**である。以下は引き続き未証明として保持する。

- 元固定結合における正のtransfer境界と、正負両方を組み合わせた二殻。
- 具体的な負境界の座標・有理Haar表による数値符号証明書。
- 体積一様のcoercivity。
- Hamiltonian spectral gap。
- 連続体4次元Yang–Mills質量ギャップ。

次の候補は、今回の存在結果を元transferの連続性や既存の真正Haar区間証明書へ接続し、有限体積での負領域の定量化を進めること。正境界の存在や体積一様性を仮定せず、別の研究課題として評価する。

本記録はcanonical formalへの新規appendのみとし、同一Git blobをmainへdocs-onlyで同期する。既存Leanとworkflowを変更せず、docs-only PRではStrict Leanを手動実行しない。
