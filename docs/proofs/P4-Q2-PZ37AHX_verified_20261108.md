# P4-Q2-PZ37AHX — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の形式定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。GitHub `main` は正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元のSU(2)完全Wilson一スラブ作用、左右空間halfweight、元ZW Gauss-law signed source、空間積Haar、型付き証明履歴、root、固定Lean/mathlib、workflowを保持。

## 1．Exact-source証明台帳

| 項目 | 検証済みの結果 |
| --- | --- |
| [AHX定理PR #6487](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6487) | **MERGED** |
| 継承元AHW正式記録HEAD | `202f0302c84f3c0a16adc90f08ab66bb38151b6f` |
| 最終exact-source HEAD | `776d2ddd701a18d2ab5b0b45f31f4866c5ca2e98` |
| exact test-merge HEAD | `d05d0d907e5725e8a8ae47f49228a731d6a1ac83` |
| 定理squash HEAD | `17781514f83b0ed84c417e9d2c7a5ee56bfea4bb` |
| source／test-merge／squash共通Git tree | **`f62ff2bccd5e8d457d3c4a28e9d744cb1a20c697` 完全一致** |
| [最終exact-source CI #42435517841](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42435517841) | **completed／SUCCESS** |
| Changed Lean job・Lean step | `128593392836` — **completed／SUCCESS** |
| 独立completion receipt job | `128594359306` — **completed／SUCCESS** |
| exact-head receipt context | `chatgpt-ci-receipt/PR Lean Fast Check` — **success** |
| Strict Lean依存閉包 | **11,386／11,386 SUCCESS** |
| 新規定理の公理監査 | **19／19**、`propext`・`Classical.choice`・`Quot.sound` のみ |
| `sorryAx` | **なし** |
| 変更Lean warning／error | **0／0** |
| 成功CIログartifact | `13599308269`、`lean-fast-check-log` |
| 新規Leanファイル | **1件・405行**、既存ファイル変更なし |
| 新規Lean blob | `459c754ffbd9c014505dd46d61bd594419b6fed7`、最終全文readback一致 |

固定環境：Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。成功ログの最終結果は `Build completed successfully (11386 jobs).`。新規全19定理の出力を個別に確認した。既存依存ファイルの歴史的warningは今回の変更ファイルのwarningと区別する。

## 2．CLOSED — 全非負実数での指数関数三次剰余

元のAHPで証明済みの
\[
0\le e^{-x}-1+x\le x^2/2\qquad(x\ge0)
\]
を再使用する。二次Taylor多項式との差
\[
r(x)=1-x+x^2/2-e^{-x}
\]
はAHPの上側不等式から非負であり、その微分は
\[
r'(t)=e^{-t}-1+t\le t^2/2=(t^3/6)'.
\]
固定mathlibの `image_le_of_deriv_right_le_deriv_boundary` により、初期値 \(r(0)=0\) を持つ両関数を比較して
\[
\boxed{0\le1-x+x^2/2-e^{-x}\le x^3/6\quad(x\ge0)}
\]
を形式証明した。\(x\le1\) のような小ささの仮定も、誤差への指数因子も追加しない。`x=0` も同一の定理に含まれる。微分比較の領域は固定版で `Ico 0 x`、終点評価は `Icc 0 x` であり、区間の端点条件を型付きに確認した。

## 3．CLOSED — 元の完全Boltzmann核と正確な二次係数

元の完全一スラブ作用
\[
S_H(A,B)=\tfrac12W_H(A)+S_H^{\mathrm{cross}}(A,B)+\tfrac12W_H(B)
\]
と、既存の同一核
\[
K_{H,\beta}(A,B)=e^{-\beta S_H(A,B)}
\]
を使う。既存の真正有限体積上界を \(C_H\) と書くと、元の定理で
\[
0\le S_H(A,B)\le C_H
\]
が成立している。第2節へ \(x=\beta S_H(A,B)\) を代入し、全 \(\beta\ge0\) に対して
\[
\left|K_{H,\beta}(A,B)-\left(1-\beta S_H(A,B)
+\frac{(\beta S_H(A,B))^2}{2}\right)\right|
\le\frac{(\beta S_H(A,B))^3}{6}
\le\frac{(\beta C_H)^3}{6}
\]
を証明した。

元の連続sourceは
\[
f_H(A)=(W_H(A)-p_H)/2,
\quad V_H=\int f_H(A)^2\,d\mu_H(A)>0.
\]
AHPの真正Haar平均ゼロ、AHRの真正一次モーメント、AHWの真正二次モーメントを使用：
\[
\int f_H\,d\mu_H=0,\qquad
\int f_H(A)S_H(A,B)\,d\mu_H(A)=V_H,
\]
\[
\int f_H(A)S_H(A,B)^2\,d\mu_H(A)
=(3p_H+W_H(B))V_H.
\]
二次多項式とsourceの積の可積分性を元のコンパクト配置空間上の連続性から証明し、積分を分解して
\[
\boxed{Q_{H,\beta}(B)=
-\beta V_H+\frac{\beta^2}{2}(3p_H+W_H(B))V_H}
\]
を厳密に得た。二次モーメントは \(\int f_H S_H^2\) であり、\(\int f_H^2 S_H\) ではない。元の左halfweightから出る一次係数は `-V_H` で、係数2の重複はない。

## 4．CLOSED — 真正signed Haar剰余とtransferの等式

剰余は名前だけの誤差変数ではなく、次の元のHaar積分として定義：
\[
R_{3,H}(\beta,B)=\int f_H(A)
\left[K_{H,\beta}(A,B)-
\left(1-\beta S_H(A,B)+\frac{(\beta S_H(A,B))^2}{2}\right)\right]d\mu_H(A).
\]
元の物理的L2 sourceと連続代表の既証明Haar-a.e.一致を使い、実際の
`decomposableOneSliceTransferIntegral` に対して
\[
\boxed{T_{H,\beta}(B)=
-\beta V_H+\frac{\beta^2}{2}(3p_H+W_H(B))V_H+
R_{3,H}(\beta,B)}
\]
を証明した。この等式自体は任意の実 \(\beta\) に成立する。以後の誤差評価は \(\beta\ge0\) で成立する。

元sourceの真正Haar L1質量
\[
M_H=\int|f_H(A)|\,d\mu_H(A)
\]
とAEVの既証明signed積分変動評価を用い、
\[
\boxed{|R_{3,H}(\beta,B)|
\le E_{3,H}(\beta):=\frac{(\beta C_H)^3}{6}M_H
\le\frac{(\beta C_H)^3}{6}\frac{p_H}{2}}
\]
を全元境界 `B` に対して証明。最後の不等式はAHJの \(M_H\le p_H/2\) による。絶対値は誤差制御にのみ使い、元sourceや元transferを正部分や絶対値sourceへ置換していない。

旧AHPの誤差予算 \(E_{2,H}(\beta)=(\beta C_H)^2M_H/2\) との正確な関係も証明：
\[
\boxed{E_{3,H}(\beta)=\frac{\beta C_H}{3}E_{2,H}(\beta).}
\]
従って \(\beta C_H\le3\) なら誤差幅自体は旧予算以下となる。ただし二つのTaylor近似の中心は異なるため、旧区間への集合包含はここでは主張しない。

## 5．CLOSED — 二側区間と条件付き固定結合符号証明書

同じ元transferについて
\[
\boxed{Q_{H,\beta}(B)-E_{3,H}(\beta)
\le T_{H,\beta}(B)\le
Q_{H,\beta}(B)+E_{3,H}(\beta)}
\]
を証明した。これは全 \(\beta\ge0\) に有効であり、既存の元固定結合
\[
\beta_0=\log(3/2)/64>0
\]
を直接代入した二側区間も形式化済み。

**負符号の十分条件：**
\[
\frac{\beta^2}{2}(3p_H+W_H(B))V_H+E_{3,H}(\beta)
<\beta V_H
\quad\Longrightarrow\quad T_{H,\beta}(B)<0.
\]

**正符号の十分条件：**
\[
\beta V_H+E_{3,H}(\beta)
<\frac{\beta^2}{2}(3p_H+W_H(B))V_H
\quad\Longrightarrow\quad T_{H,\beta}(B)>0.
\]
両条件は独立した定理であり、それぞれ固定 \(\beta_0\) に特殊化した真正transferの定理もある。**いずれかの具体的境界で条件が成立したという数値証明は、このAHXには含まれない。** 区間が0をまたぐ場合、この証明書だけでは符号は確定しない。

## 6．全文検証と固定API

変更Lean全文、imports、AHP・AHR・AHS・AHW2の依存定理、元AEV signed積分変動補題、固定mathlibの[MeanValue API](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Calculus/MeanValue.lean)を照合した。元固定結合の閉形式と正性もADCの定義本体で確認。独立した全文レビューでも数学・仕様上の修正必須事項は見つからなかった。

初回CI [#42435052492](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42435052492) は19定理・11,386ジョブともに成功したが、新規スカラー微分証明に `linter.unnecessarySeqFocus` 警告が4件あった。原因は、各段階で単一ゴールしか残らない `convert`／`simp`／`ring` を、複数ゴール用の `<;>` で連結したこと。対応する2か所を通常の逐次tacticへ修正した。**定理文・仮定・物理定義・importsを変更せず、警告を無効化する設定も追加していない。**

修正HEADに対する最終CI #42435517841のworkflow、Changed Lean job、Lean step、独立receiptがすべて完了・成功した後に確認。新規19定理すべて標準公理のみ、`sorryAx`なし、変更warning/error 0/0、最終全文readback一致を得た。さらにsource／test-merge／squashのGit tree一致を確認して統合した。

## 7．OPEN — 次段AHY

元の作用の構造をさらに使い、全体上界 `C_H^3 M_H` より精密な、真正Haar積分の三次剰余予算を研究する。候補は元sourceの絶対値を重みとする \(\int |f_H(A)|S_H(A,B)^3\,d\mu_H(A)\) の厳密評価、または境界に依存する作用上界と高次の相関消去。これは次の研究対象であり、現段階の証明済み成果へ繰り入れない。

未証明の課題：元固定結合での真正transferの具体的符号・正負二殻、体積Hに一様なcoercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップ。有限HでのTaylor誤差評価をこれらと同一視しない。

[AHX Lean定理全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/17781514f83b0ed84c417e9d2c7a5ee56bfea4bb/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSecondOrderTaylorTransferV5_PZ37AHX.lean)

本記録を新規docs-onlyファイルとしてformalへ追記し、同一Git blobをmainへ文書同期する。文書PRではStrict Leanを起動しない。
