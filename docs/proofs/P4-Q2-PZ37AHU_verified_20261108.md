# P4-Q2-PZ37AHU — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の形式定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。GitHub `main` は文書ミラー。運用原則は append-only／tighten-only／overwrite-forbidden／same-root。元の完全 SU(2) 一スラブ Wilson 作用・核・左右空間halfweight、元ZW Gauss-law signed source、真正空間積Haar、ゲージ作用、元Type値証拠履歴、固定toolchain・workflowは変更していない。

## 1．Authoritative exact-source 形式証明台帳

| 項目 | 確認済み |
| --- | --- |
| [AHU定理PR #6478](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6478) | **MERGED** |
| 継承元 AHT formal HEAD | `8c1f8f1d6fd4f67b2ca67389302ee4d88ae3d563` |
| 初回source HEAD | `f53249002910681fe3bec242b15d25c32528bde1` |
| 最終source HEAD | `acb4c810b32d70a0687dd2f8400198bc79c80a88` |
| test-merge HEAD | `14898821dae793d4e81038aece4a0be0632b5bbb` |
| squash定理正本HEAD | `d3de3abac90a95c9eb1ef950e4d6128e1eda6921` |
| source／test-merge／squash Git tree | **`48ee7f110ead42d88a249f6834c1183b3c7e8adc` 完全一致** |
| [最終CI #42426417148](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42426417148) | **completed / SUCCESS** |
| Changed Lean job | `128565547662` — **SUCCESS** |
| 独立completion receipt job | `128566815175` — **SUCCESS** |
| Lean依存閉包 | **11,382 / 11,382 SUCCESS** |
| AHU新規定理 `#print axioms` | **5件**、`propext`／`Classical.choice`／`Quot.sound` のみ |
| `sorryAx` | **なし** |
| 変更AHU Lean warning／error | **0／0** |
| CI生ログartifact | `13595687337`、`lean-fast.log` 回収・全文監査 |
| 変更対象 | 新規AHU Leanファイル1件、229行。既存Lean／物理定義／root／workflow／pins不変更 |

固定環境：Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。最終実ログ末尾 `Build completed successfully (11382 jobs).`。AHU新規5宣言の公理監査はすべて上記標準公理のみ。

## 2．CLOSED — 任意の真正ゲージ不変重みのone-link Haar厳密期待値

任意の連続で空間頂点ゲージ不変な重み \(\varphi: \mathrm{Cfg}_H\to\mathbb{R}\) と、真正右境界 \(B\)、真正リンク \(e\) について、既存PTの **ゲージWard Haar恒等式** は

\[
\int \varphi(A)E((A_e)^{-1}B_e)\,d\mu_H(A)
=\int \varphi(A)E((A_e)^{-1})\,d\mu_H(A)
\]

を証明している。既存SU(2)真正中心 \(z=-I\) と、既証明の真正Wilson一リンクエネルギー反転

\[
E(gz)=2-E(g)
\]

を再使用し、右境界のリンク値を \(z\) に取る。PTの両辺は等しい一方、中心反転により左辺は

\[
2\int\varphi\,d\mu_H-\int\varphi(A)E((A_e)^{-1})\,d\mu_H.
\]

したがって

\[
\boxed{
\int \varphi(A)E((A_e)^{-1}B_e)\,d\mu_H(A)
=\int\varphi(A)\,d\mu_H(A)
}
\]

が元の真正Haar測度上で厳密に成立する。仮想独立posterior、リンク独立を仮定するWard置換、元作用の変更はいずれも不要。

## 3．CLOSED — 完全crossingの真正Haar厳密値

元PWの真正完全crossing有限和（繰り返しを含め元の全リンク）：

\[
S_H^{\mathrm{cross}}(A,B)
=\sum_{e\in\mathrm{Link}_H} E((A_e)^{-1}B_e)
\]

に、項別可積分性と上のone-link Ward証明を適用。元AHIの既証明 \(\#\mathrm{Link}_H=p_H\) を使い

\[
\boxed{
\int\varphi(A)S_H^{\mathrm{cross}}(A,B)\,d\mu_H(A)
=p_H\int\varphi(A)\,d\mu_H(A)
}
\]

を証明した。これは固定有限 \(H\) と任意の元右境界 \(B\) に対する真正SU(2)主張である。

## 4．CLOSED — AHTの未評価混合相関と二次Wilsonモーメントの具体化

AHTでは元物理Gauss-law sourceの真正連続代表 \(f_H\) の二乗が連続・空間ゲージ不変であると既証明。\(\varphi=f_H^2\) を代入し、AHN既証明の真正 source Haar二次モーメント \(V_H\) について

\[
\boxed{
Y_H(B)
:=\int f_H(A)^2S_H^{\mathrm{cross}}(A,B)\,d\mu_H(A)
=p_H V_H
}
\]

を形式証明した。したがってAHTの厳密アフィン切片は

\[
I_{2,H}=M_{3,H}+3p_HV_H,
\qquad M_{3,H}=\int f_H(A)^3\,d\mu_H(A),
\]

となる。AHS・AHTの元完全一スラブ作用を保持し、

\[
\boxed{
M_{2,H}(B)=M_{3,H}+(3p_H+W_H(B))V_H
}
\]

を形式証明した。\(V_H>0\) はAHNの既証明であり、AHTの厳密単調性とも矛盾しない。

## 5．Lean4全文診断と修正

初回HEAD `f53249002910681fe3bec242b15d25c32528bde1` の [CI #42425926872](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42425926872) は1件失敗。実ログartifact `13595149777` を回収し、AHU全文・imports・元PW／PT／AHS／AHTの定義・固定mathlibの `Finset` APIを照合した。

失敗の構造は、元PWとAHUで同じ `Link` 型に別々の `Fintype` 列挙を局所的に使用していたため、元PWの有限和とAHUの有限和が**定義上の等式（definitional equality）としては一致しない**こと。証明済みの真正PW有限和は変更せず、元AHRの既存実装様式に合わせて `Finset.sum_congr` による**外延的な有限集合一致**を明示した。後続定理の一時的な `sorryAx` 診断は、この唯一の未解決ゴールの波及であり、追加公理は採用していない。

修正HEAD `acb4c810b32d70a0687dd2f8400198bc79c80a88` はCI #42426417148で11,382件成功、5定理すべて標準公理のみ、`sorryAx`なし、変更警告・エラー0／0。独立completion receipt SUCCESSの後、PRをsquashマージし、全Git tree一致を独立確認した。

## 6．OPEN — 次段AHVの厳密な課題

真正 source 三次Haarモーメント \(M_{3,H}\) の厳密値・符号は今回まだ確定していない。

まず既証明の真正点wise上界 \(|f_H(A)|\le p_H/2\) と非負の \(f_H(A)^2\) を使えば、元Haar上での候補評価

\[
-\frac{p_H}{2}V_H\le M_{3,H}\le \frac{p_H}{2}V_H
\]

を追加Lean定理として構成できる。さらに真正**偶数周期**上の \(Z_2\) 空間中心twistで全空間プラケット文字が同時反転できるかを検証する。実際のtwistの構成、全プラケット変換、積Haarの保存を元Typeで証明できた場合のみ \(M_{3,H}=0\) を主張する。これらはAHUで未証明の研究対象である。

元固定結合 \(\beta_0=\log(3/2)/64\) での真正transfer符号、二符号殻、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは引き続き**未証明**。

[AHUの真正Lean定理全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d3de3abac90a95c9eb1ef950e4d6128e1eda6921/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalGaugeWardCenterMixedHaarExactV5_PZ37AHU.lean)

本記録は新規docs-only Markdown追補であり、既存Lean・README・ROADMAP、元物理定義、公開root、pins、workflowを変更しない。文書専用PRでStrict Leanは起動しない。
