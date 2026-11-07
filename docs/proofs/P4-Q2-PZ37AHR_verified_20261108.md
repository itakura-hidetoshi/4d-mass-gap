# P4-Q2-PZ37AHR — 正式証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

正本は `formal/real-hilbert-uniform-coercive-strong-limit`。GitHub `main` は文書ミラー。
運用：append-only／tighten-only／overwrite-forbidden／same-root。元SU(2)完全Wilson one-slab核、両端空間halfweight、元ZW Gauss-law physical source、元積Haar測度、型付き証拠・履歴は不変更。

## 1．唯一の定理正本・exact-source検証

| 項目 | 実際の結果 |
| --- | --- |
| [AHR定理PR #6469](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6469) | **MERGED** |
| 継承元AHQ canonical HEAD | `64b20b8a0508bdb5e8623a5d427a8f10697c56dd` |
| 最終AHR source HEAD | `a92cc9fc54f6bc0eda0d9d22a0b46238ad9ee9dc` |
| test-merge SHA | `e6334b120093f976b092849461525b10b12e2b0b` |
| AHR定理squash／定理正本HEAD | `c3e6faec3b44981fae5c5b993ed2b8ee9115de5f` |
| source／test-merge／squashの共通Git tree | `480cbffe26bf32d429a42ccd09c8169a813ebca4` |
| [最終exact-source CI #42418693589](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42418693589) | **completed / SUCCESS** |
| Changed Lean job | `128542244149` completed / SUCCESS |
| 独立MCP completion receipt | `128543441954` completed / SUCCESS |
| Lean依存閉包 | **11,379 / 11,379 SUCCESS** |
| AH R新規定理数／`#print axioms` | **10件**、`propext`・`Classical.choice`・`Quot.sound` のみ |
| `sorryAx` | なし |
| 変更AHR Lean warning／error | **0 / 0** |
| 実ログartifact | `13592297678`、`lean-fast.log`を回収して確認 |
| 変更対象 | 新規AHR Leanモジュール1ファイルのみ。元物理定義／旧Lean／root／workflow／pins不変更 |

固定Lean：`v4.30.0-rc2`、固定mathlib：`5450b53e5ddc75d46418fabb605edbf36bd0beb6`。実ログの最終行 `Build completed successfully (11379 jobs).` を確認し、AHRの10件の公理依存はすべて標準3公理のみ、`sorryAx`なし、変更ファイルのwarning/errorは0/0であることを独立に検証した。GitHub MCPでsource・test-merge・squashのGit tree完全一致を確認した。

## 2．CLOSED — 元プラケットcharacterと一リンクcrossingの真正Haar直交性

真正有限体積 \(H\)、元空間プラケット \(p\)、時間crossingリンク \(e\)、元空間右境界 \(B\) を任意に取る。元の4本の互いに異なるプラケット辺から、\(e\) と異なる辺 \(t\) を取り出す。既存PY3によるこの幾何学的事実は最小周期 \(H=0\) でも証明済み。

元PUのSU(2)中心元 \(-I\) による辺 \(t\) の反転 \(\mathrm{Flip}_t\) は真正積Haar測度を保存する。元PV/PY3によりプラケットcharacter \(\chi_p\) はその反転で負になるが、元PU2により \(e\ne t\) で時間crossingのWilsonエネルギーは不変になる。したがって、符号反転積分はそれ自身の負数に等しく、

\[
\boxed{
\int_{\mathrm{Cfg}_H}
\chi_p(A)\,E\bigl(A(e)^{-1}B(e)\bigr)\,d\mu_H(A)=0.
}
\]

これは**元の独立な積Haar参照測度について証明した**ものであり、相互作用を含むWilson Gibbs posteriorの独立性を新たに仮定・宣言したものではない。

## 3．CLOSED — 全crossing和と元Gauss-law centered sourceへの型付き接続

PWの既証明の元完全crossing作用の有限和表現

\[
S_H^{\rm cross}(A,B)
=\sum_{e\in\mathrm{Link}_H} E(A(e)^{-1}B(e))
\]

を有限和のBochner積分と交換し、各項の消滅を合成した。続いて元PW2の空間Wilson作用

\[
W_H(A)=p_H-\Phi_H(A),
\qquad
\Phi_H(A)=\sum_{p\in\mathrm{Plaq}_H}\chi_p(A)
\]

と、元AGNのsource恒等式

\[
f_H(A)=\frac{W_H(A)-p_H}{2}=-\frac{\Phi_H(A)}2
\]

を、同じ元空間carrierおよび局所`Fintype`差を明示的に解消して繋いだ。従ってAHPの真正符号付きcrossing相関は、任意の元右境界Bで

\[
\boxed{
X_H(B)=\int f_H(A)S_H^{\rm cross}(A,B)\,d\mu_H(A)=0.
}
\]

AHQの \(|X_H(B)|\le p_H^2/2\) を**元source・元measureを変えずに等式へtighten**した。

## 4．CLOSED — 元Wilson transferのsharpな一次評価と有限体積小結合負符号

元AHPの厳密一次展開で \(\int f_H S_H\,d\mu_H=V_H+X_H(B)\) が証明済み。AHRでは \(X_H(B)=0\) が成立するので

\[
\boxed{
\bigl|T_{H,\beta}(B)+\beta V_H\bigr|
\le E_H(\beta),
\qquad
E_H(\beta)=\frac{(\beta C_H)^2}{2}M_{\rm src,H}
\quad(\beta\ge0).
}
\]

ここで \(C_H\) は元完全one-slab作用の実際の証明済みglobal budgetであり、\(M_{\rm src,H}=\int|f_H|d\mu_H\)、\(V_H=\int f_H^2d\mu_H>0\) は真正Gauss-law sourceの同じ参照Haarモーメント。AHN真正幾何で証明した \(F_H\le V_H\) から

\[
T_{H,\beta}(B)\le-\beta F_H+E_H(\beta)
\]

も得る。さらに \(\beta>0\) と

\[
\beta C_H^2M_{\rm src,H}<2V_H
\]

から \(E_H(\beta)<\beta V_H\) を形式証明し、同じ \(\beta\) で任意の真正右境界 \(B\) に対して \(T_{H,\beta}(B)<0\) を導く。

AHNの \(V_H>0\) を用いて、有限Hごとに具体式

\[
\boxed{
\beta_H=\frac{V_H}{1+C_H^2M_{\rm src,H}}>0
}
\]

を選び、

\[
\boxed{
\forall B\in\mathrm{Cfg}_H,\quad
T_{H,\beta_H}(B)<0
}
\]

の**存在定理**をLean4で形式証明した。結合の選択はH依存であり、\(\beta_H=\beta_0\) とは仮定しない。

## 5．Lean4全文診断・固定mathlibからの修正学習

初回実装commit `dc04c85139d57d9f82665e4638d624d978385f5c` の [CI #42418254908](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42418254908) は失敗。依存モジュールPW・PW2・PU・PU2・PY3・AGN・AHN・AHP・AHQの真正APIと変更Lean全文313行・imports・実ログを照合した。

1. 本体の一リンクHaar直交性は初回から形式検証を通過。
2. PWとPW2で局所`Fintype`インスタンスが異なるため、数学的には同じ元`Finset.univ`の有限和でもLeanの定義上の等式にならなかった。失敗した2箇所の有限和は、`Finset.sum_congr`と`Finset.ext`で**元有限集合の同一性を明示**して修正。
3. 依存する可積分性証明において、`(...).integrable_of_hasCompactSupport`のドット記法を改行で切るとLean4パーサーがfield名を認識できない。投影を同じ行へ移して修正。
4. 下流の`sorryAx`はこれら未完了の証明からの連鎖であり、新公理を導入せず消滅した。

最終HEAD `a92cc9fc54f6bc0eda0d9d22a0b46238ad9ee9dc` のCI `#42418693589` は全体SUCCESS、独立receipt成功、10定理標準公理のみ、変更warning/error 0/0。定理文を弱めず、元Wilson核や元Gauss-law sourceを上書きしていない。

## 6．OPEN — 次段AHSへの必要な厳密評価

AHRの**H依存の小正結合**における一様負符号は証明済み。しかし元の固定結合 \(\beta_0=\log(3/2)/64\) について、

\[
E_H(\beta_0)<\beta_0 V_H
\]

あるいは体積一様に役立つより鋭い高次残差評価は未証明。元の物理L² transferの定量的非零下界・正負両符号殻・体積一様coercivity・Hamiltonian spectral gap・連続体4D Yang–Mills質量ギャップはいずれも未証明。

次の研究は、厳密Haar直交性による一次項の改善を利用し、元Wilson核の局所支持と高次Haar積分の符号付き計算から、固定\(\beta_0\)で残差を減らせるかを調べる。既存証明や作用を変更しない。

[AHR定理Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c3e6faec3b44981fae5c5b993ed2b8ee9115de5f/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalOneCrossingHaarOrthogonalityV5_PZ37AHR.lean)

この正式記録は新規Markdownファイル1件のみのappend-only追補。docs-only PRでStrict Leanを新たに走らせない。
