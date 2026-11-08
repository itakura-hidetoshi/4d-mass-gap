# P4-Q2-PZ37AHY — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の形式定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。GitHub main は正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元のSU(2)完全Wilson一スラブ作用、両端の空間halfweight、元ZW signed source、元の空間積Haar、型付き証明履歴、root、固定Lean/mathlib、workflowを保持。

## 1．Exact-source証明台帳

| 項目 | 検証済みの結果 |
| --- | --- |
| [AHY定理PR #6490](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6490) | **MERGED** |
| 継承元AHX正式記録HEAD | `3469d09c6cca631ddcc2aaea4ca9980ce20e6622` |
| 最終exact-source HEAD | `2ba9ebdfeb660a79b1d463917695e70746a8d714` |
| exact test-merge HEAD | `f37759fecb899b93b9d913bd41e7b745a9de8efb` |
| 定理squash HEAD | `05ef26b6498a3175abb84e16d32f974fdee80843` |
| source／test-merge／squash共通Git tree | `4349b03496af62a5ad6af98f4d82c912efa72461`、完全一致 |
| 最終exact-source CI | [#42437937800](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42437937800) — **completed／SUCCESS** |
| Changed Lean job・Lean step | `128600732879` — **completed／SUCCESS** |
| 独立completion receipt job | `128601823704` — **completed／SUCCESS** |
| exact-head receipt context | `chatgpt-ci-receipt/PR Lean Fast Check` — **success** |
| Strict Lean依存閉包 | **11,387／11,387 SUCCESS** |
| 新規定理の公理確認 | **32／32**、`propext`・`Classical.choice`・`Quot.sound` のみ |
| `sorryAx` | **なし** |
| 変更Lean warning／error | **0／0** |
| 成功CIログartifact | `13599978146`、`lean-fast-check-log` |
| 新規Leanファイル | **1件・593行**、既存ファイル変更なし |
| 新規Lean blob | `d25c770815022e0bfbf19e96abcaf928fede6de1`、最終全文readback一致 |

固定環境：Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。成功ログの最終結果は `Build completed successfully (11387 jobs).`。変更ファイルの32定理を個別に確認。既存依存ファイルの歴史的warningと今回の変更ファイルのwarningを区別する。

## 2．CLOSED — 元の作用の右境界を残す上界

AHXから元の完全一スラブ作用をそのまま継承する。
\[
S_H(A,B)=\frac12W_H(A)+S_H^{\mathrm{cross}}(A,B)+\frac12W_H(B).
\]
既存global budgetは、元のplaquette listとlink listの長さを \(P_H,L_H\) として \(C_H=2(P_H+L_H)\)。AFZの \(p_H=P_H\) と、AHQの形式証明済みの \(L_H=p_H\) から
\[
\boxed{C_H=4p_H}
\]
を得る。

元の空間作用とcrossing作用の上界 \(W_H(A)\le2p_H\)、\(S_H^{\mathrm{cross}}(A,B)\le2p_H\) を使用する。右端のWilson作用はそのまま残し、
\[
\boxed{C_H(B):=3p_H+\frac{W_H(B)}2
=C_H-p_H+\frac{W_H(B)}2}
\]
を定義して
\[
\boxed{0\le S_H(A,B)\le C_H(B)\le C_H}
\]
を証明した。元の左右halfweightを維持した実際の作用上界である。これは上界の証明であり、最大値の達成や最適性を主張しない。

## 3．CLOSED — sourceの正負部分と真正Haar三次相関

元source \(f_H=(W_H-p_H)/2\) と元のHaar質量
\[
M_H=\int |f_H|\,d\mu_H
\]
を使う。誤差評価のために
\[
f_{H,+}=\frac{|f_H|+f_H}{2},\qquad
f_{H,-}=\frac{|f_H|-f_H}{2}
\]
を定義する。両者の連続性・非負性を証明し、AHPの既存の真正Haar平均零
\[
\int f_H\,d\mu_H=0
\]
から
\[
\boxed{\int f_{H,+}\,d\mu_H
=\int f_{H,-}\,d\mu_H=M_H/2}
\]
を得た。元transferのsource自体は従来のsigned sourceである。

次の量はいずれも、元の完全作用と元のHaarによる実際の相関積分である。
\[
J_{+,H}(B)=\int f_{H,+}(A)S_H(A,B)^3\,d\mu_H(A),
\]
\[
J_{-,H}(B)=\int f_{H,-}(A)S_H(A,B)^3\,d\mu_H(A),
\quad
J_{|f|,H}(B)=\int |f_H(A)|S_H(A,B)^3\,d\mu_H(A).
\]
連続性と配置空間のコンパクト性から被積分関数の可積分性を証明した。その上で
\[
J_{+,H},J_{-,H},J_{|f|,H}\ge0,\qquad
\boxed{J_{+,H}(B)+J_{-,H}(B)=J_{|f|,H}(B)}
\]
と
\[
\boxed{J_{\pm,H}(B)\le C_H(B)^3\,M_H/2},
\qquad
J_{|f|,H}(B)\le C_H(B)^3M_H
\]
を得た。

平均零が直接決定するのは**重みなしの質量**である。\(J_{+,H}=J_{-,H}\) や \(\int f_HS_H^3\,d\mu_H=0\) は仮定せず、主張もしない。

## 4．CLOSED — 真正Taylor剰余の符号を利用する両側評価

AHXの剰余定義を変更しない。
\[
R_{3,H}(\beta,B)=\int f_H(A)\,r_{H,\beta}(A,B)\,d\mu_H(A),
\]
\[
r_{H,\beta}(A,B)=e^{-\beta S_H(A,B)}
-\left(1-\beta S_H(A,B)+\frac{(\beta S_H(A,B))^2}{2}\right).
\]
AHXのスカラー定理を使い、全 \(\beta\ge0\) に対して
\[
-\frac{(\beta S_H(A,B))^3}{6}\le r_{H,\beta}(A,B)\le0
\]
を明示的な符号付き区間として証明した。被積分関数の可積分性は、既存のkernel/source積と二次多項式/source積の可積分性から得る。

非正の誤差 \(r\in[-d,0]\) と任意のsigned source \(f\) には
\[
-f_+d\le fr\le f_-d
\]
が成立する。これを元のHaarで積分し、
\[
\boxed{-\frac{\beta^3}{6}J_{+,H}(B)
\le R_{3,H}(\beta,B)
\le\frac{\beta^3}{6}J_{-,H}(B)}
\]
を証明した。左側を正source部分、右側を負source部分が制御する。

絶対値の積分比較による
\[
\boxed{|R_{3,H}(\beta,B)|
\le\frac{\beta^3}{6}J_{|f|,H}(B)}
\]
も独立して形式化した。ここでは作用との相関を積分の内側に残す。

## 5．CLOSED — 境界依存の誤差上界とAHX幅の半減

第3・4節を組み合わせ、
\[
\mathcal E_{H,\beta}(B)
:=\frac{(\beta C_H(B))^3}{12}M_H
\]
に対して
\[
\boxed{|R_{3,H}(\beta,B)|
\le\mathcal E_{H,\beta}(B)
\le\frac12E^{\mathrm{AHX}}_{3,H}(\beta)}
\]
を証明した。ここでAHXの既存上界は
\[
E^{\mathrm{AHX}}_{3,H}(\beta)=\frac{(\beta C_H)^3}{6}M_H.
\]
係数 \(1/12\) は、非正のkernel誤差と元sourceの平均零をともに使った結果である。さらに元のAHJ上界 \(M_H\le p_H/2\) により
\[
\boxed{|R_{3,H}(\beta,B)|
\le\frac{(\beta C_H(B))^3}{24}\,p_H}
\]
を得る。非負性と \(\mathcal E_{H,0}(B)=0\) も証明した。

すべての比較は任意の \(\beta\ge0\) と元の境界 \(B\) に有効で、\(\beta C_H\le1\) のような小ささの仮定を追加しない。相関積分 \(J_{|f|,H}\) 自体を半分にする主張ではなく、両source部分を別々に上から評価して得た一様幅の半減である。

## 6．CLOSED — 同じ二次中心を持つtransfer区間と符号条件

元の二次sourceモーメントを \(V_H=\int f_H^2\,d\mu_H\) と書く。AHXの厳密な二次中心
\[
Q_{H,\beta}(B)
=-\beta V_H+\frac{\beta^2}{2}(3p_H+W_H(B))V_H
\]
と、元の物理的L2 transferについての等式 \(R_{3,H}=T_{H,\beta}-Q_{H,\beta}\) を再使用する。
\[
\boxed{Q_{H,\beta}(B)-\frac{\beta^3}{6}J_{+,H}(B)
\le T_{H,\beta}(B)
\le Q_{H,\beta}(B)+\frac{\beta^3}{6}J_{-,H}(B)}
\]
および
\[
\boxed{Q_{H,\beta}(B)-\mathcal E_{H,\beta}(B)
\le T_{H,\beta}(B)
\le Q_{H,\beta}(B)+\mathcal E_{H,\beta}(B)}
\]
を証明した。AHXとの比較では近似中心が同一なので、改善した対称区間はAHXの区間に含まれる。

負符号の十分条件は
\[
\frac{\beta^2}{2}(3p_H+W_H(B))V_H
+\frac{\beta^3}{6}J_{-,H}(B)<\beta V_H.
\]
正符号の十分条件は
\[
\beta V_H+\frac{\beta^3}{6}J_{+,H}(B)
<\frac{\beta^2}{2}(3p_H+W_H(B))V_H.
\]
それぞれ元のtransferの厳密な負・正符号を導く条件付き定理を証明した。元固定結合 \(\beta_0=\log(3/2)/64>0\) への区間と両符号定理の特殊化も形式化済み。**具体的境界で余裕条件が成立するという証明は、AHYには含まれない。**

## 7．全文・依存先・固定APIの検証

変更Lean全文、直接importするAHX、AHQのexact count、元のglobal budgetと作用上界、AHPの平均零・可積分性・物理transfer橋渡し、AHNのL1積分、AHJのhalfCount、AHXの実際の剰余と二次中心を照合した。固定toolchainとmanifestをcanonical HEADから再取得し一致を確認した。

固定mathlibの[Bochner/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean)について、積分の線形性、単調性、絶対値による積分比較の署名を確認した。独立した全文・数学レビューでも必須修正事項は認められなかった。

初回CI [#42437358244](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42437358244) では、絶対値を用いる積分比較1か所で、点ごとの関数適用が残ったgoalに対する `rw [abs_mul]` の照合が失敗した。ほかの31定理は標準公理のみでelaborateされた。固定APIと全文の全 `integral_mono` 使用箇所を再点検し、該当goalを元と定義上同じ点ごとの不等式へ `change` で明示する3行を追加した。定理文・仮定・imports・既存物理定義は変更せず、警告抑制やsorryを加えない修正とした。修正後のexact-source CIを改めて完了まで確認した。

最終exact-sourceのworkflow、Changed Lean job、Lean step、独立receiptがすべて完了・成功してから確認した。新規32定理は標準公理のみ、sorryAxなし、変更warning/error 0/0。GitHub上の最終全文とPR変更ファイル一覧を読み戻し、source／test-merge／squashのGit tree一致を確認して統合した。

## 8．OPEN — 次段AHZ

次の焦点は、ここで残した真正相関 \(J_{+,H}(B),J_{-,H}(B)\) の評価を進め、元固定結合で符号条件を実際に満たす境界・領域を特定すること。必要に応じて、元の作用の構造から \(\int f_HS_H^3\,d\mu_H\) など高次のsigned相関を評価し、さらに高次のTaylor中心・剰余へ接続する。既存の線形crossing Ward評価だけでは、\(\int f_H^2(S_H^{\mathrm{cross}})^2\,d\mu_H\) や \(\int f_H(S_H^{\mathrm{cross}})^3\,d\mu_H\) の評価は自動的には得られず、別途証明が必要となる。

未証明の課題は、元固定結合での真正transferの具体的符号・正負二殻、体積に一様なcoercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップ。今回の有限体積の厳密な誤差幅改善を、これらの解決と同一視しない。

[AHY Lean定理全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/05ef26b6498a3175abb84e16d32f974fdee80843/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalWeightedCubicRemainderV5_PZ37AHY.lean)

本記録を新規docs-onlyファイルとしてformalへ追記し、同一Git blobをmainへ文書同期する。文書PRではStrict Leanを起動しない。
