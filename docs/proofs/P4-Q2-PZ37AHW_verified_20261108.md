# P4-Q2-PZ37AHW — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の形式定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。GitHub `main` は正式文書ミラー。運用原則：append-only／tighten-only／overwrite-forbidden／same-root。元の完全SU(2) Wilson一スラブ作用・核・左右空間halfweight・元ZW Gauss-law signed source・元空間積Haar・型付き証明履歴・Lean/mathlib pin・workflowは不変更。

## 1．Authoritative exact-source証明台帳

| 項目 | 独立検証済み |
| --- | --- |
| [AHW定理PR #6484](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6484) | **MERGED** |
| 継承元 AHV authoritative HEAD | `23ffde5e8fbef33dfe09acd7d2644c0bccc5dbad` |
| 最終 exact-source HEAD | `c727c8a5dd2c76cc39d578ee9550692f1c61cb93` |
| exact test-merge HEAD | `2b5af6a434975c48a02f56512a0e74369239905c` |
| squash 定理正本HEAD | `611af86e3bba3dd299f6e464e98cfbae8273d993` |
| source／test-merge／squash共通Git tree | **`26ec736fcd2e09bd831768b1d9c16afea2557e52` 一致** |
| [最終exact-source CI #42432091555](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42432091555) | **completed／SUCCESS** |
| Changed Lean job | `128583009683` — completed／SUCCESS |
| 独立completion receipt job | `128584197020` — completed／SUCCESS |
| receipt context | `chatgpt-ci-receipt/PR Lean Fast Check` — success |
| Strict Lean依存閉包 | **11,385／11,385 SUCCESS** |
| AHW新規`#print axioms` | **20宣言すべて標準公理**（`propext`、`Classical.choice`、`Quot.sound` のみ） |
| `sorryAx` | **なし** |
| 変更Lean warning／error | **0／0** |
| 成功CI生ログartifact | `13597692522`（`lean-fast.log` を回収・確認） |
| 新規Leanファイル | **2件**のみ。既存Lean・物理定義・公開root・pins・workflow・README・ROADMAP不変更 |

固定環境はLean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。最終ログ末尾は `Build completed successfully (11385 jobs).`。新規全20宣言の公理監査を完了。既存依存ファイルの歴史的warningと今回の変更Leanファイルのwarning/errorは分離する。

## 2．CLOSED — 元の偶数周期空間トーラス上の具体的Z/2中心cochain

元の時間ゼロ空間スライスのリンク \((x,j)\) で、既存`periodicHypercubicEvenCoordinateParity`を用いて真正法2の1-cochain

\[
\tau_j(x)=\sum_{i<j}\operatorname{parity}(x_i)\in\mathbb Z/2\mathbb Z
\]

を定義した。周期長が \(2(H+1)\) で偶数なので既存のparity homは元の周期トーラス上に一価に定義済み。既存の`periodicHypercubicEvenCoordinateParity_shift`と、その型付き空間スライスへの移送から

\[
\tau_j(x+e_i)=\tau_j(x)+\mathbf1_{\{i<j\}}
\]

を形式証明した。各真正空間プラケット \(p=(x;i,j)\)（\(i<j\)）の**元の四辺** \(e_0,e_1,e_2,e_3\) について、逆向き辺を含むZ/2境界和は

\[
\boxed{\delta\tau(p)=\tau(e_0)+\tau(e_1)+\tau(e_2)+\tau(e_3)=1}
\]

である。これは全有限 \(H\)、最小周期2を含む**証明済みの型付きflux恒等式**であり、未検証の数値実験ではない。

## 3．CLOSED — 具体的な真正SU(2)中心twistと元積Haar保存

既存の真正SU(2)中心元 \(z=-I\) を再使用し、\(z^2=1\)、\(z^{-1}=z\)、任意の \(g\in SU(2)\) との可換性を既存PU/PVから使用。法2のcenterSign \(s:\mathbb Z/2\mathbb Z\to SU(2)\) を \(s(0)=1,\ s(1)=z\) と定義し、型付き加法・逆元・中心可換性を証明。

元の空間SU(2)リンク構成に対し、新しい物理作用やposteriorを作らず、**元の構成上の変換**

\[
(T_HA)_{(x,j)}=A_{(x,j)}s(\tau_j(x))
\]

を具体的に構成。各元リンク座標は固定SU(2)元による右Haar並進なので、既存`normalizedCompactHaar_measurePreserving_mul_left_right`と`Measure.pi_map_pi`を使い

\[
\boxed{(T_H)_*\mu_H=\mu_H}
\]

を元の真正空間積Haar上でLean4形式証明した。一般の頂点ゲージ変換と取り違えていない。元の相互作用Gibbs確率全体の不変性は仮定も証明もしていない。

## 4．CLOSED — 実際の四辺SU(2) holonomyを中心元が反転

元の空間プラケットの非可換で順序付きの真正holonomy

\[
U_p(A)=A_{e_0}A_{e_1}A_{e_2}^{-1}A_{e_3}^{-1}
\]

について、元SU(2)リンク値の順序を変更せず、中心成分だけを可換移動するLean補題を構成。逆向きリンクも \(s(a)^{-1}=s(a)\) により正しく追跡し、第2節で証明した\(\delta\tau(p)=1\)を適用して

\[
\boxed{U_p(T_HA)=U_p(A)\,z}
\]

を形式証明した。元Wilsonエネルギーの中心反転 \(E(gz)=2-E(g)\) より、元の全空間プラケット実文字

\[
\chi_p(A)=1-E(U_p(A))
\]

について

\[
\boxed{\chi_p(T_HA)=-\chi_p(A)}
\]

をすべての真正プラケットで証明した。

## 5．CLOSED — 全空間sourceの反転と真正三次Haarモーメント消滅

元PW2/AHR既証明の真正全プラケット文字和 \(\Phi_H=\sum_p\chi_p\) とsourceの元の恒等式

\[
f_H(A)=-\frac12\Phi_H(A)=\frac{W_H(A)-p_H}{2}
\]

を変更なしで使う。第4節から全プラケット和は奇、元空間Wilson作用は

\[
\Phi_H(T_HA)=-\Phi_H(A),\qquad
W_H(T_HA)=2p_H-W_H(A)
\]

となり、真正centered ZW sourceについて

\[
\boxed{f_H(T_HA)=-f_H(A)}
\]

を形式証明した。第3節の**実際に構成された元Haar保存変換**を、既証明AHVの条件付き奇関数積分消滅定理へ代入し、条件を完全に解消した。

\[
\boxed{
M_{3,H}=\int_{\mathrm{Cfg}_H}f_H(A)^3\,d\mu_H(A)=0
}
\]

これは**全有限偶数周期Hにおける無条件の真正三次source Haar恒等式**であり、もはや「もし中心twistが存在すれば」という条件付き定理ではない。

AHU既証明の元完全一スラブ作用についての真正二次sourceモーメント

\[
M_{2,H}(B)=M_{3,H}+(3p_H+W_H(B))V_H,
\quad V_H=\int f_H(A)^2\,d\mu_H(A)>0
\]

へ代入し、

\[
\boxed{
M_{2,H}(B)=(3p_H+W_H(B))V_H
}
\]

を形式証明した。AHTで得た元Wilson作用に対する厳密単調性・ゲージ不変性と整合する。

## 6．Lean4全文診断・複数CI修正の構造理由

Lean4 error指摘行だけでなく、変更AHW Lean2ファイル全文、元PW2、PU/PV、既存parity、AGN/AHR/AHV/AHU、固定mathlibとGitHub Actions生ログを照合した。実装で新規公理・`sorry`・`admit`は使わず、既存元物理定義や仮定を弱めていない。

診断の主要な構造的原因は次の通り。

- **Lean notation前方参照**：初回sourceで`τ`／`s`／`T`を対応するdefより前に置いたためquotation precheckが失敗。各定義の直後に記法を移動して解消（初回CI #42429299796）。
- **固定`ZMod 2`の有限計算**：`simp`の未使用引数、法2の`2=0`、`fin_cases`で得る内部Fin構成子と具体的0／1の不一致。固定mathlibの`Finset.sum_ite_eq'`と有限値の外延的比較を使用。特に`Classical`下の`decide`が内部Fin代表の等式判定で停止したため、各0／1代表を`rfl`で型付きに正規化し、中心符号の加法・逆元の証明へ移送（#42429821610、#42430257179、#42430649819、#42431058623、#42431494407）。
- **元PW2とAHWの`Fintype`列挙差**：数学的には同じ全空間プラケット和でも`rfl`では一致しない。元AHR/AHUと同じ`Finset.sum_congr`による外延的な等式`hUniv`を作り、第2ファイルの全文字和とその負号を照合（最終source `c727c8a5dd2c76cc39d578ee9550692f1c61cb93`）。

最終exact-source CI #42432091555、20宣言標準公理のみ、`sorryAx`なし、変更warning/error 0/0、独立completion receipt SUCCESS、source/test-merge/squash共通Git tree一致を確認し、定理PR #6484をsquashマージした。

## 7．OPEN — 次段AHX：固定結合に向けた高次Taylor解析

AHWで元の3次source Haarモーメントと二次作用モーメントの切片は確定したが、**固定結合** \(\beta_0=\log(3/2)/64\) における完全Boltzmann transferの符号は導いていない。

次に、既存AHP/AHRの真正transfer Taylor一次と、AHWで得た真正完全作用二次sourceモーメントを厳密に接続し、三次剰余の積Haar評価・符号余裕と必要精度を研究する。その際、元の完全one-slab kernel、左右halfweight、正負transfer二殻と、全volumeでの外挿可能性を明確に区別する。

固定結合での真正transfer符号・正負殻、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップはいずれも引き続き**未証明**。

[第1AHW Lean定理全文（center cochainと積Haar保存）](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/611af86e3bba3dd299f6e464e98cfbae8273d993/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalEvenTorusCenterCochainV5_PZ37AHW.lean)

[第2AHW Lean定理全文（真正source反転・三次モーメントゼロ）](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/611af86e3bba3dd299f6e464e98cfbae8273d993/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalEvenTorusCenterSourceOddV5_PZ37AHW2.lean)

本証明記録は新規docs-onlyファイルとして追記する。既存Lean・物理定義・正本root・pins・workflow・README・ROADMAPは改変しない。文書PRではStrict Leanを起動しない。
