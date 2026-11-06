# AGN 正式証明記録

記録日：2026-11-06 JST。唯一のLean4定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。main上の本書は文書ミラーである。

## 完了した検証

| 項目 | 確認結果 |
|---|---|
| 定理PR | [#6381](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6381) MERGED |
| 検証済みsource | `7ab237c1bfb08c85d6ff9031b208b575b23b30b5` |
| 実checkout test-merge | `5f902a43cb2e046d3164779fe87fc2c8b51f1bbd` |
| 定理squash | `c648bd88566d1e5bf06324ada997ab37918cb12c` |
| source・test-merge・squash共通Git tree | `c6d6dc1d045edb21a42a52a0b8682836dfb6176e` |
| exact-source CI | [#42164476429](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42164476429) completed / SUCCESS |
| Lean job / step17 | `127717599152` / Run changed Lean fast check：completed / SUCCESS |
| ビルド | **11,349 jobs成功** |
| 公理依存確認 | **43宣言**：厳密平均14・質量/平均包囲12・自動証明書17、欠落0 |
| 使用公理 | `propext`・`Classical.choice`・`Quot.sound`の範囲内 |
| sorryAx | 終了済みjob全文中0件 |
| 新規Lean warning/error | **0/0** |
| 独立completion receipt job | `127719202262` completed / SUCCESS |
| sourceへのreceipt status | `chatgpt-ci-receipt/PR Lean Fast Check` SUCCESS |
| ソース差分 | 新規Lean3ファイル・1,013行追加・既存行削除0 |

終了済みLean jobの全文を確認し、43個の対象名と各公理依存をソースの `#print axioms` と照合した。source・実checkout test-merge・定理squashのGit treeを個別取得し、完全一致を確認した。

CI artifactは [13478920966](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42164476429/artifacts/13478920966)。upload log記録のSHA-256は `124bac8127e4c4bf80f1b4c7f1a65e2969f223a9ab383ce82095fc0f1912040b`。今回の独立確認は終了済みjob log全文によるものであり、artifact ZIPを再取得してhashを再計算したという主張はしない。

固定環境：Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。新規Lean葉3ファイルのみを追加し、既存Lean、物理的定義、Haar測度、元source、transfer、公開集約root、workflowは変更していない。

## 1. 元Wilson作用のHaar平均の厳密計算

元の有限体積Hにおける空間Wilson作用をW_H、実際のplaquette listの長さをp_H、元の空間product Haarをmu_Hとする。AFZが物理Hilbert内積と同定した中心化定数について、

`m_H = integral W_H dmu_H = p_H`

を証明した。中心化した源の平均をp_Hと主張するものではない。元の中心化源は `f_c=(W_H-p_H)/2` であり、そのHaar平均は0である。

証明は、元の各plaquetteに現れる4本の実際の空間リンクを使用する。偶数側長 `2*(H+1)>=2` と既証明の非自明な単位移動から4リンクの単射性を示した。H=0も含む。この埋め込みによる座標制限は、元product Haarを4リンクproduct Haarへ正確に押し出す。

既証明のcyclic四辺Haar wordと元Wilsonエネルギーの共役不変性を接続し、各元plaquetteエネルギーの積分を1と求めた。元plaquette listの和を積分の線形性で足す。異なるplaquetteどうしの独立性は仮定していない。

元の作用値域 `0<=W_H<=2*p_H` とこの厳密平均から、

`|f_c(A)| <= p_H/2`

をすべての元配置Aについて導いた。これは連続代表の点ごとの定理であり、任意のHaar-L2代表と選んだ点での値を同一視していない。AGLの有理座標証拠を持つ配置では、元の連続代表 f_c(A) を厳密有理値として評価し、幅0のAFV区間を構成した。

## 2. 真正Haarセル質量と独立の平均包囲

任意のAGH元空間格子について、各真正セルのHaar実質量を包囲する有理上下端とその証拠を分離した。元セル・元Haar測度をAGCのstep積分へそのまま移し、真正質量の総和が1であることを証明した。有理端点の総和を1と仮定していない。

任意の元可積分関数について、セルごとの有理上下界からAGIの符号付き有限評価器による積分包含を証明した。係数が負の場合は上側質量端点が下界に寄与するmin/maxを保持し、端点どうしを誤って単純に掛けていない。

元中心化定数の相殺とAGGの源の傾き12から、元Wilson作用の全リンク弦距離に対する傾き24を導出した。AGLの厳密有理中心作用値、真正質量区間、`24*radius` を覆う有理幾何誤差から、元平均の独立した積分区間を構成し、既存の `[0,2*p_H]` と交差した。これは上の厳密平均とは別の証明経路であり、今後の細分格子を検証する接続口として保持する。

具体的AFQ・AGDの24中心product gridでは、Lを元空間リンク数として、

`(1/160000)^L <= mu_H(cell_i) <= (625/1781)^L`

という既証明の真正質量端点、`radius=(4/5)*L`、実際の中心配置の有理座標証拠を構成する。未知の実数の有理近似を選ぶoracleは使わない。

## 3. AGMからAGIへの実際の元値の接続

元global action budget `2*CombinatorialVolume(H)` は厳密有理値を持つ。AGKの元beta0区間、AGJのBoltzmann包囲、AGMの自動整数尺度を組み合わせ、実際の

`k_H = exp(-beta0*GlobalActionBudget(H))`

の区間を構成し、元の `[0,1]` と交差した。正Taylor次数だけから有理下端の厳密正値性を主張していない。

有理座標配置A,Bについて、元の中心化源の厳密有理値、AGMの実際の核K_H(A,B)の区間、元floor midpointの区間から、AGEの連続被積分関数

`g_B(A)=f_c(A)*(K_H(A,B)-(1+k_H)/2)`

の符号を保持する区間を構成した。源の係数の正負をmin/maxで処理する。

真正Haar質量端点と元AGGの幾何誤差を加え、AGIの全certificate fieldを構成した。任意の有理座標境界Bに適用でき、特に真正AFQの24中心を各元リンクへ割り当てた境界では、追加の数値入力は結合次数m、Taylor次数nとn>0だけである。証明付き有理端点は元のsigned transfer t_H(B)を包含する。

## 4. 無条件のtransfer上界改善とtighten-only

厳密平均による源上界p_H/2と元の核midpoint boundから、

`|g_B(A)| <= (1-k_H)*p_H/4`

を導出した。元Haarに対する積分とAGEの元transfer同定により、floorの認証有理下端ellについて、

`|t_H(B)| <= p_H*(1-ell)/4 <= p_H/4`

が成立する。従来AGBのp_H/2を少なくとも係数1/2で改善する。AGIによる符号付き積分区間とこの独立大域区間を交差し、同じ元transferについて両方の情報を保持した。

下端が0より大きい場合に正、上端が0より小さい場合に負というAFVの条件付き符号定理へ接続した。実際の特定境界でこの不等式を成立させたという主張はしない。

## 5. Lean4の検証と修正理由

初回source `52c0e6b1cd4f614f0fe793dcb6b863384614f774` の [CI #42160684519](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42160684519) は失敗した。四つの未確定型を含む `continuous_apply` の合成でLeanのwhnf処理がheartbeat上限に達し、元plaquette要素数と頂点・方向対の積のcardinality等式も未解決だった。全文・依存定義・指定mathlibの `MeasureTheory/Function/L1Space/Integrable.lean` を確認し、可積分性を既証明の真正Haar保存写像と `MeasurePreserving.integrable_comp_of_integrable` から導く構成へ変更した。heartbeat、定理文、数学的仮定は変更していない。失敗中に生成されたsorryAxを含む診断は成功証明として扱わず、最終source全体で再検証した。

次のsource `58a245ce7a96403104ca04796be27f5dc92ece23` の [CI #42161906259](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42161906259) では、改行されたdot notationの構文と、異なるFintype instance間の要素数比較が未解決と判明した。Haar保存写像を明示的に束縛して型注釈付きの `MeasurePreserving.integrable_comp_of_integrable` を適用した。要素数は固定mathlibの `Fintype.card_eq_nat_card` を使って列挙instanceに依存しない `Nat.card` へ移した。定理文や前提を弱めず、最終source全体の完了済みCIを採用した。

source `57cf3a6b13d6f767242b6ceeb7c01bc1a06e993e` の [CI #42162980005](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42162980005) では要素数比較は解消したが、可積分性の補題で暗黙の合成写像がWilsonエネルギーの展開から誤って推論された。写像fと被積分関数gを名前付き引数で指定して推論の曖昧さを除去した。数学的構成や前提には変更がない。

source `85bbc670a455d31c003ad7d74215c96f6229b01f` の [CI #42163696241](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42163696241) では、厳密平均14宣言と質量・平均包囲12宣言が標準公理のみで通過した。初めてビルドされた接続ファイルでは、複数行の構造体リテラル2か所の構文エラーが見つかった。4フィールドのconstructorと独立した証明ブロックに整理し、すべての依存宣言を最終sourceで再検証した。

## 固定24中心の精度評価（今回のLean宣言とは別の数式確認）

元の空間方向は {1,2,3}、方向対は {(1,2),(1,3),(2,3)} である。元link型・plaquette型はいずれも空間頂点型とこの3要素型の積であり、literal plaquette list は Finset.univ.toList なので、元リンク数 L_H と p_H は等しい。

現行の幾何予算は
`gamma_H(m)=(6+13*betaUpper(m)*p_H)*(4/5)*L_H >= (24/5)*p_H`
である。一方、新しい対称大域区間の半径 R は `0<=R<=p_H/4` だから `gamma_H(m)>=2*R`。

各中心の真正値を g_i、認証sample端を a_i,b_i とすると、`a_i<=g_i<=b_i` と `|g_i|<=R` より、AGIのセル下端は `a_i-gamma<=-R`、上端は `b_i+gamma>=R` となる。真正質量の上端 M_i は非負で、その総和は真正質量総和1以上である。したがってAGIのmin/max付き和は
`rawLower<=-R*sum M_i<=-R`、
`rawUpper>=R*sum M_i>=R`
を満たす。

このため現在の固定24中心・現行幾何予算では、raw signed interval は新しい大域区間全体を含み、最後の交差はちょうど `[-R,R]` になる。現行certificateの接続自体は証明されたが、この固定格子から大域区間を超える符号情報はまだ得られない。現行構成では、いかなるm,nでも正負の判定条件を満たせない。真正質量を完全に正確にしても、現在の幾何予算を維持する限り同じ障害が残る。この評価は定義と証明済み不等式を照合した数学的帰結であり、今回新設した独立のLean theoremとしては数えていない。

## 残る課題と適用範囲

元の有限リスト・有限型の列挙は非計算的な定義を含む。大体積の24^L個の数値表を実行した結果ではない。固定24中心の半径4/5と保守的なHaar質量区間はまだ粗く、結合次数・Taylor次数だけを増やしても幾何誤差・質量誤差は消えない。

次段階は、上記の精度障害のLean定理化、元sourceの厳密平均を利用した幾何誤差の改善、細かい真正セルまたは元Haarモーメント・相関を保持する積分評価である。空間側の障害を除いた上で質量区間も精密化し、実際の境界で符号分離を認証する。

実際の非零signed transfer符号、二閾値殻非空、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは未証明である。

## 元ソース

- [厳密な元Wilson Haar平均](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c648bd88566d1e5bf06324ada997ab37918cb12c/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExactWilsonHaarMeanV5_PZ37AGN.lean)
- [真正Haar質量・独立平均包囲](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c648bd88566d1e5bf06324ada997ab37918cb12c/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHaarMeanEnclosureV5_PZ37AGN.lean)
- [元signed transferの自動証明書](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c648bd88566d1e5bf06324ada997ab37918cb12c/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAutomaticSignedSpatialCertificateV5_PZ37AGN.lean)
- [AGM正式記録](P4-Q2-PZ37AGM_verified_20261106.md)
- [AGK・AGL正式記録](P4-Q2-PZ37AGK-AGL_verified_20261106.md)
