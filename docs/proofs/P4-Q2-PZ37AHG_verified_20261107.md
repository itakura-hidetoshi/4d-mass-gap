# P4-Q2-PZ37AHG 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。`main` は文書ミラー。元Wilson作用・centered source・kernel・floor・真正Haar測度・既存証拠履歴・公開root・固定Lean/mathlibを変更しない。

## Exact-source検証と統合

| 項目 | 確認結果 |
| --- | --- |
| [AHG定理PR #6436](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6436) | **MERGED** |
| AHF継承基点 | `e999d7e7493c96b18ce73bce7c41c38da5beb9ca` |
| 最終exact-source HEAD | `70dfe63a118d2e617ec7a03ba9b3ca3ee94d124e` |
| test-merge SHA | `9d77edbd40ac2f5e75d42e1e033134b696d684de` |
| theorem squash SHA | `885c00a530c27f4abc18c32d5c1ce09a90b25020` |
| source/test-merge/squash共通Git tree | `d39711e081ffe1e4b7052690193c37ecb3b40b10` |
| [Exact-source CI #42328486379](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42328486379) | workflow completed / **SUCCESS** |
| Changed Lean job | `128269255894` completed / SUCCESS |
| Lean依存閉包 | **11,368 / 11,368 SUCCESS** |
| 新規宣言公理依存 | **19宣言（15定理・4証拠付き構成）**、標準3公理のみ |
| sorryAx / 変更Lean warning / error | **なし / 0 / 0** |
| 独立completion receipt | job `128270810640` completed / SUCCESS |
| 最終変更 | 新規Lean1件・359追加行、既存Lean変更・削除0 |

GitHub MCPから最終 `lean-fast-check-log` artifact `13555544072` を回収し、実ログの `Build completed successfully (11368 jobs).`、新規19宣言の公理依存がすべて `propext`・`Classical.choice`・`Quot.sound` の範囲内であること、ログ全体のsorryAxなし、変更対象AHGのwarning/error 0/0を確認した。既存依存の非fatal警告は変更ファイルの診断と区別する。固定Leanは `v4.30.0-rc2`、mathlibは `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。独立Strict Lean/Governance workflowが実行されたとの主張はしない。

初回CI `42327844556` でも11,368件のビルドは成功し、証明エラーはなかった。ただし不要な `<;>` に対する警告が2件あったため、2箇所を逐次タクティクへ整理し、同一の定理文・仮定で最終CIを再検証した。

## CLOSED — 元立体射影の厳密な距離恒等式

元AGR/AGSの立体射影を `S(u)` とし、`s(u)=sum_j u_j^2` とすると、元Euclidean S3上で

```text
S(u) = ((1-s(u))/(1+s(u)), 2*u_0/(1+s(u)),
        2*u_1/(1+s(u)), 2*u_2/(1+s(u)))
dist(S(u),S(v))^2 = 4*sum_j (u_j-v_j)^2 / ((1+s(u))*(1+s(v))).
```

分母正値を証明したうえで有理式を正規化して恒等式を証明した。各座標誤差が `|u_j-v_j|<=e`、`e>0` なら、分母が1以上であることから `dist^2<=12*e^2<16*e^2`、したがって厳密な開球条件 `dist<4e` が得られる。

## CLOSED — コンパクト性で選択しない明示的な有理中心族

元球面の第一座標が非負なら、逆チャート `u=(x_1,x_2,x_3)/(1+x_0)` は `[-1,1]^3` に入る。負側は元AGSの対蹠写像で扱う。任意の自然数 `N>0` と `x in [-1,1]` に対して

```text
k = Nat.floor(N*(x+1)),  0<=k<=2N,
|x-(k/N-1)| < 1/N
```

を証明した。両端点 `x=-1,1` も含む。ここから中心族を次の有限添字と式で指定する。

```lean
meshIndex N := Bool × (Fin 3 → Fin (2*N+1))
meshParameters N a j := ((a j).val : ℚ) / (N : ℚ) - 1
originalMeshCenter N i :=
  originalSignedCenter i.1 (meshParameters N i.2)
```

元ADS/ADTの球面・SU(2)対応と真正弦距離の等長性を介し、**すべての元SU(2)元は、この指定された中心族の半径 `4/N` の真正弦距離開球で覆われる**と形式証明した。中心集合の指定に、稠密性からの有理点選択やコンパクト性による有限部分被覆選択を用いない。各中心は元AGLの厳密な有理座標Type証拠を持つ。

有限添字数は `2*(2N+1)^3`。`N=128` では **33,949,186個の添字**である。チャート間で像が重複し得るため、相異なる群要素の個数とは主張しない。

## CLOSED — 元Borelセル・真正Haar証明書への接続

指定中心族を有限再添字付けし、既存AGHの元first-center Borelセルと全空間リンクの直積を用いて `originalSpatialGrid` を構成した。AHFの元plaquette数と元正向きリンク数の一致から、認証空間半径は厳密に

```text
R_H(N) = 4*p_H/N.
```

原点上の元空間リンクを構成して `p_H>0` を証明し、`N=128` に対して

```text
R_H(128)=p_H/32 < p_H/24
```

を得た。既存AGUのprecision-indexedデータへ接続し、任意の正有理Haar質量総幅予算epsとともに、**このデータの全セルがAHFの必要半径閾値未満**であることを証明した。新しい認証格子を追加したのであり、旧original24証明書や元物理モデルを上書きしていない。

## 明示的構成と未計算部分の境界

本結果は、中心族を明示式で指定し、その被覆・半径を証明した結果である。`Fintype.equivFin` による有限再添字付けと、AGQによる真のHaar質量の有理包含区間選択には古典的構成が残る。Haar質量を数値評価したこと、AGPの巨大な全直積表を実際に列挙・積分したこと、計算量が実用的であることは主張しない。

AHFの半径条件は必要条件であって十分条件ではない。`R_H(128)<p_H/24` は、AHFで特定した粗い認証半径による強制棄却の条件を外すが、**正または負checkerがtrueになることはまだ証明していない**。

## OPEN / NEXT — AHH

次の焦点は、元の真正Haar質量・Wilson作用・centered source・kernelの具体的な認証、または同じ元Haar積分のモーメントや相殺構造を使ったより鋭い評価で、実際の有限体積符号証人を得ることである。明示格子の存在を非零transferの存在へ読み替えない。

実際の非零signed-transfer、二符号殻、H一様coercivity、Hamiltonian gap、連続体4D Yang–Mills質量ギャップは、本結果では未証明のまま保持する。

[AHG Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/885c00a530c27f4abc18c32d5c1ce09a90b25020/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExplicitStereographicMeshV5_PZ37AHG.lean)。本記録を新規ファイルとして追加する。今回はREADME・ROADMAPを更新せず、両ブランチそれぞれの旧本文と過去の正式証明記録を保持する。文書専用PRでStrict Leanは起動しない。
