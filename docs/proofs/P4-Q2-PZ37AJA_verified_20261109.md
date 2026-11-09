# P4-Q2-PZ37AJA — 元の正規化ZW物理源像の定量的Haar-L²下界

2026年11月9日 JST。Lean定理の唯一のcanonical正本は `itakura-hidetoshi/4d-mass-gap` の `formal/real-hilbert-uniform-coercive-strong-limit`。この文書は機械検証を受けた定理の条件・署名・来歴を記録するが、記録本文自体はLeanの証明ではない。

[統合済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/e5beaef8120445c216753125ec31cd8c86a852ed/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNormalizedSourceQuantitativeHaarL2V5_PZ37AJA.lean) ／ [Lean定理PR #6575](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6575)。

## 1．元の物理対象と量化

元の完全 SU(2) Wilson one-slab 作用、左右境界の空間halfweight、真正product-Haar確率測度 `μ_H`、符号付きZW Gauss-law物理L²源 `f_{0,H}`、元の物理transfer `P_{H,β}`、既存の元物理ノルムによる正規化 `N_{H,β}=P_{H,β}/‖P_{H,β}‖` を一切変更しない。有限Hごとに境界空間と物理Hilbert空間は異なる。

`u_{H,β}` はAIWで定めた元の指定連続積分代表、`m_{H,β}>0` は元のAIG余裕を同じ物理作用素ノルムで割った正規化余裕、`R_{H,β}={B:u_{H,β}(B)<-m_{H,β}}` はAIGの元の厳密負領域と同一の集合である。

## 2．新しい形式定理

任意の有限 `H∈ℕ`、任意の `β>0` に対して、真正Haar実測度 `Measure.real μ_H R` を用いる**定量的な二乗ノルム下界**

\[
\boxed{
m_{H,\beta}^{\,2}\;\operatorname{Measure.real}(\mu_H,R_{H,\beta})
\ \le\
\|N_{H,\beta} f_{0,H}\|_{L^2}^{\,2}
}
\]

がLeanで成立する。別の定理で、元の余裕と元の厳密負領域の真正Haar測度がともに正であることから、左辺の**厳密正値**を証明した。これにより各有限H・各β>0での明示的な正の数式による下界を得た。平方根を取ったノルム不等式は数学的帰結として読めるが、その表現の新たなLean宣言があるとは主張しない。

この境界は `H,β` に依存する。`Measure.real μ_H R` の全正結合・全体積共通の正の数値下界は認証していない。AITの半Haar下界を全正結合へ昇格させない。

## 3．型付き証明の接続

まず一般の有限測度実L²に関して、可測集合 `s`、余裕 `m≥0`、`f∈Lp ℝ 2 μ`、指定代表 `u` について、`(fun x => f x)=ᵐ[μ]u` かつ `∀x∈s,u(x)<-m` を**明示的な仮定**として、

\[
m^2\,\operatorname{Measure.real}(\mu,s)\le \|f\|^2
\]

を証明した。この一般補題では `L2.integrable_inner (𝕜 := ℝ) f f` と既存の `realL2_norm_sq_eq_integral_norm_sq` を用いて、集合上の点ごとの二乗下界を全測度の実L²ノルムへ結ぶ。

次にAIWの**既存作用素出力のHaar-a.e.代表等式**を利用し、AIGの元の厳密負領域の可測性と、AIZの元負領域の正Haar測度を**同じH・β・元measure・元source**に合わせて適用した。これは任意のL²代表に全点での符号を仮定したものではない。

## 4．追加したLean宣言（3定理）

| 名前空間／宣言 | 形式化した内容 |
|---|---|
| `MGAP4D.MathlibAnalytic.realL2_norm_sq_ge_margin_sq_mul_realMeasure` | 有限測度L²、指定a.e.代表、可測集合の厳密負余裕から定量的二乗ノルム下界 |
| `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJA_originalNormalizedPhysicalSource_norm_sq_ge_margin_measure` | 元のWilson/ZW物理L²源像の真正margin×Haar質量下界 |
| `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJA_originalQuantitativeHaarL2_certificate_pos` | その元の証明書の各有限H・全正結合での厳密正値 |

新規Leanファイルは `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNormalizedSourceQuantitativeHaarL2V5_PZ37AJA.lean`。168行追加・削除0、3定理、追加定義0。3つの`#print axioms`を新規定理ごとに独立出力した。

## 5．固定環境とimports

Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 固定。直接importsは統合済みAIZ、新規ではない既存`RealL2ExternalTensor`、固定mathlibの`Mathlib.MeasureTheory.Integral.Bochner.Set`、`Mathlib.Tactic`。`autoImplicit false`／既存heartbeat・synthInstance上限を保持。既存の元Wilson物理定義・元measure・source・公開root・manifest・workflow・旧Leanを一切変更していない。

## 6．CI失敗、構造診断、最終認証

初回source `b23d6bebf164ddda13b92a00fdca81f1e123abd9` の [CI #42607467139](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42607467139) は**失敗・未認証**。53行 `L2.integrable_inner f f` で内積のスカラー型引数が未確定となり、型クラス `InnerProductSpace ?m ℝ` が解決できなかった。エラー回復からの下流`sorryAx`を証明と認めていない。

新規Lean全文168行と4 imports、AIW a.e.橋、AIG可測性・正測度、AIZ依存署名、固定mathlibのL²内積積分とset integral APIを照合。定理の仮定・署名・物理対象は変更せず、53行だけ `L2.integrable_inner (𝕜 := ℝ) f f` と型引数を明示した。修正版source `a4cd620ea2c153d2cf2c5dbc5b93d9e2f89b1f9b`。

| 検証 | 修正版Exact-source | 統合後自動push |
|---|---|---|
| CI | [#42608468069](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42608468069) | [#42609883742](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42609883742) |
| イベント／結果 | pull_request / SUCCESS | push / SUCCESS |
| HEAD | `a4cd620ea2c153d2cf2c5dbc5b93d9e2f89b1f9b` | `e5beaef8120445c216753125ec31cd8c86a852ed` |
| Lean主job | `129130363135` SUCCESS | `129135281315` SUCCESS |
| 独立completion receipt | `129134785751` SUCCESS | `129137820801` SUCCESS |
| Lean依存閉包 | 11,415/11,415 | 11,415/11,415 |
| 公理出力 | 3/3、標準3公理のみ | 3/3、標準3公理のみ |
| 新規Lean warning/error | 0/0 | 0/0 |
| AJAの`sorryAx` | なし | なし |

実ログで3定理の公理依存が`propext`、`Classical.choice`、`Quot.sound`のみであること、変更sourceのwarning/errorが0であることを照合した。独立receiptは別Lean kernelによる二重証明ではなく、実行結果の受領記録である。

## 7．Git来歴・同一tree照合

| 対象 | SHA |
|---|---|
| AJA開始formal HEAD | `112c4ee90055fe780720efea248e5fe2242a7ad5` |
| 初回未認証source | `b23d6bebf164ddda13b92a00fdca81f1e123abd9` |
| 最終認証source | `a4cd620ea2c153d2cf2c5dbc5b93d9e2f89b1f9b` |
| 実test-merge | `e40341db30e8cf0c2ac61f93a11688ff492485ef` |
| 正式Lean定理squash | `e5beaef8120445c216753125ec31cd8c86a852ed` |
| source／test-merge／squash共通Git tree | `28b728a8dd9f387ff053f21db03f6ec80e7296fe` |
| 新規Lean blob | `08f067c5e0c5db6d36c8aeb37982d3b43cdc3c2c` |

squashの親はAJA開始formal HEADであり、source/test-merge/squashのtreeが一致した。定理の認証と文書記録を区別する。文書専用PRでStrict Leanを手動起動しない。

## 8．障害と次の研究

**AJAで得たのは実際の元物理Hilbert L²ノルム二乗に対する各H・βで正の証明書である。** 既存AIXの元正規化余裕は特定結合windowでHとともに0へ収束しうる。したがって本証明書の正値から体積一様な真の振幅下界、実際の振幅極限、励起sector非零性、全物理Hilbert coercivity、Hamiltonian spectral gap、4D連続体Yang–Mills mass gapは証明されない。

次段 `AJB` 候補は、元のtop eigenspace（既存`PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceContraction`）と元ZW源の**実際のtop射影／直交成分**の型付き接続を個別に調査すること。元源にtop直交性を仮定で追加せず、射影公式・有限体積のノルム分解から認証可能な範囲を構成する。次段でもPreference ⇏ Descent ⇏ Authorityに相当する条件未充足の大域化を避ける。
