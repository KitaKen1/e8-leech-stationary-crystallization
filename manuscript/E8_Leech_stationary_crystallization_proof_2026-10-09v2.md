# E₈・Leech 定常点過程の定量結晶化：接続証明

作成日：2026-10-09  
対象資料：`E8コンサル.html`、とくに §§2, 4–6。  
位置づけ：CKMRV・BRR の既知定理を入力として、対象資料で未確定だった数学的接続を証明する研究ノート。Lean の実行・既存コードの監査・独立査読を行った記録ではない。文献上の新規性は別途確認を要する。

## 0. 結論と使用する文献

以下の証明は、資料の固定指数 1/13 の主張を、元の全点・期待値としての強度1・非エルゴード法則・閉球・正の許容余剰という量化のまま導く。同じ証明で位置誤差を任意の固定指数 0<γ<1/12 にできる。さらに非零 Gaussian 正混合への拡張と零余剰法則の分類を導く。

主要な接続は次の三つである。

1. CKMRV の原点値の式と厳密な正値性から、小半径の一様 slack を得る。Leech の小半径で発散する未正則化積分を用いない。
2. 有限格子部分集合との両方向近似を、剛体移動した「格子全体」への一方向距離に正確に書き換え、コンパクトな位相・回転パラメータで Borel 性を得る。
3. 周期充填の安定性を、期待密度欠損だけから定常充填へ移す。標本の密度収束もエルゴード性も使わない。

**[CKMRV]** H. Cohn, A. Kumar, S. D. Miller, D. Radchenko, M. Viazovska, *Universal optimality of the E8 and Leech lattices and interpolation formulas*, arXiv:1902.05438。参照箇所は Lemma 6.2、Proposition 6.1、式 (6.1)、(6.2)、(6.4)(1)、および §5 で構成・検証された生成関数の滑らかさとコンパクトパラメータ上の Schwartz 評価。参照した PDF の印刷頁81–86。

**[BRR]** K. J. Böröczky, D. Radchenko, J. P. G. Ramos, *A quantitative stability result for the sphere packing problem in dimensions 8 and 24*, arXiv:2303.07908v2。Theorems 1.5/1.6 が周期安定性入力。Theorems 1.1/1.2 に述べられた球充填最適性から周期中心密度 ≤1 を使う。印刷頁2–4。

本文の接続補題とその証明は、本ノートの導出であり、これらの文献にそのまま書かれていると主張するものではない。

## 1. 正確な定理

d∈{8,24} とし、Λ は余体積1の E₈ または Leech 格子とする。最短非零ベクトル長を r₀ と書く。したがって r₀=√2 または2である。

Ξ は ℝᵈ 上の単純・局所有限な定常点過程で、強度は期待値の意味で1とする。Q=[0,1)ᵈ と置き、順序付きエネルギーを

\[
\mathcal E_s(\mu)=\mathbb E_\mu\sum_{x\in\Xi\cap Q}\sum_{y\in\Xi\setminus\{x\}}|x-y|^{-s},
\qquad L_s=\sum_{z\in\Lambda\setminus\{0\}}|z|^{-s}
\]

で定義する。s>d とする。内側の点は Q の外も含む。係数1/2は入れない。

**定理。** 任意の固定 γ∈(0,1/12) に対し、d,s,γ のみに依存する C>0 と 0<δ₀<exp(−e) が存在する。任意の上記 μ と 0<δ<δ₀ について

\[
\mathcal E_s(\mu)\le L_s+\delta
\]

ならば、R=log(1/δ)/log log(1/δ) として、次を同時に満たす配置の集合 G は Borel であり、μ(G)≥1−CR^(−1/2) である。

\[
X=\Xi\cap\overline B_R,\qquad
\exists\Phi\text{ Euclidean isometry},\ \exists Z\subset\Lambda\text{ finite}:
\quad d_H(X,\Phi Z)\le C\delta^\gamma,
\]

\[
\#X\ge (1-CR^{-1/2})\operatorname{vol}(\overline B_R).
\]

非空有限集合についての d_H は通常の Hausdorff 距離である。空集合の場合は元資料の二つの全称命題によって解釈すればよい。十分小さい δ では点数下界が正なので、良い事象上では空集合の問題は生じない。

γ=1/13 とすれば元資料の量化を得る。この場合 C,δ₀ の依存先は d,s だけとなる。Z の格子像が観測球内に含まれることは要求しない。

## 2. 定常 Schwartz LP の直接証明

### 2.1. 局所二次モーメントと絶対可積分性

N_Q=#(Ξ∩Q) とする。Q の直径は √d なので

\[
N_Q(N_Q-1)\le d^{s/2}\sum_{x,y\in\Xi\cap Q,\ x\ne y}|x-y|^{-s}.
\]

ゆえに

\[
M:=\mathbb E N_Q^2\le1+d^{s/2}\mathcal E_s(\mu)<\infty.
\]

Q+k, k∈ℤᵈ に対する点数を N_k とすると、定常性と Cauchy–Schwarz より E[N_0N_k]≤M。したがって任意の Schwartz 関数 f について

\[
\mathbb E\sum_{x\in\Xi\cap Q}\sum_{y\in\Xi}|f(y-x)|
\le M\sum_{k\in\mathbb Z^d}\sup_{u\in k+[-1,1]^d}|f(u)|<\infty.
\]

この評価は、後の極限で符号付き f を扱う根拠にもなる。

### 2.2. Fourier 非負性からの不等式

f は実偶 Schwartz 関数で、Fourier 変換は

\[
\widehat f(\xi)=\int_{\mathbb R^d}f(x)e^{-2\pi i x\cdot\xi}\,dx
\]

と規格化し、\widehat f≥0 を仮定する。有限箱 W_L=[0,L)ᵈ において

\[
\sigma_L=\sum_{x\in\Xi\cap W_L}\delta_x-\mathbf1_{W_L}\,dx
\]

と置く。Fourier 反転と Fubini により、各標本で

\[
\iint f(x-y)\,d\sigma_L(x)d\sigma_L(y)
=\int\widehat f(\xi)|\widehat{\sigma_L}(\xi)|^2\,d\xi\ge0.
\]

期待値を取り、強度1を使って交差項を計算すると

\[
\mathbb E\sum_{x,y\in\Xi\cap W_L}f(x-y)
\ge\int_{W_L}\int_{W_L}f(x-y)\,dxdy.\tag{2.1}
\]

左辺の大箱極限を説明する。対角を含む換算点対測度 β を

\[
\int g(u)\,d\beta(u)=\mathbb E\sum_{x\in\Xi\cap Q}\sum_{y\in\Xi}g(y-x)
\]

で定義する。定常性から、点対の (x,y−x) 座標での期待測度は dx⊗β となる。具体的には、差分変数を有界 Borel 集合に制限したとき x 側の測度が局所有限かつ平行移動不変なので Lebesgue 測度の定数倍となり、単調類で積測度表示が従う。

(2.1) を |W_L| で割ると左辺は

\[
\int f(u)\,\frac{|W_L\cap(W_L-u)|}{|W_L|}\,d\beta(u).
\]

重みは0以上1以下で、各固定 u に対して1へ収束する。2.1節の絶対可積分性から支配収束を適用できる。右辺にも同じ議論を Lebesgue 測度で適用する。したがって

\[
f(0)+\mathcal P_\mu(f)\ge\widehat f(0),\qquad
\mathcal P_\mu(f):=\mathbb E\sum_{x\in\Xi\cap Q}\sum_{y\ne x}f(y-x).\tag{2.2}
\]

これが必要な定常 LP である。エルゴード性や標本ごとの強度は一度も使っていない。対角を f(0) として除いたので、規格化は元資料の順序付きエネルギーと一致する。

## 3. CKMRV から固定コンパクト区間の slack を抽出する

### 3.1. Gaussian 入力と校正

α>0 に対して

\[
g_\alpha(r)=e^{-\alpha r^2},\qquad
f_\alpha(x)=F(i\alpha/\pi,x),\qquad
h_\alpha(r)=g_\alpha(r)-f_\alpha(r)
\]

と置く。CKMRV Lemma 6.2 とその構成により、f_α は実 radial Schwartz、\widehat f_α≥0、h_α≥0。非零 r で h_α(r)=0 となるのは Λ の非零ベクトル長だけである。関数族は (α,x) に関して滑らかで、α のコンパクト区間上で必要な Schwartz 評価が一様に成り立つ。

Λ の自己双対性、格子半径での f_α=g_α と \widehat f_α=0、および Poisson 和公式により

\[
\widehat f_\alpha(0)-f_\alpha(0)
=\sum_{z\in\Lambda\setminus\{0\}}g_\alpha(|z|)=:L_\alpha.\tag{3.1}
\]

2節を適用すると

\[
\mathcal P_\mu(g_\alpha)-L_\alpha\ge\mathcal P_\mu(h_\alpha)\ge0.\tag{3.2}
\]

各固定 α の Gaussian エネルギーは2.1節の評価から有限である。

### 3.2. 原点の正値性が小半径を閉じる

CKMRV Lemma 6.2 の証明の関数等式は、y=π/α として

\[
h_\alpha(r)=y^{d/2}\widetilde F(iy,r).
\]

また同論文の式 (6.1) は

\[
\widetilde F(iy,0)=\frac{2\pi y}{d}
\sum_{z\in\Lambda\setminus\{0\}}|z|^2e^{-\pi y|z|^2}.
\]

したがって

\[
h_\alpha(0)=\frac{2\pi}{d}y^{d/2+1}
\sum_{z\in\Lambda\setminus\{0\}}|z|^2e^{-\pi y|z|^2}>0.\tag{3.3}
\]

これは d=24 でもそのまま有効である。さらに、Leech の √2 は非零格子ベクトル長ではないので、Lemma 6.2 は h_α(√2)>0 も与える。

I=[π/4,π/3] と置く。joint continuity と厳密正値性から

\[
m_0:=\min_{\alpha\in I,\ 0\le r\le7r_0/8}h_\alpha(r)>0.\tag{3.4}
\]

ここでは、r=0 や Leech の r≤√2 に未正則化 Laplace 積分を代入していない。CKMRV が構成済みの正則化された関数、証明済みの厳密正値性、原点値の式を使っている。

### 3.3. 最短半径の近傍だけに正の Laplace 積分を使う

CKMRV の式 (6.2)、(6.4)(1) により、7r₀/8≤r<r₀ で

\[
h_\alpha(r)=4y^{d/2}\sin^2(\pi r^2/2)
\int_0^\infty\widehat K(iy,iv)e^{-\pi r^2v}\,dv.
\]

d=24 の場合、この区間は r≥7/4>√2 なので通常の積分の収束域に入る。

I に対応する y は [3,4] に属する。矩形 [3,4]×[1,2] 上で kernel は連続かつ正なので

\[
m_K:=\min_{3\le y\le4,\ 1\le v\le2}\widehat K(iy,iv)>0.
\]

r₀² は2または4であり、D=r₀²−r² は上記の r の範囲で [0,1] に入る。sin(πD/2)≥D より

\[
\sin^2(\pi r^2/2)=\sin^2(\pi D/2)
\ge D^2\ge r_0^2(r_0-r)^2.
\]

積分を v∈[1,2] に制限し、r²≤4 を使えば

\[
h_\alpha(r)\ge c_1(r_0-r)^2,\qquad
c_1=4\,3^{d/2}m_K e^{-8\pi}r_0^2>0.\tag{3.5}
\]

### 3.4. Riesz への接続で区間外の gap を失わない

\[
w_s(\alpha)=\frac{\alpha^{s/2-1}}{\Gamma(s/2)},\qquad
V_s(r)=\int_I w_s(\alpha)h_\alpha(r)\,d\alpha.
\]

V_s は非負連続である。Gamma 積分表示と Tonelli により

\[
\mathcal E_s=\int_0^\infty w_s(\alpha)\mathcal P_\mu(g_\alpha)\,d\alpha,
\qquad L_s=\int_0^\infty w_s(\alpha)L_\alpha\,d\alpha.
\]

(3.2) は全 α>0 で成り立つ。両積分が有限なので差を取り、まず全域の非負 gap を確保してから I だけの費用を残すことができる。

\[
\boxed{\mathcal P_\mu(V_s)\le\mathcal E_s-L_s\le\delta.}\tag{3.6}
\]

区間外の Gaussian の不等式を証明せず捨てる操作ではない。また ∫₀∞w_s f_α を Schwartz 関数として扱う必要はない。

w_I=∫_I w_s(α)dα>0 とすると、(3.4)–(3.5) より適当な a₀,b₀>0 が存在して

\[
0<r\le r_0/2\Longrightarrow V_s(r)\ge a_0,
\]

\[
r_0/2\le r<r_0\Longrightarrow V_s(r)\ge b_0(r_0-r)^2.
\]

たとえば a₀=w_I m₀、b₀=min(w_I m₀/r₀²,w_I c₁) でよい。したがって

\[
\kappa:=\min(4a_0,b_0r_0^2)>0
\]

と置けば

\[
0<t\le\tfrac12,\quad0<r<r_0(1-t)
\Longrightarrow V_s(r)\ge\kappa t^2.\tag{3.7}
\]

元資料の φ_s として、この固定区間の V_s を使えばよい。

## 4. 局所結晶事象の Borel 性：有限 Z の射影を回避する

P は Λ の閉基本平行多面体とする。P はコンパクトで、任意の Λ の剛体移動は

\[
Q(\Lambda+u),\qquad Q\in O(d),\ u\in P
\]

と表せる。パラメータ空間 T=O(d)×P はコンパクト距離空間である。

有界有限集合 X に対して

\[
D_\Lambda(X)=\min_{(Q,u)\in T}\max_{x\in X}
\operatorname{dist}(Q^Tx-u,\Lambda)
\tag{4.1}
\]

と定義する。X=∅ の最大値は0とする。固定 X について目的関数は連続なので最小値が実現される。

**同値性。**

\[
D_\Lambda(X)\le\varepsilon
\iff
\exists\Phi\text{ isometry},\ \exists Z\subset\Lambda\text{ finite},
\quad d_H(X,\Phi Z)\le\varepsilon.\tag{4.2}
\]

右から左は明らか。左から右は、最小値を実現する Q,u を取り、各 x∈X に対して最近格子点 z_x∈Λ を一つ取ればよい。Λ は閉離散なので最近点は存在する。Z={z_x:x∈X} と Φ(z)=Q(z+u) を取れば、各 x は ΦZ に近く、各 z∈Z はそれを選んだ x に近い。重複する最近点があっても問題ない。

これが使えるのは、元資料で Z が任意の有限部分集合であり、ΦZ が球内に含まれることも、全単射も要求していないためである。結論を弱めた書き換えではない。

可算稠密集合 {(Q_j,u_j)} を T に固定する。X=Ξ∩閉球B_R に対し

\[
D_\Lambda(X)=\inf_j M_j(\Xi),\qquad
M_j(\Xi)=\max_{x\in\Xi\cap\overline B_R}
\operatorname{dist}(Q_j^Tx-u_j,\Lambda).
\]

v≥0 に対して

\[
\{M_j>v\}=
\left\{\Xi\left(\overline B_R\cap
\{x:\operatorname{dist}(Q_j^Tx-u_j,\Lambda)>v\}\right)\ge1\right\}.
\]

右辺は有界 Borel 集合の点数を用いた事象なので Borel。よって D_Λ も Borel である。点数下界も Borel であり、元資料の LocalCrystal 全体が Borel となる。

中心 a を変数に含めても、(Ξ,a)↦Ξ−a とパラメータ付き計数写像の Borel 性から同じ結論が従う。有限緩衝周期化も、各有界 Borel 集合の点数を周期コピーの可算和として書けるため Borel である。

閉球の境界での連続性は不要である。Φ や Z の可測選択、解析集合の射影、測度の完備化も不要である。

## 5. 周期 BRR から定常 BRR への移送補題

BRR の定数をまとめ、

\[
b_\eta=B_dR(\eta)^{-1/2},\qquad
\varepsilon_\eta=E_d e^{c_dR(\eta)}\eta^{1/4}
\]

と書く。d=8 では M_d=2²⁰、d=24 では M_d=2¹⁴⁰ とする。

**補題。** Y は定常点過程で、最小点間距離 r₀、有限強度 ρ を持つとする。このとき ρ≤1。η が BRR の許容範囲にあり、球 K=閉球B_r が

\[
R(\eta)\le r,\qquad 2r\le M_dR(\eta)
\]

を満たせば、元の全点 Y∩K に対する BRR の局所結晶結論と点数下界が成立しない確率は

\[
\boxed{\mathbb P(\mathrm{failure})
\le b_\eta+\frac{1-\rho}{\eta}.}\tag{5.1}
\]

**証明。** h=r₀ とし、L>2h に対して

\[
W_L=[0,L)^d,\quad W_L^-=[h,L-h)^d,\quad
P_L(Y)=(Y\cap W_L^-)+L\mathbb Z^d.
\]

同じ周期内では元の hard core があり、異なる周期の点間には少なくとも一座標で2hの緩衝があるので P_L(Y) は最小距離 r₀ の周期充填である。その中心密度は

\[
D_L(Y)=\frac{\#(Y\cap W_L^-)}{L^d}\le1.
\]

最後の不等式は、周期球充填の厳密な密度上界である。定常性から

\[
\mathbb ED_L=\rho\left(1-\frac{2h}{L}\right)^d.
\tag{5.2}
\]

L→∞ としてまず ρ≤1 が従う。1−D_L が非負なので Markov により

\[
\mathbb P(D_L<1-\eta)
\le\frac{1-\rho(1-2h/L)^d}{\eta}.\tag{5.3}
\]

Y と独立に、U_L を W_L 上一様とする。D_L≥1−η の各標本について BRR を適用する。4節で示した同時 Borel 性により積空間で積分でき、周期配置についての悪い事象の確率は (5.3) の右辺+b_η 以下である。

U_L が W_L の境界から距離 h+r より内側なら、球 U_L+K 内で P_L(Y) と Y の元の全点が一致する。除外される中心の割合は

\[
\le1-\left(1-\frac{2(h+r)}{L}\right)^d=O_d((h+r)/L).
\]

一方、定常性により Y−U_L の法則は Y の法則と同じである。したがって Y の原点での固定局所事象について

\[
\mathbb P(\mathrm{failure})
\le b_\eta+
\frac{1-\rho(1-2h/L)^d}{\eta}+O_d((h+r)/L).
\]

左辺は L に依存しないので L→∞ として (5.1) を得る。これは標本密度の極限ではなく、既に計算した期待値と境界誤差の極限である。□

**有限 L の実装との関係。** この証明で L→∞ を使わず、最後の二つの有限 L 誤差を所望の予算以下にする共通の L を選んでもよい。元資料の単一標本・有限周期長の実装方針を維持できる。

## 6. 削除・微小拡大・元の全点の復元

0<t≤1/2 とする。距離 r₀(1−t) 未満に他の点を持つ点を全て削除し、残存過程を Y_t とする。削除判断は全空間の配置に対して行うので、観測窓の外の相手も正しく数える。

削除点の強度 q_t は (3.6)–(3.7) から

\[
q_t\le\mathbb E\sum_{x\in\Xi\cap Q}\sum_{y\ne x}
\mathbf1_{\{|x-y|<r_0(1-t)\}}
\le\frac{\delta}{\kappa t^2}.\tag{6.1}
\]

ここでも順序付き対を使っており、余分な係数1/2はない。薄化は可測かつ平行移動同変なので Y_t は定常で、強度は1−q_t、最小距離は r₀(1−t) 以上である。

\[
\lambda=(1-t)^{-1},\qquad Y'_t=\lambda Y_t
\]

とする。Y'_t は最小距離 r₀ の定常過程で、その強度は

\[
\rho_t=(1-q_t)(1-t)^d,
\qquad1-\rho_t\le q_t+dt.\tag{6.2}
\]

R=R(δ)、r=λR とし、5節を球B_rに適用する。得られる点数下界は

\[
\#(Y_t\cap\overline B_R)
=\#(Y'_t\cap\overline B_{\lambda R})
\ge(1-b_\eta)\lambda^d\operatorname{vol}(\overline B_R)
\ge(1-b_\eta)\operatorname{vol}(\overline B_R),\tag{6.3}
\]

ここでは δ を十分小さくして b_η<1 とした。

位置誤差の復元では、**格子側の Φ を拡大縮小しない**。X_t=Y_t∩閉球B_R とすると

\[
d_H(X_t,\lambda X_t)\le(\lambda-1)R\le2tR.
\]

同じ Φ,Z を用いて三角不等式を取れば

\[
d_H(X_t,\Phi Z)\le\varepsilon_\eta+2tR.\tag{6.4}
\]

Φ はもとの Euclidean 等長写像のままである。格子像が球外へ少し出ることは元の目標で許されている。

さらに、観測球内に削除点がある確率は

\[
\mathbb P((\Xi\setminus Y_t)\cap\overline B_R\ne\varnothing)
\le q_t\operatorname{vol}(\overline B_R).\tag{6.5}
\]

この事象の補集合では元の全点と残存点が観測球内で一致する。独立性を仮定せず和事象評価を取ると、(6.3)–(6.4) の結論が元の全点に対して成立しない確率は

\[
\boxed{
\le b_\eta+\frac{dt+\delta/(\kappa t^2)}{\eta}
+\frac{\delta}{\kappa t^2}\operatorname{vol}(\overline B_R).
}\tag{6.6}
\]

## 7. 指数を閉じる：任意 γ<1/12

\[
t=\delta^{1/3},\qquad
\beta=\frac{1+12\gamma}{6}\in(1/6,1/3),\qquad
\eta=\delta^\beta.
\]

ℓ=log(1/δ) とすると

\[
R(\delta)=\frac{\ell}{\log\ell},\qquad
R(\eta)=\frac{\beta\ell}{\log(\beta\ell)}.
\]

βℓ>e となるほど δ を小さくすれば

\[
\beta R(\delta)\le R(\eta)\le R(\delta).
\]

λ≤2 なので

\[
R(\eta)\le\lambda R(\delta),\qquad
\frac{2\lambda R(\delta)}{R(\eta)}\le\frac4\beta<24.
\]

したがって BRR の球の包含条件と直径条件を両次元で満たす。

位置誤差は

\[
\varepsilon_\eta=E_d\exp(c_dR(\eta))\delta^{\beta/4}
=\delta^{\beta/4-o(1)}.
\]

\[
\frac\beta4-\gamma=\frac{1-12\gamma}{24}>0
\]

なので、δ が十分小さいと ε_η≤Cδ^γ。また2tR=2δ^(1/3)R=o(δ^γ)。

確率については

\[
\frac t\eta=\delta^{1/3-\beta}
=\delta^{(1-12\gamma)/6}=o(R^{-1/2}),
\]

\[
\delta^{1/3}R^d=o(R^{-1/2}),\qquad
R(\eta)^{-1/2}\le\beta^{-1/2}R^{-1/2}.
\]

(6.6) と合わせて失敗確率 ≤CR^(−1/2)、点数損失 ≤CR^(−1/2)、位置誤差 ≤Cδ^γ が同時に従う。

すべての小ささ条件を有限個まとめて δ₀ を選び、全ての係数の最大を C に吸収する。この選択は d,s,γ のみに依存し、μ より先に行える。4節から目標事象自体が Borel なので、それを G と取る。これで1節の定理を得た。

### 元資料の 1/13 の選択

γ=1/13 なら β=25/78 であり、

\[
\frac\beta4-\frac1{13}=\frac1{312},\qquad
\frac13-\beta=\frac1{78}.
\]

したがって元資料の指数は整合している。δ を「真の余剰」そのものとする等式は使っていない。

γ=1/12 の端点はこの証明では得ていない。上の二つの正の指数余裕が消えるためであり、端点の成立・不成立を断定するものではない。

## 8. 非零 Gaussian 正混合

ν は (0,∞) 上の非零正 Borel 測度とし、

\[
p(r)=\int_{(0,\infty)}e^{-\alpha r^2}\,d\nu(\alpha),\qquad
L_p=\sum_{z\in\Lambda\setminus\{0\}}p(|z|)<\infty
\]

とする。エネルギー E_p は1節の r^(−s) を p(r) に置き換えて定義する。

L_p<∞ は p(r₀)<∞ を含み、任意の0<a≤b<∞について

\[
\nu([a,b])e^{-br_0^2}\le p(r_0)<\infty.
\]

したがって ν は局所有限で、ν≠0 から正質量を持つコンパクト区間 I=[a,b] を選べる。任意のD<∞と r≤D に対して

\[
p(r)\ge\nu(I)e^{-bD^2}>0.
\]

よって E_p<∞ から局所二次モーメントが得られ、2節が適用できる。

\[
V_p(r)=\int_I h_\alpha(r)\,d\nu(\alpha)
\]

を使い、全 α の (3.2) を ν で積分すると

\[
\mathcal P_\mu(V_p)\le E_p-L_p.
\]

3.2節の正値性・連続性は任意のコンパクト I に適用できる。最短半径近傍の二次下界にも同じ積分表示を使える。明示式の見かけ上の対角特異点を避けるなら、y∈[π/b,π/a] に対して v の積分を

\[
[V,V+1],\qquad V>\max(1,\pi/a,b/\pi)+1
\]

に制限すればよい。この矩形では y=v および y=1/v を避けられる。kernel の正値性と連続性から正の一様下界を取り、指数因子を e^(−πr₀²(V+1)) で下から抑える。

したがって (3.7) と同型の短距離費用が得られ、4–7節をそのまま適用できる。定数の依存先を d,p,γ に変えるだけでよい。ν が単一 Gaussian の原子測度でもよく、密度を持つ必要はない。

通常の有限値ポテンシャルとして述べるなら p(r)<∞ (r>0) を定義に含める。拡張値を許す場合も、L_p<∞ と E_p≤L_p+δ のもとでこの証明は有効であり、p=∞ の距離を持つ点対は有限エネルギー条件が排除する。

## 9. 零余剰法則の完全分類

E_s=L_s、または8節の E_p=L_p とする。7節の定量定理を γ=1/13 と δ_n=exp(−n⁸) に適用する。十分大きい n について閾値内にあり、

\[
R_n=\frac{n^8}{8\log n},\qquad
\sum_n R_n^{-1/2}<\infty.
\]

Borel–Cantelli より、ほとんど全ての配置で十分大きい全 n に対し、

\[
\Xi\cap\overline B_{R_n}\text{ がある }\Gamma_n=Q_n(\Lambda+u_n)
\text{ に距離 }C\delta_n^{1/13}\text{ 以内},
\]

\[
\#(\Xi\cap\overline B_{R_n})\ge(1-CR_n^{-1/2})\operatorname{vol}(\overline B_{R_n})
\tag{9.1}
\]

となる。Q_n∈O(d),u_n∈P と正規化し、コンパクト性で部分列極限(Q,u)を取る。各固定 x∈Ξ に距離の連続性を適用して

\[
\Xi\subset\Gamma:=Q(\Lambda+u).\tag{9.2}
\]

### 9.1. 包含する格子の一意性

余体積1の異なる二つのアフィン格子 Γ₁,Γ₂ の交わりは、空集合か、ベクトル格子 L₁∩L₂ の剰余類である。交わりの階数が d 未満なら密度0。階数 d なら、一方の格子での指数が2以上なので密度≤1/2である。指数1なら余体積が等しいため両アフィン格子は同一となる。

よって (9.1) を満たす Ξ が二つの異なる余体積1格子に含まれることはない。Γ は一意である。

### 9.2. 一意な格子を Borel かつ平行移動同変に取る

Λ の全等長像の空間 𝓛 は、点計数測度の vague 位相においてコンパクトである。実際、O(d)×P からの像であり、コンパクト台の連続試験関数に対する格子和は、パラメータに一様な有限個の格子点だけで計算されるため連続である。

関係 Ξ⊂Γ は点計数測度の大小 Ξ≤Γ と同値で、vague 位相で閉である。Γ 側がコンパクトなので、閉部分集合に証人を制限した存在条件も閉となる。

一意性の条件も Borel である。非一意性は、𝓛 上の距離を用いて「相互距離が1/m以上の二つの包含格子が存在する」という閉射影の可算和で表せる。一意性が成立する Borel 部分集合上では、任意の閉 C⊂𝓛 に対して

\[
\{\Xi:\Gamma(\Xi)\in C\}
=\{\Xi:\exists\Gamma\in C,\ \Xi\subset\Gamma\}
\]

と書けるので、Γ(Ξ) は Borel である。一意性から Γ(Ξ+a)=Γ(Ξ)+a が従う。従って、μ が誘導する格子点過程 Γ も定常である。

### 9.3. 期待強度1で欠損を全て除く

Λ の基本領域の直径から、全等長像について一様に

\[
\#(\Gamma\cap\overline B_R)
=\operatorname{vol}(\overline B_R)+O_\Lambda(R^{d-1})
\]

が成り立つ。これは、各格子点に対応する体積1の基本領域を球の内外に比較するだけで得られる。従って定常過程 Γ の強度は1である。

Ξ⊂Γ かつ両者の強度が1なので、任意の単位立方体 Q+k について

\[
\mathbb E\#((\Gamma\setminus\Xi)\cap(Q+k))=0.
\]

非負整数値のため、この個数はほとんど確実に0。k∈ℤᵈ の可算個を合わせて Ξ=Γ がほとんど確実に成り立つ。単に密度0の欠損まで許す結論ではなく、欠損そのものが存在しない。

### 9.4. 位相は Haar、向きは任意の混合

方向空間を O(d)/Aut(Λ) とする。Γ の方向の分布を σ と書く。固定方向 QΛ に対して、平行移動位相は ℝᵈ/QΛ の Haar 分布となる。

これは条件付き分布の可測性を別途追わなくても示せる。格子等長像のコンパクト空間上の任意の連続 F について、定常性により

\[
\mathbb E F(\Gamma)
=\mathbb E\frac1{|W_T|}\int_{W_T}F(\Gamma+a)\,da.
\]

各固定格子に対する右側の空間平均は、基本領域によるタイル分割と境界評価により、その方向の位相トーラス上の Haar 平均へ収束する。支配収束から法則の表示を得る。

したがって零余剰法則は正確に

\[
\boxed{\mu=\int_{O(d)/\operatorname{Aut}(\Lambda)}
\operatorname{Law}\bigl(Q(\Lambda+U)\bigr)\,d\sigma([Q]),
\quad U\sim\operatorname{Haar}(\mathbb R^d/\Lambda).}\tag{9.3}
\]

逆向きも明らかである。各被積分法則は定常・強度1で、等長不変なポテンシャルのエネルギーが格子値に等しい。回転不変性を仮定していないので σ が Haar である必要はない。

## 10. 監査結果と実装上の優先順位

### 主張ごとの判定

- 固定指数1/13：**既知結果で閉じる**。3–7節が元資料で不足していた接続証明。
- 任意の固定0<γ<1/12：**既知結果で閉じる**。7節。端点は主張しない。
- 非零 Gaussian 正混合：**既知結果で閉じる**。正 Borel 測度、(0,∞) 上の混合、有限格子エネルギーという条件のもとで8節が証明を与える。
- 零余剰の法則分類：**既知結果で閉じる**。定量定理に加えて、9節のコンパクト性・一意性・強度消去・位相平均を使う。
- 同じ定理の文献上の新規性：**未確定**。本ノートの導出と、未発表の新結果であるという主張は別である。
- 無条件 Lean 定理の成立：**このノートでは検証していない**。添付資料は入力付き合成を報告しており、元コード一式は今回の添付ではない。

### 最短の数学的依存図

```text
CKMRV Gaussian 補助関数・校正・厳密正値性
             │
             ├─ 原点式 (6.1) ＋ compactness
             ├─ 最短半径近傍の正 kernel 積分
             └─ 定常 Schwartz LP ＋ 正混合 Tonelli
                          ↓
                  固定区間 slack V
                          ↓
             短距離点の薄化 ＋ 微小拡大
                          ↓
        周期密度≤1 ＋ BRR 1.5/1.6
                          ↓
       定常 BRR 移送 ← コンパクト位相による Borel 性
                          ↓
          元の全点復元 ＋ 指数選択
                          ↓
             正確な目標 γ<1/12
                          ↓
              零余剰法則の分類
```

まず定理インターフェースとして固定する価値が高いのは、(i) 原点値を含むコンパクト区間短距離 slack、(ii) 式(4.2)と Borel 性、(iii) 定常 BRR 移送式(5.1)である。4–5節の新しい接続のために BRR の格子証人を可測選択する実装は不要である。

紙上の数学では、CKMRV が既に証明した小半径の解析接続を再構築する必要はない。ただし完全な Lean 証明では、引用した CKMRV/BRR の定理を、証明済み宣言として輸入するか形式化する必要がある。論文の引用を新しい公理として置くだけでは無条件化にならない。

HTML だけから Lean 移植の人時を信頼できる精度で再見積もることはできない。本ノートが削るのは、接続数学の不確定性と不要な証人選択・小半径の再解析であって、CKMRV と BRR の深い証明をカーネル検証へ移す全作業ではない。
