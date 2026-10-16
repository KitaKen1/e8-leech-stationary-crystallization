# E₈・Leech 定常結晶化：接続補題と紙上証明

2026-10-09

## 状態と資料の区別

入力資料：`E8コンサル(1).html`。以下は同資料の目標を変更せず、既刊の CKMRV と BRR を用いて接続を記述した紙上証明である。既刊の深い定理自体を再証明するものではない。Lean ソースはこの相談に添付されておらず、Lean ビルド・推移的公理監査・独立査読を実施したとの主張はしない。新規性・投稿先での評価も別途の検討事項である。

使用する一次資料：

- [C] H. Cohn, A. Kumar, S. D. Miller, D. Radchenko, M. Viazovska, *Universal optimality of the E8 and Leech lattices and interpolation formulas*, arXiv:1902.05438v3. 特に §5、Proposition 6.1、Lemma 6.2、その証明、式 (6.2)、(6.4)(1)。
- [B] K. J. Böröczky, D. Radchenko, J. P. G. Ramos, *A quantitative stability result for the sphere packing problem in dimensions 8 and 24*, arXiv:2303.07908v2. Theorems 1.1, 1.2, 1.5, 1.6。

本ノートで証明する接続は、これらの定理文そのものと区別する。

## 1. 目標

$d\in\{8,24\}$ とし、$\Lambda$ は余体積 1 の標準 E₈ または Leech 格子とする。最短長を $r_0=\sqrt2$ または $2$ と書く。$s>d$。

$\Xi$ は単純・局所有限な定常点過程で、強度は期待値の意味で 1 とする。エルゴード性、独立性、標本ごとの密度、元配置の最小距離は仮定しない。

$Q=[0,1)^d$ として、順序付きのエネルギーを

$$
\mathcal E_p(\mu)=\mathbb E_\mu\sum_{x\in\Xi\cap Q}\sum_{y\in\Xi\setminus\{x\}}p(|x-y|),
\qquad L_p=\sum_{z\in\Lambda\setminus\{0\}}p(|z|)
$$

と書く。Riesz の場合は $p(r)=r^{-s}$、$\mathcal E_s=\mathcal E_p$、$L_s=L_p$。

**定理。** $d,s$ のみに依存する $C>0$ と $0<\delta_0<\exp(-e)$ が存在する。$0<\delta<\delta_0$ と $\mathcal E_s\le L_s+\delta$ に対し、

$$R=R(\delta)=\frac{\log(1/\delta)}{\log\log(1/\delta)}$$

と置くと、確率 $\ge1-CR^{-1/2}$ の Borel 事象上で、元配置の全点

$$X=\Xi\cap\overline B(0,R)$$

について、有限 $Z\subset\Lambda$ と Euclidean 等長写像 $\Phi$ が存在し、

$$d_H(X,\Phi Z)\le C\delta^{1/13},\qquad
\#X\ge(1-CR^{-1/2})\operatorname{vol}(B_R)
$$

が同時に成り立つ。$\delta$ は実際の余剰と等しくなくてよい。

以下で証明する。

## 2. CKMRV から使用する入力

Fourier 変換は $\widehat f(\xi)=\int f(x)e^{-2\pi i\langle x,\xi\rangle}\,dx$ とする。

$g_\alpha(x)=e^{-\alpha|x|^2}$ に対する [C, Lemma 6.2] の実偶 radial Schwartz 関数を

$$f_\alpha(x)=F(i\alpha/\pi,x),\qquad h_\alpha=g_\alpha-f_\alpha$$

とする。既刊結果が与える性質は

$$h_\alpha\ge0,\qquad\widehat f_\alpha\ge0,$$

および $r>0$ において $h_\alpha(r)=0$ となるのは $\Lambda$ の非零ベクトル長に限る、という厳密な等号条件である。特に $0<r<r_0$ では $h_\alpha(r)>0$。24 次元の $r=\sqrt2$ もこの正値領域に含まれる。

格子が自己双対であること、補間条件、Poisson 和公式から

$$\widehat f_\alpha(0)-f_\alpha(0)=L_{g_\alpha}.\tag{2.1}$$

また [C, Lemma 6.2 の証明] の双対性は

$$h_\alpha(r)=\left(\frac\pi\alpha\right)^{d/2}
 \widehat f_{\pi^2/\alpha}(r).\tag{2.2}$$

[C, §5] の構成はパラメータと空間変数に関する連続性と、コンパクトなパラメータ区間上での一様 Schwartz 評価を与える。従って以下のパラメータ積分・可測性・コンパクト最小値が使える。

### 2.1 原点の正値性：特殊値計算を使わない接続

Fourier 反転と Fourier 非負性から

$$f_\beta(0)=\int_{\mathbb R^d}\widehat f_\beta(\xi)\,d\xi\ge0.$$

よって (2.1) は

$$\widehat f_\beta(0)=f_\beta(0)+L_{g_\beta}\ge L_{g_\beta}>0$$

を与える。(2.2) に代入して

$$h_\alpha(0)\ge\left(\frac\pi\alpha\right)^{d/2}
 L_{g_{\pi^2/\alpha}}>0.\tag{2.3}$$

従って原点の正値性のために、theta 級数の微分公式や [C, (6.1)] の特殊値を別途実装する必要はない。

特に $I=[\pi/4,\pi/3]$、$y=\pi/\alpha\in[3,4]$ とし、長さ $r_0$ の非零格子ベクトルを一本だけ残すと

$$h_\alpha(0)\ge 3^{d/2}e^{-4\pi r_0^2}\qquad(\alpha\in I).\tag{2.4}$$

原点に関しては一本のベクトルが正の証明書になる。

### 2.2 最短長近傍の二次下界

[C, (6.2), (6.4)(1)] により、$7r_0/8\le r\le r_0$ では

$$h_\alpha(r)=4y^{d/2}\sin^2(\pi r^2/2)
 \int_0^\infty\widehat K(iy,iv)e^{-\pi r^2v}\,dv.$$

24 次元でもこの半径区間は $r>\sqrt2$ にあるので、ここでは未正則化の正積分が使える。小半径へこの積分を延長することはしない。

核は $[3,4]\times[1,2]$ 上で連続かつ厳密に正なので、

$$B=\min_{3\le y\le4,\ 1\le v\le2}\widehat K(iy,iv)>0.$$

この矩形では核の表示の極を避けている。$r^2\le4$ だから積分区間 $[1,2]$ の寄与は $Be^{-8\pi}$ 以上。

さらに $\Delta=r_0^2-r^2$ とすると $0\le\Delta\le1$ で、$r_0^2$ は偶整数である。従って

$$\sin^2(\pi r^2/2)=\sin^2(\pi\Delta/2)
 \ge\Delta^2\ge r_0^2(r_0-r)^2.$$

ゆえに

$$h_\alpha(r)\ge c_1(r_0-r)^2,\quad
 c_1=4\,3^{d/2}B e^{-8\pi}r_0^2>0.\tag{2.5}$$

### 2.3 小半径と中間領域

既刊の厳密な等号条件、(2.3)、連続性を合わせると

$$m=\min_{\alpha\in I,\ 0\le r\le7r_0/8}h_\alpha(r)>0.$$

したがって $c_0=\min\{m/r_0^2,c_1\}>0$ と置けば

$$h_\alpha(r)\ge c_0(r_0-r)^2\quad
 (\alpha\in I,\ 0\le r\le r_0).\tag{2.6}$$

この段階では Leech の小半径の解析接続を再実行しない。[C, Lemma 6.2] の全半径にわたる正値性を使う。つまり解析接続の深い依存を消したのではなく、既刊の正確な定理の内部に置いている。全 Lean 化に際しこの入力が未形式化なら、その依存は依然として残る。

## 3. 定常 LP：非エルゴード法則への接続

### 3.1 局所二次モーメント

$N_Q=\#(\Xi\cap Q)$ とする。Riesz エネルギーが有限なら

$$N_Q(N_Q-1)\le d^{s/2}
\sum_{x\in\Xi\cap Q}\sum_{y\in\Xi\cap Q\setminus\{x\}}|x-y|^{-s},$$

ゆえに $\mathbb E N_Q^2<\infty$。平行移動不変性と Cauchy–Schwarz により、任意の整数平行移動 $k+Q$ に対して

$$\mathbb E[N_QN_{k+Q}]\le\mathbb E N_Q^2.$$

Schwartz 関数の減衰を単位箱ごとに足せば、任意の Schwartz 関数 $f$ の順序付き点対和は絶対可積分である。

### 3.2 中心化した有限測度の正定値二次形式

$Q_T=[-T/2,T/2)^d$ とし、有限符号付き測度

$$M_T=1_{Q_T}(\Xi-dx)$$

を考える。実偶 Schwartz 関数 $f$ が $\widehat f\ge0$ を満たすなら、Fourier 反転から各標本について

$$\iint f(x-y)\,dM_T(x)dM_T(y)
 =\int\widehat f(\xi)|\widehat M_T(\xi)|^2\,d\xi\ge0.$$

期待値を取り、強度 1 により交差項を計算すると

$$\mathbb E\sum_{x,y\in\Xi\cap Q_T}f(x-y)
 \ge\iint_{Q_T\times Q_T}f(x-y)\,dx\,dy.$$

体積で割り $T\to\infty$ とする。定常二次モーメント測度で表すと左辺には箱の重なり比

$$w_T(z)=\operatorname{vol}(Q_T\cap(Q_T-z))/T^d$$

が掛かる。$0\le w_T\le1$、$w_T(z)\to1$ と上の絶対可積分性により優収束が使える。対角項を分けて

$$\mathcal E_f(\mu)\ge\widehat f(0)-f(0).\tag{3.1}$$

これが本件で必要な定常 LP である。標本ごとの強度、空間エルゴード定理、エルゴード分解を使っていない。

$f=f_\alpha$ とすれば (2.1) と $g_\alpha=f_\alpha+h_\alpha$ から

$$\mathcal E_{g_\alpha}\ge L_{g_\alpha}+\mathcal E_{h_\alpha}
 \quad(\alpha>0).\tag{3.2}$$

## 4. コンパクト区間の費用だけを残す

Riesz の正混合表示を

$$r^{-s}=\int_0^\infty e^{-\alpha r^2}\,d\nu_s(\alpha),
\qquad d\nu_s(\alpha)=\frac{\alpha^{s/2-1}}{\Gamma(s/2)}\,d\alpha$$

と書く。全パラメータの slack を一個の関数にまとめる必要はない。

$$V_s(r)=\int_I h_\alpha(r)\,d\nu_s(\alpha)\ge0$$

だけを定義する。(3.2) を、$I$ の外では slack を残さず全 $\alpha>0$ にわたり積分する。非負関数への Tonelli により

$$\mathcal E_s(\mu)\ge L_s+\mathcal E_{V_s}(\mu).\tag{4.1}$$

ここで区間外の Gaussian の格子基準値を落としていないことが重要である。

(2.6) により $\kappa=c_0\nu_s(I)>0$ と置けば

$$V_s(r)\ge\kappa(r_0-r)^2\quad(0\le r\le r_0).\tag{4.2}$$

添付資料の二領域証明書には

$$a=\kappa r_0^2/4,\qquad b=\kappa$$

を渡せる。$\mathcal E_s\le L_s+\delta$ なら (4.1) は $\mathcal E_{V_s}\le\delta$ を与える。

## 5. LocalCrystal は Borel：証人を有限候補にする

固定した $R,e>0$ を考える。格子の基本平行体の閉包を $P$ とし、$M=\max_{p\in P}|p|$ とする。

非空な有限 $X\subset\overline B_R$ が、ある $\Phi(z)=Uz+b$ と有限 $Z\subset\Lambda$ に対して $d_H(X,\Phi Z)\le e$ を満たすとする。

$U^{-1}b=p+\lambda$、$p\in P$、$\lambda\in\Lambda$ と書き、$Z$ を $Z+\lambda$ で置き換えると、証人を

$$U(Z+p),\qquad U\in O(d),\quad p\in P$$

に正規化できる。さらに各 $z\in Z$ は $|z|\le R+e+M$ を満たすので

$$Z\subset S_{R,e}:=\Lambda\cap\overline B_{R+e+M}.$$

$S_{R,e}$ は有限。従って求める存在条件は

$$D_{R,e}(X):=
\min_{\varnothing\ne Z\subset S_{R,e}}
\min_{U\in O(d),\ p\in P}d_H(X,U(Z+p))\le e.\tag{5.1}$$

内側の証人空間はコンパクト、外側の候補は有限。各 Hausdorff 距離は $X$ に関して 1-Lipschitz なので、最小値 $D_{R,e}$ も 1-Lipschitz である。

配置から有限窓 $\Xi\cap\overline B_R$ への写像は Borel である。実際、窓が開集合 $O$ に当たる条件は $N_\Xi(\overline B_R\cap O)>0$、窓が $O$ に含まれる条件は $N_\Xi(\overline B_R\setminus O)=0$ という可測な計数条件になる。窓点数も Borel。

従って正の点数下界と (5.1) の共通事象は Borel である。空集合は点数下界によって除かれる。平行移動作用を合成すれば配置と中心の積空間でも Borel である。

この証明は閉球の境界での連続性も、$\Phi$ の可測選択も、解析集合の普遍可測性も使わない。

## 6. BRR の定常充填版

[B, Theorems 1.5, 1.6] を次の形で使用する。$\eta$ が十分小さいとき、中心密度 $\ge1-\eta$ の周期充填に対して、

$$R_\eta=\frac{\log(1/\eta)}{\log\log(1/\eta)},\qquad
R_\eta\le S,\qquad 2S\le M_dR_\eta$$

なら、中心確率 $\ge1-B_dR_\eta^{-1/2}$ で窓 $\overline B_S$ が

$$d_H\le e_\eta:=A_d\exp(c_dR_\eta)\eta^{1/4},
\qquad N\ge(1-B_dR_\eta^{-1/2})\operatorname{vol}(B_S)\tag{6.1}$$

を満たす。$M_8=2^{20}$、$M_{24}=2^{140}$ としてよい。記号 $A_d,B_d,c_d$ は BRR の定数を本ノート用に改名したもの。

**接続補題。** 最小距離 $r_0$、強度 $\rho$ の定常点過程 $Y$ に対して、同じ窓条件のもとで (6.1) が成り立つ確率は

$$\mathbb P(\text{(6.1)})\ge
1-B_dR_\eta^{-1/2}-\frac{1-\rho}{\eta}.\tag{6.2}$$

また $\rho\le1$。エルゴード性は不要である。

**証明。** 一辺 $L$ の周期箱 $Q_L$ の各面から $r_0/2$ の緩衝帯を除いた半開箱を $W_L$ とし、

$$P_L(Y)=(Y\cap W_L)+L\mathbb Z^d$$

と置く。異なる周期コピーの点も少なくとも一座標方向で $r_0$ 離れるので、これは最小距離 $r_0$ の周期充填である。

[B, Theorems 1.1, 1.2] の最適密度上界から、各標本で

$$D_L:=\frac{\#(Y\cap W_L)}{L^d}\le1.$$

定常性により

$$\mathbb E D_L=\rho\left(1-\frac{r_0}{L}\right)^d.$$

$L\to\infty$ とすれば $\rho\le1$。また Markov により

$$\mathbb P(D_L<1-\eta)
\le\frac{1-\rho(1-r_0/L)^d}{\eta}.\tag{6.3}$$

$U_L$ を周期箱に一様な独立の中心とする。密度が良い標本では BRR を適用し、密度が悪い標本では失敗確率を 1 で抑える。第5節の Borel 性により積空間上で積分できる。

$U_L+\overline B_S\subset W_L$ なら周期化配置と元配置は窓内で一致する。この条件を満たさない中心の割合は $O_d((S+r_0)/L)$ 以下。

元配置 $Y$ の定常性により、中心を一様化した窓の成功確率は原点窓の成功確率と等しい。従って原点窓の失敗確率は

$$B_dR_\eta^{-1/2}
+\frac{1-\rho(1-r_0/L)^d}{\eta}
+O_d\left(\frac{S+r_0}{L}\right).$$

$L\to\infty$ として (6.2) を得る。これは固定した同じ Borel 事象の確率下界で極限を取っているのであり、配置・事象・等長写像の極限を取っているのではない。□

## 7. 削除、拡大、全点復元と指数

### 7.1 削除強度

$0<t\le1/2$ とする。全空間で距離 $r_0(1-t)$ 未満の相手を持つ点をすべて削除し、削除過程を $D$、残存過程を $T=\Xi\setminus D$ とする。窓外の相手もこの判定に含める。

(4.2) と (4.1) により、距離 $r_0(1-t)$ 未満の順序付き点対の単位体積あたり期待数は

$$\le\frac{\delta}{\kappa r_0^2t^2}.$$

各削除点は少なくとも一本のこのような順序付き点対の始点であるから、削除強度 $q$ は

$$q\le A\delta/t^2,\qquad A=(\kappa r_0^2)^{-1}.\tag{7.1}$$

点対が順序付きなので、ここで余分な係数 $1/2$ は入れない。削除は平行移動同変な Borel 操作である。

### 7.2 拡大後の強度

$$t=\delta^{1/3},\quad a=(1-t)^{-1},\quad Y=aT.$$

$Y$ は定常で最小距離 $r_0$ を持ち、その強度は

$$\rho=a^{-d}(1-q)\ge1-(A+d)t.\tag{7.2}$$

標本ごとの密度については何も仮定していない。

### 7.3 周期安定性の誤差

$$b=\frac{25}{78},\qquad \eta=\delta^b,\qquad
R=R(\delta),\qquad S=aR$$

と置く。十分小さい $\delta$ では

$$bR\le R_\eta\le R,\qquad a\le2,$$

よって

$$R_\eta\le S,\qquad 2S\le\frac4b R_\eta<M_dR_\eta.$$

第6節が適用でき、密度の Markov 損失は

$$\frac{1-\rho}{\eta}\le(A+d)\delta^{1/78}.\tag{7.3}$$

BRR の位置誤差については

$$e_\eta\le A_d\exp(c_dR_\eta)\delta^{25/312}.$$

$$\frac{25}{312}-\frac1{13}=\frac1{312}>0$$

なので、十分小さい $\delta$ で $\exp(c_dR_\eta)\le\delta^{-1/312}$ とでき、

$$e_\eta\le A_d\delta^{1/13}.\tag{7.4}$$

### 7.4 削除点が観測窓に存在しない確率

(7.1) と定常性により

$$\mathbb P(D\cap\overline B_R\ne\varnothing)
\le\mathbb E N_D(\overline B_R)
=q\operatorname{vol}(B_R)
\le A\operatorname{vol}(B_1)R^d\delta^{1/3}.\tag{7.5}$$

この事象の補集合では、元配置の全点と残存配置の点が観測球内で完全に一致する。

### 7.5 逆拡大は等長写像ではないので補正する

$W=Y\cap\overline B_S$ が $UZ+v$ に Hausdorff 距離 $e_\eta$ 以内であるとする。$z_0\in Z$ を選び、$Z'=Z-z_0$、$v'=Uz_0+v$ と正規化すると

$$|z|\le2(S+e_\eta)\quad(z\in Z').$$

元の尺度では $a^{-1}W$ と $a^{-1}(UZ'+v')$ は距離 $e_\eta/a$ 以内。ただし後者は縮小格子なので、そのまま目標の等長像ではない。

等長写像を

$$\Psi(z)=Uz+v'/a$$

と取り直せば

$$d_H(a^{-1}W,\Psi Z')
\le e_\eta/a+2(1-a^{-1})(S+e_\eta)
\le e_\eta+2t(S+e_\eta).\tag{7.6}$$

$tR=\delta^{1/3}R=o(\delta^{1/13})$ なので、これは $C\delta^{1/13}$ 以下となる。

点数については、削除点のない事象上で

$$\#(\Xi\cap\overline B_R)=\#W
\ge(1-B_dR_\eta^{-1/2})\operatorname{vol}(B_{aR})
\ge(1-C R^{-1/2})\operatorname{vol}(B_R).$$

最後の不等式のため、閾値を小さくして係数を正にしておく。

総失敗確率は

$$B_dR_\eta^{-1/2}+(A+d)\delta^{1/78}
+A\operatorname{vol}(B_1)R^d\delta^{1/3}
\le C R^{-1/2}.\tag{7.7}$$

第5節、削除・拡大の Borel 性により、これらを満たす共通事象は Borel である。必要な有限個の閾値条件をまとめて $\delta_0(d,s)$ を選ぶ。定数と閾値はすべて法則より先に選べる。

これで第1節の正確な定理が従う。□

## 8. 任意の $0<\gamma<1/12$

第7節で

$$b=\frac{1+12\gamma}{6},\qquad \eta=\delta^b$$

とすればよい。$1/6<b<1/3$ であり、

$$\frac b4-\gamma=\frac{1-12\gamma}{24}>0,
\qquad \frac13-b=\frac{1-12\gamma}{6}>0.$$

前者が指数損失 $\exp(cR_\eta)$ を吸収し、後者が Markov 損失を消す。$R_\eta$ と $R(\delta)$ は定数倍で比較でき、BRR の窓条件も満たす。削除復元と逆拡大も同じ議論でよい。

従って位置誤差 $C_{d,s,\gamma}\delta^\gamma$ の版が成立する。$1/12$ 自体や、この指数が最適であることは主張しない。

## 9. 非零 Gaussian 正混合

$(0,\infty)$ 上の非零正 Borel 測度 $\nu$ に対して

$$p(r)=\int_0^\infty e^{-\alpha r^2}\,d\nu(\alpha),\qquad L_p<\infty$$

とする。$L_{g_\alpha}$ は正で、各コンパクトな $\alpha$ 区間上で正の下界を持つので、$L_p<\infty$ から $\nu$ はその区間で有限となる。従って正の質量を持つ有限コンパクト区間 $I=[a,b]\subset(0,\infty)$ が存在する。

$\mathcal E_p<\infty$ なら、$0<r\le\sqrt d$ で $p(r)\ge p(\sqrt d)>0$ を使って第3節の局所二次モーメントを得る。$p(\sqrt d)<\infty$ は、$\sqrt d\ge r_0$ と $p(r_0)\le L_p<\infty$ から従う。以後の定常 LP は同じ。

第4節では $V(r)=\int_Ih_\alpha(r)\,d\nu(\alpha)$ を使用する。原点と内側の正値性は同じ。最短長近傍では双対高さのコンパクト区間 $J=[\pi/b,\pi/a]$ に対し、核の極を避けるコンパクトな $v$ 区間を選んで正積分を下から抑える。

例えば $J=[y_-,y_+]$ に対して $T>\max\{y_+,1/y_-,1\}$ を取り、$v\in[T,T+1]$ とすればよい。ここは modular な極を避ける。$\widehat K$ の正値性と連続性から正の最小値が得られ、半径 $r\le r_0$ では指数関数にも正の一様下界がある。

こうして同じ二次費用を得るため、主定理、任意 $\gamma<1/12$、次節の零余剰分類が成立する。定数は $p,d,\gamma$ に依存してよい。

注意：$L_p<\infty$ だけでは $p(r)<\infty$ が全ての小さい $r>0$ で成り立つとは限らない。例えば $0<c<r_0^2$ とし $d\nu(\alpha)=1_{[1,\infty)}(\alpha)e^{c\alpha}d\alpha$ とすると、小半径では $p=\infty$、格子和は有限となる。本証明は非負拡張値を許し $\mathcal E_p<\infty$ を仮定する形でも有効である。通常の実数値ポテンシャルとして定理を書くなら、$p(r)<\infty$ for all $r>0$ を定義に加える。

## 10. 零余剰分類：定量定理の極限を使わない別経路

この節は任意の上の正混合に適用できる。$\mathcal E_p=L_p$ とする。

### 10.1 全ての距離が偶整数平方になる

第4節の gap より $\mathcal E_V=0$。$V$ の零点は CKMRV の等号半径だけなので、単位箱を整数平行移動して可算個の零確率例外を除けば、ほとんど確実に全ての異なる $x,y\in\Xi$ について

$$|x-y|^2\in2\mathbb Z,\qquad |x-y|\ge r_0.\tag{10.1}$$

### 10.2 標本を含むアフィン整数包

非空な標本で $x_0\in\Xi$ を選び

$$M=\operatorname{span}_{\mathbb Z}(\Xi-x_0)$$

と置く。生成元 $u,v$ の内積は

$$\langle u,v\rangle=(|u|^2+|v|^2-|u-v|^2)/2\in\mathbb Z.$$

任意の $m\in M$ について $|m|^2\in2\mathbb Z$。従って $M$ の非零ベクトルは長さ $\ge\sqrt2$ であり、$M$ は階数 $\le d$ の離散格子となる。

階数 $d$ なら Gram 行列の行列式は正整数なので

$$\operatorname{covol}(M)\ge1.$$

階数が低ければ標本の体積密度は 0、階数 $d$ なら $\Xi\subset x_0+M$ より上密度は $1/\operatorname{covol}(M)\le1$。空配置も上密度 0 とする。

### 10.3 期待強度だけで余体積 1 を強制

$$Z_R=\frac{\#(\Xi\cap B_R)}{\operatorname{vol}(B_R)}.$$

ここで $R$ は正整数に沿って増大させればよい。最小距離により $R\ge1$ で $Z_R\le C_d$ が標本一様に成り立つ。定常性と強度 1 は $\mathbb E Z_R=1$ を与える。

逆 Fatou の不等式と前段の上密度評価から

$$1=\limsup_{R\to\infty}\mathbb E Z_R
\le\mathbb E\limsup_{R\to\infty} Z_R\le1.$$

したがって上密度はほとんど確実に 1。特に標本は非空、$M$ は階数 $d$、余体積 1 である。

### 10.4 密度ゼロの穴を定常性で除く

アフィン整数包

$$\mathcal L(\Xi)=x_0+\operatorname{span}_{\mathbb Z}(\Xi-x_0)$$

は $x_0$ の選択に依存せず、平行移動同変である。これをランダムな点集合として Borel に扱える。具体的には、有界環状領域ごとの有限点の Borel 列挙をつなげ、最初の点を基点にして、有限整数結合を可算列挙し、重複を最初の出現により除けばよい。最小距離 $\sqrt2$ によりこの列挙が定める点集合は局所有限である。

従って $\mathcal L(\Xi)$ は定常な格子過程である。各標本は余体積 1 であり、最小距離は少なくとも $\sqrt2$。格子の点数漸近と最小距離による一様上界を使った優収束から、その期待強度も 1 となる。

$\Xi\subset\mathcal L(\Xi)$ なので、差集合は定常で強度 $1-1=0$。各有界箱の期待点数が 0 であることと可算被覆から

$$\Xi=\mathcal L(\Xi)\quad\text{ほとんど確実}.$$

この順番が重要である。Leech の場合、整数包を作った時点では、その最短長が 2 以上とはまだ言えない。しかし穴を除いた後では元標本と一致するため、最短長が 2 以上と分かる。

### 10.5 格子と法則の分類

いま標本は最小距離 $r_0$、余体積 1 の格子である。[B, Theorems 1.1, 1.2] の周期等号分類により、標本は対応する E₈ または Leech の等長像に限られる。

$\operatorname{Aut}(\Lambda)=\{U\in O(d):U\Lambda=\Lambda\}$ とする。向き $[U]\in O(d)/\operatorname{Aut}(\Lambda)$ を条件付けると、平行移動定常性により格子位相の条件付き分布はトーラス $\mathbb R^d/U\Lambda$ 上の Haar 分布である。厳密には、可算稠密な平行移動群について同時に条件付き不変性を取り、連続作用により全平行移動へ延ばして Haar 一意性を使う。

従って零余剰法則はちょうど

$$\mu=\int_{O(d)/\operatorname{Aut}(\Lambda)}
\left(\int_{\mathbb R^d/\Lambda}\delta_{U(\Lambda+u)}\,dm_\Lambda(u)\right)d\sigma([U])$$

という形である。$\sigma$ は任意の確率測度。内側の法則は代表元 $U$ に依存しない。逆に全てのこのような法則は強度 1、定常、エネルギー $L_p$ を満たす。

この証明には BRR の定量安定性、Borel–Cantelli、窓ごとの等長写像のコンパクト極限を必要としない。

## 11. Lean への依存整理と判定

数学的判定：固定 $1/13$、任意 $0<\gamma<1/12$、適切に定式化した非零 Gaussian 正混合、零余剰法則分類はいずれも、上の既刊入力と本ノートの接続補題で閉じる。

推奨する接続の分割：

1. `origin_slack_pos_of_duality_calibration`：Fourier 反転・非負性・校正・双対性から原点の正値性。
2. `compact_slack_quadratic`：原点込みのコンパクト正値性と、最短長近傍の正積分から二次下界。
3. `stationary_compact_slack_gap`：定常 LP と全 Gaussian の格子基準値を保った正混合。
4. `localCrystal_borel_finite_witnesses`：基本平行体による正規化、有限格子候補、コンパクト最小値。
5. `stationary_packing_stability_of_periodic`：緩衝周期化、$D_L\le1$、期待欠損、中心平均、同じ事象の確率下界で $L\to\infty$。
6. 既存の削除・拡大・復元・指数計算へ接続。
7. 零余剰分類は別枝にし、偶整数距離・アフィン整数包・強度ゼロの穴・位相 Haar へ進む。

ただし CKMRV の実補助関数の全域符号と BRR の定量定理が Lean に未形式化なら、上の分割だけでそれらの深い入力の実装が済むわけではない。原点の特殊値計算、全 slack のパラメータ積分、任意射影の可測性、エルゴード分解、独立大箱、零余剰での大域コンパクト極限は省けるが、既刊入力そのものの形式化は別の作業である。

独立レビューでは特に、(2.2) の規格化、(2.5) の収束半径、(3.1) の対角項、(5.1) の有限候補化、(6.2) の定常移送、(7.6) の逆拡大補正、10.4 の整数包と穴除去の順序を確認するのがよい。
