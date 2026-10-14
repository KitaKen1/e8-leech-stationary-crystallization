# Quantitative Stationary Crystallization for the E₈ and Leech Lattices

Let $`d\in\{8,24\}`$, and let $`\Lambda\subset\mathbb R^d`$ be the covolume-one E₈ or Leech lattice. For $`s>d`$, consider the ordered Riesz energy of a stationary simple locally finite point process $`\Xi`$ of intensity one:

```math
\mathcal E_s(\mu)
=\mathbb E_\mu\sum_{x\in\Xi\cap[0,1)^d}
  \sum_{y\in\Xi\setminus\{x\}}|x-y|^{-s},
\qquad
L_s=\sum_{z\in\Lambda\setminus\{0\}}|z|^{-s}.
```

The second sum includes points outside the unit cube. There is no factor of $`1/2`$. Intensity one is an expectation condition; ergodicity and samplewise density limits are not assumed.

> [!NOTE]
> **Theorem (Quantitative stationary crystallization).**
>
> For every $`s>d`$, there exist $`C>0`$ and $`0<\delta_0<e^{-e}`$, depending only on $`d,s`$, such that the following holds. If $`\mu`$ is as above, $`0<\delta<\delta_0`$, and
>
> ```math
> \mathcal E_s(\mu)\le L_s+\delta,
> ```
>
> then, with
>
> ```math
> R=\frac{\log(1/\delta)}{\log\log(1/\delta)},
> ```
>
> there is a measurable event of probability at least $`1-CR^{-1/2}`$ on which $`X=\Xi\cap\overline B_R`$ satisfies
>
> ```math
> \exists\Phi\text{ a Euclidean isometry},\quad
> \exists Z\subset\Lambda\text{ finite}:
> \quad d_H(X,\Phi Z)\le C\delta^{1/13},
> ```
>
> ```math
> |X|\ge(1-CR^{-1/2})\mathrm{vol}(\overline B_R).
> ```

Here $`|X|`$ denotes the number of points in $`X`$. The conclusion concerns **all original points** in the closed observation ball. The lattice witness is a finite subset, and its image may extend slightly outside the ball. The constants are chosen before the process law and the positive upper bound $`\delta`$ on the energy excess.

This repository presents a proposed paper proof. A proof sketch follows; the [PDF manuscript](PDF/e8-leech-stationary-crystallization.pdf) gives the detailed connection from the Gaussian auxiliary functions of Cohn–Kumar–Miller–Radchenko–Viazovska (CKMRV) to the periodic stability theorem of Böröczky–Radchenko–Ramos (BRR). The stationary transfer and restoration of the original points are proved in the manuscript.

## Proof sketch

### 1. Obtain linear programming for the stationary law

Finite Riesz energy controls the local second moment:

```math
\mathbb E_\mu N_Q^2\le1+d^{s/2}\mathcal E_s(\mu),
\qquad N_Q=|\Xi\cap Q|,\quad Q=[0,1)^d.
```

For a real even Schwartz function $`f`$ with $`\widehat f\ge0`$, apply Fourier positivity to the point measure in a large box minus Lebesgue measure on that box. Stationarity and dominated convergence then give

```math
f(0)+\mathcal P_\mu(f)\ge\widehat f(0),
\qquad
\mathcal P_\mu(f)=\mathbb E_\mu\sum_{x\in\Xi\cap Q}\sum_{y\ne x}f(y-x).
```

This works directly with the original law, including nonergodic laws (Section 2).

### 2. Turn the energy excess into a cost for close pairs

For $`g_\alpha(r)=e^{-\alpha r^2}`$, use the CKMRV auxiliary function $`f_\alpha`$ and its nonnegative slack $`h_\alpha=g_\alpha-f_\alpha`$. Poisson summation calibrates the lattice value, so

```math
\mathcal P_\mu(g_\alpha)-L_\alpha
\ge\mathcal P_\mu(h_\alpha)\ge0.
```

Integrate the slack only over $`I=[\pi/4,\pi/3]`$ with the Riesz weight:

```math
V_s(r)=\int_I\frac{\alpha^{s/2-1}}{\Gamma(s/2)}h_\alpha(r)\,d\alpha.
```

The Gaussian inequality holds for every positive parameter, so Tonelli gives $`\mathcal P_\mu(V_s)\le\delta`$. Strict positivity at and near the origin, together with the positive kernel representation near the minimum lattice distance $`r_0`$, yields

```math
0<t\le\tfrac12,\quad 0<r<r_0(1-t)
\quad\Longrightarrow\quad V_s(r)\ge\kappa t^2
```

for some $`\kappa>0`$. Here $`r_0=\sqrt2`$ in dimension eight and $`r_0=2`$ in dimension twenty-four. The small-radius argument uses the regularized auxiliary function, including its origin value (Section 3).

### 3. Transfer periodic stability using expected density

The finite-window matching event is Borel: minimizing the maximum distance to an isometric copy of the full lattice over compact rotation and phase parameters is equivalent to the finite-subset Hausdorff condition (Section 4).

For a stationary packing of minimum distance $`r_0`$ and intensity $`\rho`$, periodize a large buffered box. Each periodization has center density at most one, and its expected density tends to $`\rho`$. Markov's inequality and BRR then give

```math
\mathbb P(\mathrm{failure})
\le B_dR(\eta)^{-1/2}+\frac{1-\rho}{\eta},
\qquad
R(\eta)=\frac{\log(1/\eta)}{\log\log(1/\eta)}.
```

The local position error is at most $`E_d e^{c_dR(\eta)}\eta^{1/4}`$. The transfer uses a uniform random observation center and vanishing boundary error; it requires no almost-sure density limit (Section 5).

### 4. Delete close pairs, dilate, and recover every original point

Delete every point with a neighbor at distance less than $`r_0(1-t)`$, using the entire configuration. The deleted intensity satisfies

```math
q_t\le\frac{\delta}{\kappa t^2}.
```

Dilate the remaining process by $`\lambda=(1-t)^{-1}`$. It is a packing of minimum distance $`r_0`$, with intensity deficit at most $`q_t+dt`$. Apply stationary stability on the ball of radius $`\lambda R`$.

The same Euclidean isometry remains a witness after comparing each original position $`x`$ with $`\lambda x`$; this adds at most $`2tR`$ to the position error. The probability of any deleted point in the original observation ball is at most $`q_t\mathrm{vol}(\overline B_R)`$. Hence the total failure probability is bounded by

```math
B_dR(\eta)^{-1/2}
+\frac{dt+\delta/(\kappa t^2)}{\eta}
+\frac{\delta}{\kappa t^2}\mathrm{vol}(\overline B_R).
```

On the complementary event, the local conclusion holds for all original points (Section 6).

### 5. Choose the parameters and close the estimates

Take

```math
t=\delta^{1/3},\qquad \eta=\delta^{25/78}.
```

The position error is at most $`C\delta^{1/13}`$, while the probability and point-count losses are at most $`CR^{-1/2}`$. The two positive exponent margins are

```math
\frac{25}{312}-\frac1{13}=\frac1{312},
\qquad
\frac13-\frac{25}{78}=\frac1{78}.
```

They absorb the exponential-in-$`R(\eta)`$ factor and all powers of $`R`$ as $`\delta\to0`$ (Section 7).

## Detailed manuscript

- [PDF manuscript](PDF/e8-leech-stationary-crystallization.pdf)
- [Timestamp proof](PDF/e8-leech-stationary-crystallization.pdf.ots)

## Conclusion

The proposed proof gives quantitative local crystallization for stationary intensity-one point processes in dimensions eight and twenty-four. An ordered Riesz-energy excess of at most $`\delta`$ yields position error $`C\delta^{1/13}`$ on a ball of radius $`R=\log(1/\delta)/\log\log(1/\delta)`$, with probability and point-count losses at most $`CR^{-1/2}`$. The conclusion includes all original points in the closed observation ball and uses a Euclidean isometry of the covolume-one E₈ or Leech lattice.

The manuscript also gives every fixed position exponent below $`1/12`$, extends the argument to nonzero positive Gaussian mixtures with finite lattice energy, and identifies the zero-excess laws as orientation mixtures of lattices with Haar-uniform translation phase.
