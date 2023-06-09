This code was written as part of the 2023 MSRI "Formalization of Mathematics" workshop hosted in Berkeley California

## Formal_Lipschitz
Implementation of Theorem 2.2 of "Metric Embeddings and Lipschitz Extentensions by Assaf Naor" page 5

Link: https://web.math.princeton.edu/~naor/homepage%20files/embeddings_extensions.pdf

Code now integrated in Mathlib4 under :
### Mathlib.Topology.MetricSpace.Kuratowski

### Mathlib.Analysis.lpSpace 

### Mathlib.Topology.MetricSpace.Lipschitz
 
## Theorem 2.2. 

Suppose $\left(X, d_X\right)$ is a metric space, $A \subseteq X$ and let $f: A \rightarrow \ell_{\infty}(\Gamma)$ a Lipschitz function. Then, there is an

extension $\tilde{f}: X \rightarrow \ell_{\infty}(\Gamma)$ of $f$, i.e. with $\tilde{f}|\_A=f$, such that $\|\tilde{f}\|\_{\text {Lip }}=\|f\|\_{\text {Lip }}$.

## Proof. 

Let $\|f\|\_{\text {Lip }}=L$ and write

$$
f(x)=\left(f\_\gamma(x)\right)\_{\gamma \in \Gamma}, \text { for } x \in X \text { and } f\_\gamma(x) \in \mathbb{R}
$$

Then, we see that

$$
\|f\|\_{\text {Lip }}=\sup \_{d_X(x, y) \leqslant 1} \sup \_{\gamma \in \Gamma}\left|f\_\gamma(x)-f\_\gamma(y)\right|=\sup \_{\gamma \in \Gamma}\left\|f\_\gamma\right\|\_{\text {Lip }},
$$

thus each $f\_\gamma$ is also $L$-Lipschitz. Thus, it is enough to extend all the $f\_\gamma$ isometrically, that is prove our theorem with $\mathbb{R}$ replacing $\ell\_{\infty}(\Gamma)$. This will be done in the next important lemma.

## Lemma 2.3 
(Nonlinear Hahn-Banach theorem). Suppose $\left(X, d_X\right)$ is a metric space, $A \subseteq X$ and let $f: A \rightarrow \mathbb{R}$ a Lipschitz function. 

Then, there is an extension $\tilde{f}: X \rightarrow \mathbb{R}$ of $f$, i.e. with $\left.\tilde{f}\right|\_A=f$, such that $\|\tilde{f}\|\_{\text {Lip }}=\|f\|\_{\text {Lip }}$

First-direct proof. Call again $L=\|f\|\_{\text {Lip }}$ and define the function $\tilde{f}: X \rightarrow \mathbb{R}$ by the formula

$$
\tilde{f}(x)=\inf \_{a \in A}\left\\{f(a)+L d\_X(x, a)\right\\}, \quad x \in X
$$

To see that this function satisfies the results, fix an arbitrary $a\_0 \in A$. Then, for any $a \in A$ :

$$
f(a)+L d_X(x, a) \geqslant f\left(a\_0\right)-L d\left(a, a\_0\right)+L d(x, a) \geqslant f\left(a\_0\right)-L d\left(x, a\_0\right)>-\infty,
$$

so $\tilde{f}(x)$ is well-defined. Also, if $x \in A$, the above shows that $\tilde{f}(x)=f(x)$. Finally, for $x, y \in X$ and $\varepsilon>0$, choose $a\_x \in A$ such that

$$
\tilde{f}(x) \geqslant f\left(a\_x\right)+L d\left(x, a\_x\right)-\varepsilon
$$

Then,

$$
\tilde{f}(y)-\tilde{f}(x) \leqslant f\left(a\_x\right)+L d\left(y, a\_x\right)-f\left(a\_x\right)-L d\left(x, a\_x\right)+\varepsilon \leqslant L d(x, y)+\varepsilon .
$$

Thus, we see that $\tilde{f}$ is indeed $L$-Lipschitz.
