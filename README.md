# cut-and-project

## Conjectures on the Period Lengths of One-Dimensional Cut-and-Project Sequences

With $\alpha, \beta \in ℕ$, $\alpha \perp \beta$, $x, y \in ℝ$, $\omega \in \mathbb{R}_{\ge 0}$ and $i \in ℤ$, we consider the points

$$
\mathbf{P} =
\biggl(
\begin{pmatrix} x \\ y \end{pmatrix}
\Bigm|
x \in \mathbb{Z},
y \in
\bigl[\tfrac{\alpha}{\beta}(x-\omega), \tfrac{\alpha}{\beta}x+\omega\bigr]
\cap \mathbb{Z}
\biggr)
$$

projected vertically onto

$$
f(x) = \frac{\alpha}{\beta}x
$$

and measure their Euclidean distances $(d^{(i)})$.

With

$$
\Lambda_{\alpha,\beta} := \alpha + \beta + 1,
$$

we propose the following conjectures concerning the period length $\lambda$ of $(d^{(i)})$:

1. There is always a finite $\lambda$.
2. If $\omega \in (0,1)$, then $\lambda_{\alpha,\beta} < \Lambda_{\alpha,\beta}$.
3. If $\omega = 1$, then $\lambda_{\alpha,\beta} = \Lambda_{\alpha,\beta}$.
4. If $\omega \in (1,2)$, then $\lambda_{\alpha,\beta} \ge \Lambda_{\alpha,\beta}$.
5. If $\omega > 2$, then $\lambda_{\alpha,\beta} > \Lambda_{\alpha,\beta}$.
6. If $\omega \ne 1$, then $\displaystyle \lambda \approx \bigl\lfloor \omega \,\Lambda_{\alpha,\beta}\bigr\rfloor$.

We use numerical methods to support these conjectures.

> **Remark.** We will show that $\lambda_{\omega=0} = 1$.

> **Remark.** Conjecture 6 is the result of a conversation with [ChatGPT](https://chat.openai.com).
