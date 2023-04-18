---
marp: true
math: mathjax
---

# Исчисление построений

---

$∃α.\; α$

$∀α.\; α$

$∀\phi.\; \phi(0) → (∀n.\; \phi(n) → \phi(n+1)) → ∀n.\; \phi(n)$

---

$$\begin{aligned}
⊥ &:= ∀α.\; α \\
P ∧ Q &:= ∀α.\; (P → Q → α) → α \\
P ∨ Q &:= ∀α.\; (P → α) → (Q → α) → α \\
(∃x.\; ϕ) &:= ∀α.\; ∀x.\; (ϕ → α) → α
\end{aligned}$$

---

$x ∈ S$ to $S(x)$

$\{1, 2, 3\}$ to $λx.\; x = 1 ∧ x = 2 ∧ x = 3$

$\{n \in ℕ \mid 2 \leqslant n \leqslant 5\}$ to $λn.\; ℕ(n) ∧ 2 \leqslant n \leqslant 5$

$\{2\cdot n \mid n \in ℕ\}$ to $λk.\; ∃n.\; ℕ(n) ∧ k = 2\cdot n$

---

$$\begin{aligned}
&x ∈ A &\qquad & A(x)\\
&A ⊆ B  &  &∀x.\; A(x) → B(x)\\
&∅  &  &λx.\; \bot \\
&\{a\}  &  &λx.\; x = a  \\
&A ∪ B  &  &λx.\; A(x) ∨ B(x) \\
&A ∩ B  &  &λx.\; A(x) ∧ B(x) \\
&A \setminus B  &  &λx.\; A(x) ∧ ¬B(x)  \\
&A^\complement  &  &λx.\; ¬A(x)
\end{aligned}$$

---

Но уже можно догадаться, куда это ведёт...

---

# Парадоксы

---

$$X := X → Q$$

1. Пусть $X$
   1. Тогда $X → Q$ (определение $X$)
   2. И потому $Q$
2. Следовательно, $X → Q$
3. Что означает $X$ (определение!)
4. Отсюда $Q$

(парадокс Карри)

---

![bg fit](../build/cp-proof.svg)

---

![bg fit](../build/cp-red.svg)

---

$X(α) := α(α) → Q$

$X(X)$

$X(X) := X(X) → Q$
