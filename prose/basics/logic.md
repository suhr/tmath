# Высказывания и доказательства

Пусть на натуральных числах определено отношение $⩽$, про которое мы знаем следующее:

- Для любого натурального числа $n$, $n \leqslant n$
- Для любых натуральных чисел $n$ и $k$, если $n ⩽ k$, то $n ⩽ k + 1$

Что можно вывести, зная лишь эти два факта? Ну, например, можно доказать, что $3 ⩽ 5$:

1. $3 ⩽ 3$
2. Следовательно $3 ⩽ 4$
3. Отсюда $3 ⩽ 5$

Или можно доказать, что если $n$ натуральное число, то $n ⩽ n + 3$:

1. Пусть $n$ — натуральное число
2. Тогда $n ⩽ n$
3. Следовательно, $n ⩽ n + 1$
3. Следовательно, $n ⩽ n + 2$
4. Отсюда $n ⩽ n + 3$

Это примеры математических рассуждений. Но как именно мы рассуждаем?

Для начала, введём обозначения. Мы будем писать «если $P$, то $Q$» как $P → Q$, а «для любого $x:τ$, $P$» как $∀x.\; P$. Символ $∀$ называется квантором всеобщности.

Тогда изначальные предпосылки можно записать так:

- $refl : ∀n:ℕ.\; n ⩽ n$
- $step : ∀\{n:ℕ\}\{k:ℕ\}.\; n ⩽ k → n ⩽ k + 1$

Рассуждение это последовательность утверждений, где каждое утверждение следует из предыдущих согласно какому-то логическому правилу. Выделим правила вывода, использованные в доказательствах выше.

Первое правило это удаление квантора всеобщности:

1. $∀n:ℕ.\; n ⩽ n$
2. $3:ℕ$
3. Следовательно, $3 ⩽ 3$

Если $P$ истино для всех $x:τ$, то оно должно быть истино и для некоторого конкретного значения $v:τ$. Символьно, это правило можно записать как

$$\frac{∀{\color{red}x}:{\color{red}τ}.\; {\color{red}P} \qquad {\color{red}v}:{\color{red}τ} }{{\color{red}P}[{\color{red}x} := {\color{red}v}]}$$

Другое правило вывода — modus pones:

1. $3 ⩽ 3$
2. $(3 ⩽ 3) → (3 ⩽ 4)$
3. Следовательно, $3 ⩽ 4$

Если из $P$ следует $Q$, и $P$ истино, то тогда $Q$. Символьно:

$$\frac{{\color{red}P} → {\color{red}Q}\qquad {\color{red}P}}{{\color{red}Q}}$$

Наконец, правило, которое было использовано во втором рассуждении это введение квантора всеобщности:

- Пусть $n:ℕ$
    - …
    - $n ⩽ n + 3$
- Следовательно, $∀n.\; n ⩽ n + 3$

Здесь мы вводим переменную $n:ℕ$, и затем доказываем $n ⩽ n + 3$ вне зависимости от какого-либо конкретного значения $n$. Из чего делаем вывод, что $n ⩽ n + 3$ верно для любого $n: ℕ$.

Вспомним правило типизации для применения функций:

$$\frac
{ Γ ⊢ {\color{red}f}:(∀{\color{red}x}:{\color{red}α}.\;{\color{red}β})\qquad
  Γ⊢ {\color{red}v}:{\color{red}α}                                           }
{Γ ⊢ ({\color{red} f\ v}): {\color{red}β}[{\color{red}x} := {\color{red}v}]}$$

Оно обобщает первые два правила рассуждения. Причём контекст типизации можно рассматривать как набор предпосылок.

Правило для лямбда-функций же обобщает третье правило:

$$\frac
{ Γ,({\color{red}x}:{\color{red}α}) ⊢ {\color{red}e}:{\color{red}β} \qquad
  Γ ⊢ (∀{\color{red}x}:{\color{red}α}.\;{\color{red}β}):\mathcal U\ i      }
{Γ ⊢ (λ{\color{red}x}:{\color{red}α}.\;{\color{red}e}):
  (∀{\color{red}x}:{\color{red}α}.\;{\color{red}β})                        }$$

Предположив ${\color{red}x}:{\color{red}α}$ и доказав ${\color{red}β}$, мы доказываем $∀{\color{red}x}:{\color{red}α}.\;{\color{red}β}$.

**Парадигма:** высказывание это тип, его доказательство это значение данного типа.

В этой парадигме мы можем вывести доказательство $3 ⩽ 5$ как

1. $(refl\ 3) : 3 ⩽ 3$
2. $step\ (refl\ 3) : 3 ⩽ 4$
3. $step\ (step\ (refl\ 3)) : 3 ⩽ 5$

Доказательство $3 ⩽ 5$ это просто выражение $step\ (step\ (refl\ 3))$. Доказательство же $∀n.\; n ⩽ n + 3$ можно записать как

$$λn:ℕ.\; step\ \big(step\ (step\ (refl\ n))\big)$$

Хотя $∀$ и $→$ достаточно, чтобы рассуждать о чём угодно, удобно иметь и другие составные высказывания. Правила для них мы выразим как функции.

Высказывание $A ∧ B$ означает, что истино и $A$, и $B$. Оно вводится следующей функцией:

$$intro: A → B → A ∧ B$$

И разбирается на части следующими функциями:

$$\begin{aligned}
left &: A ∧ B → A \\
right &: A ∧ B → B
\end{aligned}$$

Пользуясь этими утверждениями, докажем следующее:

$$Z → (Z → A) → (Z → B) → A ∧ B$$

Сначала докажем по шагам:

1. Из $Z$ и $Z → A$ следует $A$
2. Из $Z$ и $Z → B$ следует $B$
3. Из $A$ и $B$ следует $A ∧ B$

Теперь докажем то же самое выражением:

$$λ(z: Z)(za: Z → A)(zb: Z → B).\; intro\ (za\ z)\ (zb\ z)$$

Высказывание $A ∨ B$ означает, что по крайней мере одно из высказываний $A$ и $B$ истино. Оно вводится функциями

$$inl: A → A ∨ B\\
inr: B → A ∨ B$$

И разбирается функцией

$$elim: A ∨ B → (A → Z) → (B → Z) →Z$$

Она соответствует разбору возможных вариантов:

1. Рассмотрим $P ∨ Q$
2. Пусть $P$
    1. ...
    2. $Z$
3. Пусть $Q$
    1. ...
    2. $Z$
4. Следовательно, $Z$

Высказывание $∃x:τ.\; P\ x$ означает, что существует такое $x:τ$, что $P\ x$ истино. Введение:

$$intro: (x:τ) → P\ x → (∃x:τ.\; P\ x)$$

Использование:

$$elim: (∃x:τ.\; P\ x) →(∀x:τ.\; P\ x → Z) → Z$$

Внимательный читатель заметит, что высказывания про $∧$ и $∨$ очень похожи на функции, определённые для `α × β` и `α ⊕ β`. И действительно, логические связки в Lean определены как индуктивные типы:

```lean
structure And (a b : Prop) : Prop where
  -- Имя конструктора
  intro ::
  -- Поля
  left : a
  right : b
```

```lean
inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
```

```lean
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p
```

Отношения тоже могут быть определены индуктивно. Отношение $(⩽)$, которое мы рассматривали, определено в Lean как индуктивное семейство типов:

```lean
inductive Nat.le (n: Nat): Nat → Prop
  | refl     : Nat.le n n
  | step {m} : Nat.le n m → Nat.le n (succ m)
```

Мы рассмотрели доказательства как некие рассуждения. Но их можно также рассматривать как заготовленный план для спора.

Представим оппонента, который разбирает высказывания следующим образом:

- Если мы утверждаем $P ∧ Q$, то он выбирает одно из высказываний и дальше разбирает это высказывание
- На $P ∨ Q$, он спрашивет — какое именно из высказываний истино? Получив ответ, он разбирает это высказывание
- В случае $P → Q$, скептик ищет доказательство $P$. Если находит, то разбирает $Q$
- Для $∀x:τ.\; φ\ x$ скептик выбирает значение $v: τ$ и, если оно существует, переходит к $φ\ v$
- И если мы утверждаем, что  $∃x:τ.\;φ\ x$, он спрашивает — какое именно $x$? Получив $v:τ$ в качестве ответа, он разбирает $φ\ v$
- Для остальных утверждений он просто требует их доказательство

Например, рассмотрим высказывание «для каждого натурального числа $n$ существует большее натуральное число $k$»:

$$∀n:ℕ.\; ∃k: ℕ.\; n < k$$

Для него возможен такой диалог:

- Скажем, для $n := 9000$ найдётся такое $k$, что $9000 < k$? Что это за $k$ такое?
- Например, $k := 9001$.
- Докажи, что $9000 < 9001$
- (доказываем, что $9000 < 9001$)

Если переставить $∀$ и $∃$ в предыдущем примере, то получим ложное высказывание «существует такое натуральное число $k$, что любое натуральное число $n$ меньше»:

$$∃k: ℕ.\; ∀n:ℕ.\; n < k$$

Диалог уже будет другой:

1. И что же это за число такое?
2. $100500$
3. И, стало быть, $100501 < 100500$?

И оппонент побеждает в споре, так как $100501 < 100500$ доказать мы не можем.

Доказательства как выражения являются одновременно и планом для диалога:

- Применение $pq: P → Q$ к $p:P$ вычисляет доказательство $Q$
- Применение $ap: ∀x:τ.\; P\ x$ к $v:τ$ вычисляет доказательство $P\ v$
- Из $pq : P ∧ Q$ можно извлечь как доказательство $P$, так и доказательство $Q$
- $pq: P ∨ Q$ можно сопоставить $inl\ p$ или $inr\ q$
- Из $ep: ∃x:τ.\;$ можно извлечь $v:τ$ вместе с доказательством $P\ v$

Нам осталось рассмотреть ещё одно высказывание: $¬P$ («не P»), которое истино когда $P$ ложно.

Для этого рассмотрим один из основных вариантов его использования:

1. $P ∨ Q$
2. $¬P$
3. Следовательно, $Q$

Доказательство обратного позволяет отсекать невозможные случаи.

Но так как из $P$ следует $P ∨ Q$ для любого высказывания $Q$, предыдущее рассуждение обобщается в

$$absurd: P → ¬P → Q$$

Из одновременной истинности $P$ и $¬P$ следует истинность любого утверждения. Другими словами, *из абсурда следует что угодно*.

У абсурда не может быть доказательств (иначе бы все утверждения были истинными, а любые рассуждения — бессмысленными). И в Lean абсурд это индуктивный тип без конструкторов:

```lean
inductive False : Prop
```

И $¬P$ выражается через абсурд: $¬P := P → False$.

## Упражнения

Математика не может быть освоена одним лишь пассивным созерцанием, и пришло время практики. Но Lean может помочь с написанием доказательства.

Например, пусть мы хотим доказать, что $P ∨ Q → ¬P → Q$. Мы пишем:

```lean
example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  _
```

Выражение `_` называется *дыркой*. Lean не может придумать доказательство на место дырки, но зато он показывает нам её тип, вместе с контекстом:

```
Expected type
PQ: Prop
pq: P ∨ Q
np: ¬P
⊢ Q
```

Напишем часть доказательства:

```lean
example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  pq.elim _ _
```

Lean показывает, что одна из дырок имеет тип `P → Q`, а другая — `Q → Q`.

Допишем ещё:

```lean
example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  pq.elim (λp => _) (λq => _)
```

Контексты у дырок становятся разными: в одном `p : P`, а в другом `q : Q`.

Наконец, запишем доказательство полностью:

```lean
example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  pq.elim (λp => (np p).elim) (λq => q)
```

Важно уметь сопоставить выражение с рассуждением по шагам. Выражение выше соответствует следующему рассуждению:

1. Рассмотрим $P ∨ Q$
2. Пусть $P$
    1. Но это невозможно, так как $¬P$
3. Пусть $Q$
    1. Тогда $Q$

Другой пример: докажем, что $P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)$:

```lean
example {P Q R: Prop}(pqr: P ∧ (Q ∨ R)): (P ∧ Q) ∨ (P ∧ R) :=
  let ⟨p,qr⟩ := pqr;  qr.elim (λq => Or.inl ⟨p,q⟩) (λr => Or.inr ⟨p,r⟩)
```

Выражение `let` позволяет не только вводить локальные определения, но и разбирать доказательства выражений вида $P ∧ Q$ на части.

Доказательству выше соответствует рассуждение

1. Из $P ∧ (Q ∨ R)$ следуют $P$ и $Q ∨ R$
2. Рассмотрим $Q ∨ R$
    1. Пусть $Q$. Тогда $P ∧ Q$ и, следовательно, $(P ∧ Q) ∨ (P ∧ R)$
    2. Пусть $R$. Тогда $P ∧ R$ и отсюда $(P ∧ Q) ∨ (P ∧ R)$

Третий пример:

```lean
example {P Q: Prop}(pq: P → Q)(nq: ¬Q): ¬P :=
  λp => nq (pq p : Q)
```

Соответствующее рассуждение:

1. Предположим, что $P$
    1. Так как $P → Q$, то $Q$
    2. Что абсурдно, так как $¬Q$
2. Следовательно, $¬P$

Перечислим ещё раз правила для $∧$, $∨$ и абсурда:

```
And.intro : ∀{a b: Prop}, a → b → a ∧ b
And.left  : ∀{a b: Prop}, a ∧ b → a
And.right : ∀{a b: Prop}, a ∧ b → b

Or.inl  : ∀{a b: Prop}, a → a ∨ b
Or.inr  : ∀{a b: Prop}, b → a ∨ b
Or.elim : ∀{a b c: Prop}, a ∨ b → (a → c) → (b → c) → c

False.elim : False → C
```

Теперь упражнения. Простые:

```lean
example {P Q: Prop}(pq: P ∧ Q): Q ∧ P := _
example {P Q R: Prop}(pQr: P ∧ (Q ∧ R)): (P ∧ Q) ∧ R := _
example {P Q: Prop}(p: P): Q → P := _
example {P Q R: Prop}(pqr: P → Q → R): P ∧ Q → R := _
example {P Q R: Prop}(pqr: P → Q → R)(pq: P → Q): P → R := _
example {P Q R: Prop}(pq: P → Q)(qr: Q → R): P → R := _
example {P Q: Prop}(npq: ¬(P ∨ Q)): ¬P ∧ ¬Q := _
example {P Q: Prop}(npQ: ¬P ∨ Q): P → Q := _
example {P Q R: Prop}(pQr: P → Q ∧ R): (P → Q) ∧ (P → R) := _
example {P Q R: Prop}(pqR: P ∨ Q → R): (P → R) ∧ (Q → R) := _
```

Сложнее:

```lean
example {P Q R: Prop}(pqR: (P ∨ Q) ∨ R): P ∨ (Q ∨ R) := _
example {P Q R: Prop}(pqPr : (P ∧ Q) ∨ (P ∧ R)): P ∧ (Q ∨ R) := _
example {P Q R: Prop}(pQr: P ∨ (Q ∧ R)): (P ∨ Q) ∧ (P ∨ R) := _
```

Не обязательно решать их все, но необходимо понимать, как каждое из них может быть решено. К каждому решению следует привести рассуждение.

Упражнения на $∀$ и $∃$ выделены в отдельный блок. Но сначала примеры.

Докажем, что $(∀x.\; P\ x ∧ Q\ x) → (∀x.\; P\ x) ∧ (∀x.\; Q\ x)$:

```lean
example {P Q: α → Prop}(apq: ∀x, P x ∧ Q x): (∀x, P x) ∧ (∀x, Q x) :=
  ⟨λx => (apq x).left,  λx => (apq x).right⟩
```

Рассуждение:

1. Докажем $∀x.\; P\ x$
    1. Пусть $x:τ$
    2. Тогда $P\ x ∧ Q\ x$
    3. Отсюда $P\ x$
2. Докажем $∀x.\; Q\ x$
    1. Пусть $x$ это значение типа $τ$
    2. Тогда $P\ x ∧ Q\ x$
    3. Отсюда $Q\ x$
3. Отсюда $(∀x.\; P\ x) ∧ (∀x.\; Q\ x)$

Другой пример:

```lean
example {P: α → β → Prop}(eap: ∃x, ∀y, P x y): ∀y, ∃x, P x y :=
  let ⟨x,ap⟩ := eap;  λy => ⟨x, (ap y : P x y)⟩
```

`let` позволяет разобрать и $∃x:τ.\; P\ x$ на $x:τ$ и $P\ x$.

Рассуждение:

1. Возьмём такое $x$, что $∀y.\; P\ x\ y$
2. Покажем, что $∀y, ∃x, P\ x\ y$
    1. Пусть дано некоторое значение $y$
    2. Тогда $P\ x\ y$
    3. Следовательно, $∃x.\; P\ x\ y$

Ещё раз, правила для $∃$:

```
Exists.intro : ∀{α: Sort u}{p: α → Prop},
  (w:α) → p w → Exists p
Exists.elim : ∀{α: Sort u}{p: α → Prop}{b : Prop},
  (∃x, p x) → (∀(a:α), p a → b) → b
```

И упражнения. Простые:

```lean
example {P: α → β → Prop}(ap: ∀x, ∀y, P x y): ∀y, ∀x, P x y := _
example {P: α → β → Prop}(ep: ∃x, ∃y, P x y): ∃y, ∃x, P x y := _
example {P: α → Prop}(ne: ¬∃x, P x): ∀x, ¬(P x) := _
example {P: α → Prop}{Q: Prop}(epQ: (∃x, P x) → Q): ∀x, P x → Q := _
example {P: α → Prop}{Q: Prop}(apq: ∀x, P x → Q): (∃x, P x) → Q := _
```

Сложнее:

```lean
example {P Q: α → Prop}(aa: (∀x, P x) ∨ (∀x, Q x)): ∀x, P x ∨ Q x := _
example {P Q: α → Prop}(ee: (∃x, P x) ∨ (∃x, Q x)): ∃x, P x ∨ Q x := _
```
