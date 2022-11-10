# Lean

Lean это интерактивный прувер (средство интерактивного доказательства теорем), основанный
на исчислении конструкций.

Синтаксис выражений в Lean:

- `λx:τ => e`.
  - Для нескольких переменных можно также писать `λ(x:α)(y:β) => e` и `λx y: τ => e`
  - Если переменная не используется, то вместо неё пишется подчёркивание: `λ_:τ => e`
  - Ещё одна запись: `fun x:τ => e`
- `e1 e2`
  - Другой синтаксис: `e1 $ e2`. Он правоассоциативен: `f $ g $ h` означает `f $ (g $ h)`
  - Пробел и `$` различаются по приоритету: `f x + y` означает `(f x) + y`, когда же `f $ x + y` это `f (x + y)`
- `∀x:α, β`. Переменные перечисляются точно также, как и у абстракции
- `let x := v;  e` это по смыслу ${\color{red}e}[{\color{red}x} := {\color{red}v}]$ — выражение `e`, где `x` определено как `v`

**Важно:** Применение *всегда* пишется через пробел, даже если выражения обёрнуты в скобки.
В противном случае, Lean выдаёт крайне неинформативную ошибку «expected command».

Вселенные типов в Lean называются сортами и пишутся как `Sort 0`, `Sort 1` и так далее. Кроме того,
у них есть и альтернативные имена: 

```
Prop : Type 0 : Type 1 : Type 2 : ...
```

Вселенная `Prop` (она же `Sort 0`) обладает особыми свойствами, в том числе правила типизации
для неё несколько другие, чем для остальных вселенных. Мы рассмотрим эти различия позже.

`Type 0` таже записывается как просто `Type`.

А сейчас, установим Lean и создадим проект, как показано в этом видео:

```{raw} html
<iframe width="720" height="380" src="https://www.youtube.com/embed/yZo6k48L0VY" title="Getting Started with Lean 4 in Visual Studio Code" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe>
```

Далее, опишем всё сразу кодом.

```lean
-- Коментарий начинается с `--`
-- Lean это действительно интерактивный прувер, и в нем можно получить ответ,
-- просто введя команду в текстовый редактор

-- Команда `#check` позволяет проверить, что выражение корректно типизированно
-- `(e : τ)` это то же выражение, что и `e`, но с указанием типа
#check ((λα β: Type => λx:α => λ_:β => x) : ∀α β: Type, α → β → α)
-- Lean во многих случаях может сам вывести тип, и тогда его не нужно указыать
#check λ(α β: Type)(x:α)(_:β) => x

-- Пример это определение без имени
example: ∀α β: Type, α → β → α := λ(α β: Type)(x:α)(_:β) => x
-- `∀α β: Type` и `λ(α β: Type)` дублируют друг друга. Но есть короткая запись:
example (α β: Type): α → β → α := λ(x:α)(_:β) => x
-- Или даже:
example (α β: Type)(x:α)(_:β): α := x

-- Можно определить функцию
def f1 (α β: Type)(x:α)(_:β): α := x
-- И использовать её:
#check f1 Nat Nat 3 5
-- Команда `#reduce` позволяет вычислить выражение:
#reduce f1 Nat Nat 3 5
-- С помощью подчёркиваний, можно попросить Lean вывести тип за нас:
#check f1 _ _ 3 5

-- Чтобы не писать каждый раз подчёркивания, можно определить функцию так:
def f2 {α β: Type}(x:α)(_:β): α := x
-- `α` и `β` это неявные аргументы, которые не указываются при применении:
#check f2 3 5
-- Но если необходимо, можно указать их все явно:
#check @f2 Nat Nat 3 5
-- Или указать лишь некоторые, по имени:
#check f2 (β := Nat) 3 5

-- Lean позволяет определить функцию сразу для всех вселенных:
example {α β: Sort u}(x:α)(_:β): α := x
-- И явное указание вселенной можно опустить
example (x:α)(_:β): α := x
```

## Типы данных в Lean

Lean сразу предоставляет множество различных типов данных. Рассмотрим некоторые из них.

Команда `#print` позволяет больше узнать о типе или функции. Написав `#print Bool` мы узнаём следующее:

```
inductive Bool : Type
number of parameters: 0
constructors:
Bool.false : Bool
Bool.true : Bool
```

Если использовать действие VS Code «перейти к определению» (клавиша F12, когда курсор на слове `Bool`), то откроется файл `Prelude.lean` со следующим определением:

```lean
inductive Bool : Type where
  /-- The boolean value `false`, not to be confused with the proposition `False`. -/
  | false : Bool
  /-- The boolean value `true`, not to be confused with the proposition `True`. -/
  | true : Bool

export Bool (false true)
```

`Bool` это *индуктивный тип*. Это означает, что определены следующие константы:

- `Bool : Type`
- `Bool.false : Bool`
- `Bool.true : Bool`

Константы `Bool.false` и `Bool.true` называются конструкторами значения типа `Bool`. Директива `export Bool (false true)` позволяет их писать как просто `false` и `true`.

Выражение `match b with ...` сопоставляет значение `b: Bool` с каждым из конструктором, и, в зависимости от того, является ли оно значением `false` или значением `true`, вычисляется в то или иное выражение.

Например, применение следующей функции к `false` вычисляется в `true`, а применение к `true` — в `false`:

```lean
def neg (b:Bool): Bool :=
  match b with
  | false => true
  | true  => false

#reduce neg false
#reduce neg true
```

Ветви `| v => e` можно также писать и на одной строке. Кроме того, для таких функций есть также сокращённая запись:

```lean
example: Bool → Bool
| false => true    | true  => false
```

Сопоставлять можно не только одно значение, но и несколько. Например, функцию, которая вычисляется в `false`, когда два значения типа `Bool` равны, и в `true`, когда не равны, можно определить так:

```lean
example: Bool → Bool → Bool
| false, false => false    | false, true  => true
| true,  false => true     | true,  true  => false
```

Натуральные числа в Lean это также индуктивный тип:

```lean
inductive Nat where
  /-- `Nat.zero`, normally written `0 : Nat`, is the smallest natural number.
  This is one of the two constructors of `Nat`. -/
  | zero : Nat
  /-- The successor function on natural numbers, `succ n = n + 1`.
  This is one of the two constructors of `Nat`. -/
  | succ (n : Nat) : Nat
```

Это то же определение натуральных чисел, что мы использовали когда говорили про функции. В математике, тип натуральных чисел таже обозначают как $ℕ$.

Натуральное число может быть построено двумя способами: либо с помощью конструктора `Nat.zero`, либо из какого-то другого натурального числа `n` с помощью конструктора `Nat.succ`. И сопоставление позволяет достать число `n` из числа `Nat.succ n`:

```lean
def pred: Nat → Nat
| Nat.zero   => 0
| Nat.succ n => n

#reduce pred (pred 5)
```

Мы также можем определять рекурсивные функции на натуральных числах. Например, алгоритм сложения, который мы рассматривали когда говорили о функциях:

```lean
def add1 (n:Nat): Nat → Nat
| 0          => n
| Nat.succ k => add1 n.succ k
```

Здесь `n.succ` это сокращённая запись `Nat.succ n`.

Другое определение сложения, где функция применяется к тому же значению `n`:

```lean
def add2 (n:Nat): Nat → Nat
| 0          => n
| Nat.succ k => (add2 n k).succ
```

Lean позволяет только ту рекурсию, где аргумент структурно уменьшается (например, в ветке `Nat.succ k` функция применяется к `k`). Например, Lean не принимает следующую функцию:

```lean
def il: Nat → Nat
| 0 => 0
| Nat.succ n => il n.succ
```

Рекурсивные определения с сопоставлением на самом деле не являются частью ядра Lean — они транслируются в другие выражения. Используя команду `#print`, мы можем посмотреть, в какие именно. Например, `add2` преобразуется в

```lean
def add2 : Nat → Nat → Nat :=
fun n x =>
  Nat.brecOn x fun x f =>
    (match (motive := (x : Nat) → Nat.below x → Nat) x with
      | 0 => fun x => n
      | Nat.succ k => fun x => Nat.succ x.fst.fst)
      f
```

Вместо прямой рекурсии здесь используется некая функция `Nat.brecOn`. Посмотрим что внутри:

```lean
@[reducible] protected def Nat.brecOn.{u} : {motive : Nat → Sort u} →
  (t : Nat) → ((t : Nat) → Nat.below t → motive t) → motive t :=
fun {motive} t F_1 =>
  (Nat.rec { fst := F_1 Nat.zero PUnit.unit, snd := PUnit.unit }
      (fun n n_ih =>
        { fst := F_1 (Nat.succ n) { fst := n_ih, snd := PUnit.unit }, snd := { fst := n_ih, snd := PUnit.unit } })
      t).1
```

Уф. К счастью, нам нужен не этот код, а только одна функция, которую он использует. Исследуем `Nat.rec` с помощью `#print`:

```
recursor Nat.rec.{u} : {motive : Nat → Sort u} →
  motive Nat.zero → ((n : Nat) → motive n → motive (Nat.succ n)) → (t : Nat) → motive t
```

И мы добрались до сути вещей. Рекурсор — это функция, которая есть у каждого индуктивного типа, которая и позволяет преобразовать значение этого типа в значение какого-либо другого типа.

Для натуральных чисел его можно описать так:

```lean
def natRec {M: Nat → Sort u}(z: M Nat.zero)(f: ∀n:Nat, M n → M n.succ): (t: Nat) → M t
| Nat.zero   => z
| Nat.succ n => f n (natRec z f n)
```

`M` это *мотив* — функция из числа в тип результата (тип результата может зависеть от значения!). `z` это результат применения функции к нулю, `f` вычисляет результат применения функции к `Nat.succ n` используя `n` и `natRec z f n`.

Сложение с использованием рекурсора выглядит так:

```lean
#reduce (λn => Nat.rec (motive := λ_ => Nat) n (λ_ s => s.succ)) 2 3
```

Распишем вычисление рекурсора по шагам:

```lean
#reduce (Nat.rec 2 (λ_ s => s.succ) : Nat → Nat) 3
#reduce (λ_ s => s.succ) 2 $ (Nat.rec 2 (λ_ s => s.succ) : Nat → Nat) 2
#reduce (λ_ s => s.succ) 2 $ (λ_ s => s.succ) 1 $ (Nat.rec 2 (λ_ s => s.succ) : Nat → Nat) 1
#reduce (λ_ s => s.succ) 2 $ (λ_ s => s.succ) 1 $ (λ_ s => s.succ) 0 $
  (Nat.rec 2 (λ_ s => s.succ) : Nat → Nat) 0
#reduce (λ_ s => s.succ) 2 $ (λ_ s => s.succ) 1 $ (λ_ s => s.succ) 0 $ 2
```

Здесь явно видно, что `Nat.rec z f n` это `f n $ … $ f 1 $ f 0 $ z` — обобщённая версия n-кратного применения функции к значению.

`Nat.recOn` это рекурсор с другим порядком аргументов. Кроме рекурсора, у индуктивных типов есть функция `casesOn`, аналогичная выражению `match`. Используя `#print`, видим, что она выражается через рекурсор:

```lean
@[reducible] protected def Nat.casesOn.{u} : {motive : Nat → Sort u} →
  (t : Nat) → motive Nat.zero → ((n : Nat) → motive (Nat.succ n)) → motive t :=
fun {motive} t zero succ => Nat.rec zero (fun n n_ih => succ n) t
```

Она просто отбрасывает рекурсивную часть.

`Prod α β` (также пишется как `α × β`) это произведение типов `α` и `β` — тип пар `(a,b)`, где `a:α` и `b:β`. `#print` говорит про него следующее:

```
inductive Prod.{u, v} : Type u → Type v → Type (max u v)
number of parameters: 2
constructors:
Prod.mk : {α : Type u} → {β : Type v} → α → β → α × β
```

И действительно, мы можем создавать пары с помощью `Prod.mk` и разбирать с помощью `Prod.casesOn`:

```lean
#reduce ( (Prod.mk 2 3).casesOn (λx y => (y,x)) : Nat×Nat )
```

Однако, если мы применим «перейти к определению» к `Prod`, то увидим нечто иное:

```lean
structure Prod (α : Type u) (β : Type v) where
  /-- The first projection out of a pair. if `p : α × β` then `p.1 : α`. -/
  fst : α
  /-- The second projection out of a pair. if `p : α × β` then `p.2 : β`. -/
  snd : β
```

Это *структура* с полями `fst:α` и `snd:β`. Каждое из полей соответствует аргументу единственного конструктора `Prod.mk`. Кроме того, определены проекции `fst: α×β → α` и `snd: α×β → β`, извлекающие соответствующее значение из пары:

```lean
#reduce (2,3).fst
#reduce (2,3).snd
```

Синтаксис `{f1 := v1, …}` позволяет указать значения полей структуры по имени. Например, `{snd := 3, fst := 2}` это то же самое, что и `(2,3)`:

```lean
#reduce ( {snd := 3, fst := 2} : Nat×Nat )
```

Ещё один способ создать пару значений:

```lean
#reduce ( ⟨2,3⟩ : Nat×Nat )
```

Если `T` это индуктивный тип с единственным конструктором, скажем, `T.mk`, то тогда `⟨v1, …, vn⟩ : T` это то же самое, что и `T.mk v1 … vn`.

Кроме произведения типов, есть также сумма типов `Sum α β` (также `α ⊕ β`). Она определена так:

```lean
inductive Sum (α : Type u) (β : Type v) where
  /-- Left injection into the sum type `α ⊕ β`. If `a : α` then `.inl a : α ⊕ β`. -/
  | inl (val : α) : Sum α β
  /-- Right injection into the sum type `α ⊕ β`. If `b : β` then `.inr b : α ⊕ β`. -/
  | inr (val : β) : Sum α β
```

Это значение c двумя вариантами: или это `inl a`, где `a:α`, или же это `inr b`, где `b:β`. `Sum.casesOn` позволяет вычислять различные значение в зависимости от того, левый вариант или правый:

```lean
#reduce ( (Sum.inl 3).casesOn pred Nat.succ : Nat )
#reduce ( (Sum.inr 3).casesOn pred Nat.succ : Nat )
```

Последний тип, который мы рассмотрим это `Empty`. `#print` говорит про него следующее:

```lean
inductive Empty : Type
number of parameters: 0
constructors:
```

Как будто у `Empty` нет конструкторов. Смотрим определение:

```lean
inductive Empty : Type
```

Действительно, никаких конструкторов.

Хотя значений типа `Empty` не существует, может существовать функция `Empty → Empty`:

```lean
#check λe:Empty => e
```

Дай мне невозможное, невозможное верну. Но интереснее рекурсор `Empty.rec`:

```
recursor Empty.rec.{u} : (motive : Empty → Sort u) → (t : Empty) → motive t
```

Так как значений типа `Empty` не существует, взамен такого значения можно пообещать *вообще что угодно* — и это обещание никогда не будет нарушено. Например, можно пообещать число:

```lean
#check λe:Empty => (e.rec : Nat)
```
