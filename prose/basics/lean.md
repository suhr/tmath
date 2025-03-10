# Lean

Lean это система интерактивного доказательства теорем, основанная на исчислении индуктивных построений. Она станет нашим основным инструментом.

## Установка

Для работы с Lean нам потребуется система управления версиями Git и редактор исходного кода Visual Studio Code.

Переходим по ссылкам и скачиваем оба приложения, после чего устанавливаем сначала Git, а затем Visual Studio Code. Открываем Visual Studio Code. На панели слева щёлкаем по иконке с четырьмя квадратами — откроется панель расширений. Вводим `lean4` в строку поиска и устанавливаем расширение.

Нам осталось лишь открыть проект. Используем Git, чтобы скачать и открыть заготовленный проект. Для этого нажимаем клавишу F1 и в появившейся строке поиска вводим `git clone` и нажимаем `Enter`. Visual Studio Code попросит URL репозитория, вставляем в поле ввода `https://github.com/suhr/polygon.git` и снова нажимаем `Enter`. Выбираем директорию, в которую будет скачана директория с проектом.

На панели слева выбираем иконку с двумя листами бумаги. Откроется панель файлов. Щёлкаем по файлу `Basics.lean` чтобы открыть его.

## Основы Lean

Начнём с синтаксиса примеров и определений.

Определение `name` как значения `expr` типа `type` записывается в Lean следующим образом:

```lean
def name: type := expr
```

Когда определение представляет собой доказательство некоторого высказывания, вместо слова `def` принято писать слово `theorem`:

```lean
theorem name: type := expr
```

Декларация, что выражение `expr` является примером значения типа `type`, записывается как

```lean
example: type := expr
```

Выражение `expr` может быть перенесено на следующую строку, а также может быть разбито на несколько строк. В таком случае каждая строка выражения должна начинаться с отступа. Отступ вводится с помощью клавиши `Tab`.

Рассмотрим теперь синтаксис выражений в Lean:

- Лямбда-абстракция $λx:τ.\; e$ записывается в Lean как `λx:τ ↦ e` или как `fun x: τ => e`. Вместо `λx:α ↦ λy:β ↦ e` можно просто писать `λ(x:α)(y:β) ↦ e`
- Применение $e_1\ e_2$ записывается как `e1 e2`. Важно: применение в выражении *всегда* пишется через пробел. Запись вроде `f(x)` или `(f a)b` синтаксически некорректна
- Тип функций $∀x:σ.\; τ$ записывается как `∀x:σ, τ`. Можно также писать `(x:σ) → τ`
- Запись `let x := v;  e` означает выражение `e`, в котором `x` определено как `v`. Точку с запятой можно опустить, если `e` начинается с новой строки
- `(e : τ)` представляет собой выражение `e` вместе с явным указанием того, что оно имеет тип `τ`

Lean широко использует символы Unicode, отсутствующие на стандартной клавиатуре. Расширение Lean в Visual Studio Code предоставляет метод ввода математических символов.

Ввод символа начинается с ввода обратной косой черты, после которой следует имя символа. Если введённое имя однозначно определяет требуемый символ и не является префиксом имени какого-то другого символа, метод ввода немедленно заменяет введённое имя на требуемый символ. В противном случае, ввод символа можно завершить, нажав клавишу `Tab` или пробел.

Имена греческих букв совпадает с их именами на английском языке. Так, например, `\lambda` вводит `λ`, а `\sigma` и `\tau` вводят `σ` и `τ`. Если первая буква имени является заглавной, то и вводимая буква тоже будет заглавной. Например, `\Gamma` превращается в `Γ`.

Символы `→` (стрелка), `↦` (другая стрелка), `∧` (конъюнкция), `∨` (дизъюнкция) и `¬` (отрицание) вводятся, соответственно, как `\to`, `\mapsto`, `\and`, `\or` и `\not`. Кванторы всеобщности и существования записываются как `\forall` и `\exists`.

Вселенные типов в Lean называются сортами, и записываются как `Sort 0`, `Sort 1` и так далее. Вселенная `Sort 0` является вселенной высказываний, и потому обозначается как `Prop`. Вселенные типов `Sort 1`, `Sort 2` и так далее обозначаются также как `Type 0`, `Type 1` и так далее. Вместо `Type 0` можно писать просто `Type`.

Покажем теперь синтаксис Lean, записав следующее выражение исчисления построений:

$$(λα\,β:\mathcal U_1.\; λx:α.\; λy:β.\; x) : ∀α\,β: \mathcal U_1.\; (x:α) → (y:β) → α$$

В Lean этот пример примет следующий вид:

```lean
example: ∀α β: Type, α → β → α :=
  λ(α β: Type)(x:α)(y:β) ↦ x
```

В этой записи связывающие переменные и их типы встречаются дважды: один раз в типе и второй раз в выражении. Lean предоставляет сокращение, позволяющее избежать подобного повторения:

```lean
example (α β: Type)(x:α)(y:β): α := x
```

Сокращённую запись можно воспринимать следующим образом: пример является функцией, которая, будучи применена к `α` и `β` типа `Type`, `x` типа `α` и `y` типа `β`, становится выражением `x` типа `α`.

Превратим теперь наш пример в определение:

```lean
def f1 (α β: Type)(x:α)(_:β): α := x
```

Подчёркивание вместо имени связывающей переменной означает, что связываемое значение не используется в определении.

Lean это *интерактивное* средство доказательства теорем. Панель Lean Infoview в правой половине экрана показывает различную полезную информацию. Одной из вещей, которую показывает эта панель, является контекст и ожидаемый тип в том месте, куда установлен курсор редактора.

Поставим курсор непосредственно перед выражением `x` в определении `f1`.  Lean Infoview покажет следующую информацию:

```
α β : Type
x : α
x✝ : β
⊢ α
```

Список до символа турникета представляет собой контекст выражения, а тип после турникета является ожидаемым типом выражения.

С Lean можно взаимодействовать посредством команд, которые вводятся прямо в редактор. Рассмотрим некоторые из этих команд.

Команда `#check` проверяет, что выражение корректно типизированно, и выводит его тип. Поставив курсор на `#check f1 Nat Nat 3 5` можно узнать, что это выражение имеет тип `Nat`.

Команда `#reduce` редуцирует выражение. Поставив курсор на `#reduce f1 Nat Nat 3 5`, можно узнать, что результатом вычисления выражения является число `3`.

И, наконец, команда `#print` печатает определение той или иной сущности. Например, `#print f1` показывает полное определение этой функции.

Lean умеет сам выводить некоторые значения, в первую очередь типы. Чтобы попросить Lean вывести требуемое значение, достаточно написать символ подчёркивания на месте выводимого выражения. Например, следующим образом можно попросить Lean вывести типы, к которым применяется функция `f1`:

```lean
#check f1 _ _ 3 5
```

Подчёркивания в выражении называются *дырками.* Здесь Lean выводит, что требуемыми значениями на месте дырок является тип натуральных чисел `Nat`.

В лямбда-абстракции, тип при связывающей переменной можно просто опустить. Например, вместо `λP: Prop ↦ ¬P` или `λP: _ ↦ ¬P` можно писать просто `λP ↦ ¬P`.

В примере или определении функции, некоторые аргументы можно пометить как неявные, заключив их в фигурные скобки. Неявные аргументы выводятся автоматически и не указываются при применении функции.

В качестве примера функции с неявным аргументами, определим `f2` следующим образом:

```lean
def f2 {α β: Type}(x:α)(_:β): α := x
```

В отличие от функции `f1`, функция `f2` не требует перечисления типов в применении:

```lean
#check f2 3 5
```

При необходимости, неявные аргументы можно указать. Если в выражении перед именем функции стоит символ `@`, то тогда функция используется так же, как и функция, у которой все аргументы явные:

```lean
#check @f2 Nat Nat 3 5
```

Есть и другой способ указать явный аргумент — по имени:

```lean
#check f2 (β := Nat) 3 5
```

Lean позволяет обобщить определение или пример для всех вселенных типов. Например:

```lean
example {α β: Sort u}(x:α)(_:β): α := x
```

Кроме того, в примере выше `{α β: Sort u}` можно опустить:

```lean
example (x:α)(_:β): α := x
```

В этом случае, Lean сам обобщает пример для всех вселенных типов наиболее общим образом.

Рассмотрим теперь возможности Lean связанные с индуктивными типами.

Особой разновидностью индуктивных типов в Lean являются так называемые структуры. С точки зрения ядра Lean структуры являются индуктивными типами с единственным конструктором. Для пользователя, однако, Lean предоставляет дополнительные способы взаимодействия с ними.

Примером типа структуры является тип `Prod`, определённый следующим образом:

```lean
structure Prod (α : Type u) (β : Type v) where
  fst : α
  snd : β
```

Тип `Prod α β` представляет тип пар значений, где первое значение в паре имеет тип `α`, а второе значение имеет тип `β`. Тип пар также называют произведение типов `α` и `β` и обозначают как `α × β` (символ `×` вводится как `\times`).

Определение вводит индуктивный тип `Prod` с конструктором `Prod.mk` типа `α → β → Prod α β`. Кроме того, Lean определяет функции `Prod.fst` типа `Prod α β → α` и `Prod.snd` типа `Prod α β → β`, называемые *проекциями* структуры.

Вместе с типом, Lean также вводит одноимённое *пространство имён.* Точка предоставляет доступ к имени в пространстве имён, так, например, запись `Prod.mk` означает функцию `mk` в пространстве имён `Prod`.

Результатом применения `Prod.fst` и `Prod.snd` к значению типа `Prod α β` является, соответственно, левое и правое значение в паре. Например, результатом применения `Prod.fst` к `Prod.mk 3 5` является число `3`, когда же результатом применения `Prod.snd` является число `5`.

Если `e` это значение типа `T`, а `f` это некоторая функция, определённая в пространстве имён `T`, то тогда `e.f` означает то же самое, что и `T.f e`. Например, `(Prod.mk 3 5).fst` это то же самое выражение, что и `Prod.fst (Prod.mk 3 5)`.

Структуру можно построить, указав значение для каждой из её проекций:

```lean
#check ({fst := 3, snd := 5} : Nat × Nat)
```

Кроме того, структуру, как и любой другой тип с единственным конструктором, можно построить, перечислив значения в угловых скобках:

```lean
#check (⟨3, 5⟩ : Nat × Nat)
```

Угловые скобки вводятся как `\langle` и `\rangle`.

Любое значение индуктивного типа с единственным конструктором можно разобрать, используя *сопоставление с образцом.* Делается это следующим образом:

```lean
#reduce
  let (Prod.mk f s) := Prod.mk 3 5
  f
```

В этом выражении, `let` определяет такие `f` и `s`, что `Prod.mk f s` это в точности то же значение, что и `Prod.mk 3 5`. Синтаксическое выражение слева от `:=` называется *образцом.*

Нотацию для структур и перечисление в угловых скобках можно также использовать в качестве образца:

```lean
#reduce
  let {fst := f, snd := _} := Prod.mk 3 5
  f

#reduce
  let ⟨f,_⟩ := Prod.mk 3 5
  f
```

## Упражнения

Время упражнений! Будем доказывать простые логические тождества.

Конъюнкция, дизъюнкция, абсурд и квантор существования определены в Lean как индуктивные типы. Мы не будем разбирать их определения, всё, что нам нужно знать, это типы следующих функций:

```
And.intro : ∀{a b: Prop}, a → b → a ∧ b
And.left  : ∀{a b: Prop}, a ∧ b → a
And.right : ∀{a b: Prop}, a ∧ b → b

Or.inl  : ∀{a b: Prop}, a → a ∨ b
Or.inr  : ∀{a b: Prop}, b → a ∨ b
Or.elim : ∀{a b c: Prop}, a ∨ b → (a → c) → (b → c) → c

False.elim : ∀{C: Sort u}, False → C

Exists.intro : ∀{α: Sort u}{P: α → Prop},
  (x:α) → P x → Exists P
Exists.elim : ∀{α: Sort u}{P: α → Prop}{β : Prop},
  (∃x, P x) → (∀x:α, P x → β) → β
```

Эти функции выражают соответствующие правила введения и удаления связок и квантора всеобщности. Высказывание `¬P` определено в Lean как `P → False`.

Рассмотрим теперь процесс доказательства высказываний на примерах.

Для начала, докажем, что если `P ∨ Q`, и если `¬P`, то тогда `Q`. Начнём доказательство с записи соответствующего примера с дыркой на месте будущего свидетельства:

```lean
example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  _
```

Lean не может придумать доказательство, требуемое на месте дырки. Но зато он может показать ожидаемый тип дырки и её контекст. Достаточно поставить курсор непосредственно перед дыркой, и Lean покажет следующее:

```
don't know how to synthesize placeholder
context:
pq : P ∨ Q
np : ¬P
⊢ Q
```

Нам необходимо построить значение типа `Q`. Чтобы решить эту задачу, можно использовать перечисленные в контексте значения. Использовать `np` типа `¬P` мы пока что не можем, так как для этого требуется значение типа `P`, которого у нас нет. Но мы можем использовать `pq`, применив к нему функцию `Or.elim`:

```lean
example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  pq.elim _ _
```

Lean Infoview позволяет узнать контекст как первой дырки:

```
pq : P ∨ Q
np : ¬P
⊢ P → Q
```

Так и второй:

```
pq : P ∨ Q
np : ¬P
⊢ Q → Q
```

Значением типа `Q → Q` является, очевидно, функция `λq ↦ q`. Это позволяет немедленно закрыть вторую дырку:

```lean
example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  pq.elim _ (λq ↦ q)
```

Доказательством высказывания `P → Q` является лямбда-абстракция, предполагающая `P`:

```lean
example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  pq.elim (λp ↦ _) (λq ↦ q)
```

Контекст дырки в лямбде выглядит следующим образом:

```
pq : P ∨ Q
np : ¬P
p : P
⊢ Q
```

Теперь мы можем использовать `np` чтобы доказать `Q`. Для этого применим `np` к `p`, чтобы получить абсурд, и затем используем `False.elim` чтобы получить из абсурда свидетельство `Q`:

```lean
example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  pq.elim (λp ↦ False.elim (np p)) (λq ↦ q)
```

Закрытие всех дырок завершает доказательство.

Важно уметь сопоставить выражение с рассуждением по шагам. Построенному доказательству соответствует следующее рассуждение:

1. Пусть $P ∨ Q$, и пусть $¬P$
   1. Рассмотрим $P ∨ Q$
      1. Пусть $P$
         1. Но это невозможно, так как $¬P$
      2. Пусть $Q$
         1. Тогда $Q$
2. Следовательно, $(P ∨ Q) → ¬P → Q$

Рассмотрим теперь другой пример. Докажем, что из $P ∧ (Q ∨ R)$ следует $(P ∧ Q) ∨ (P ∧ R)$. Начинаем, как и раньше, с дырки:

```lean
example {P Q R: Prop}(pqr: P ∧ (Q ∨ R)): (P ∧ Q) ∨ (P ∧ R) :=
  _
```

У нас есть свидетельство истинности $P ∧ (Q ∨ R)$, и естественно разобрать его на свидетельство $P$ и свидетельство $Q ∨ R$. Для этого можно использовать функции `And.left` и `And.right`. Но `And` это индуктивный тип с единственным конструктором, что позволяет разобрать значение с помощью сопоставления с образцом:

```lean
example {P Q R: Prop}(pqr: P ∧ (Q ∨ R)): (P ∧ Q) ∨ (P ∧ R) :=
  let ⟨p,qr⟩ := pqr
  _
```

Контекст дырки при этом принимает вид:

```
pqr : P ∧ (Q ∨ R)
p : P
qr : Q ∨ R
⊢ P ∧ Q ∨ P ∧ R
```

Как и в прошлом примере, единственное что мы можем сделать это применить `Or.elim`. Сделаем это, заодно введя соответствующие лямбда-абстракции:

```lean
example {P Q R: Prop}(pqr: P ∧ (Q ∨ R)): (P ∧ Q) ∨ (P ∧ R) :=
  let ⟨p,qr⟩ := pqr;
  qr.elim (λq ↦ _) (λr ↦ _)
```

Контекст первой дырки выглядит следующим образом:

```
pqr : P ∧ (Q ∨ R)
p : P
qr : Q ∨ R
q : Q
⊢ P ∧ Q ∨ P ∧ R
```

Значение типа `(P ∧ Q) ∨ (P ∧ R)` можно построить либо из значения `P ∧ Q`, либо из значения `P ∧ R`. Выбираем первое, применив `Or.inl`:

```lean
example {P Q R: Prop}(pqr: P ∧ (Q ∨ R)): (P ∧ Q) ∨ (P ∧ R) :=
  let ⟨p,qr⟩ := pqr;
  qr.elim (λq ↦ Or.inl _) (λr ↦ _)
```

Новая цель, новый контекст:

```
pqr : P ∧ (Q ∨ R)
p : P
qr : Q ∨ R
q : Q
⊢ P ∧ Q
```

Значение типа `P ∧ Q` можно построить с помощью конструктора `And.intro`, но мы воспользуемся угловыми скобками:

```lean
example {P Q R: Prop}(pqr: P ∧ (Q ∨ R)): (P ∧ Q) ∨ (P ∧ R) :=
  let ⟨p,qr⟩ := pqr;
  qr.elim (λq ↦ Or.inl ⟨p,q⟩) (λr ↦ _)
```

Оставшееся дырка закрывается схожим образом:

```lean
example {P Q R: Prop}(pqr: P ∧ (Q ∨ R)): (P ∧ Q) ∨ (P ∧ R) :=
  let ⟨p,qr⟩ := pqr;
  qr.elim (λq ↦ Or.inl ⟨p,q⟩) (λr ↦ Or.inr ⟨p,r⟩)
```

Доказательству выше соответствует следующее рассуждение:

1. Пусть $P ∧ (Q ∨ R)$
   1. Тогда $P$
   2. И $Q ∨ R$
   3. Рассмотрим $Q ∨ R$
       1. Пусть $Q$
          1. Тогда $P ∧ Q$
          2. И, следовательно, $(P ∧ Q) ∨ (P ∧ R)$
       2. Пусть $R$.
          1. Тогда $P ∧ R$
          2. И отсюда $(P ∧ Q) ∨ (P ∧ R)$
2. Следовательно, $P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)$

Теперь посмотрим, как доказываются высказывания с кванторами. Докажем, что из $∀x.\; P\ x ∧ Q\ x$ следует $(∀x.\; P\ x) ∧ (∀x.\; Q\ x)$:

```lean
example {P Q: α → Prop}(apq: ∀x, P x ∧ Q x): (∀x, P x) ∧ (∀x, Q x) :=
  _
```

Конъюнкцию можно построить с помощью угловых скобок:

```lean
example {P Q: α → Prop}(apq: ∀x, P x ∧ Q x): (∀x, P x) ∧ (∀x, Q x) :=
  ⟨_, _⟩
```

Посмотрим на контекст первой дырки:

```
P Q : α → Prop
apq : ∀ (x : α), P x ∧ Q x
⊢ ∀ (x : α), P x
```

Пусть `x` это значение типа `α`:

```lean
example {P Q: α → Prop}(apq: ∀x, P x ∧ Q x): (∀x, P x) ∧ (∀x, Q x) :=
  ⟨λx ↦ _, _⟩
```

Контекст новой дырки:

```
P Q : α → Prop
apq : ∀ (x : α), P x ∧ Q x
x : α
⊢ P x
```

Применение `apq` к `x` даёт значение типа `P x ∧ Q x`, из которого свидетельство `P x` можно достать, применив проекцию:

```lean
example {P Q: α → Prop}(apq: ∀x, P x ∧ Q x): (∀x, P x) ∧ (∀x, Q x) :=
  ⟨λx ↦ (apq x).left, _⟩
```

Аналогично закрывается последняя дырка:

```lean
example {P Q: α → Prop}(apq: ∀x, P x ∧ Q x): (∀x, P x) ∧ (∀x, Q x) :=
  ⟨λx ↦ (apq x).left, λx ↦ (apq x).right⟩
```

Рассуждение:

1. Пусть $∀x.\; P\ x ∧ Q\ x$
   1. Пусть $x:α$
      1. Тогда $P\ x ∧ Q\ x$
      2. И отсюда $P\ x$
   2. Следовательно, $∀x.\; P\ x$
   3. Пусть $x:α$
      1. Тогда $P\ x ∧ Q\ x$
      2. И отсюда $Q\ x$
   4. Следовательно, $∀x.\; Q\ x$
   5. Отсюда $(∀x.\; P\ x) ∧ (∀x.\; Q\ x)$
2. Следовательно, $(∀x.\; P\ x ∧ Q\ x) → (∀x.\; P\ x) ∧ (∀x.\; Q\ x)$

Последний пример показывает, как доказываются высказывания с квантором существования. Докажем, что если `∃x, ∀y, P x y`, то тогда `∀y, ∃x, P x y`:

```lean
example {P: α → β → Prop}(eap: ∃x, ∀y, P x y): ∀y, ∃x, P x y :=
  _
```

Начнём доказательство с того, что разберём `eap` на части и предположим `y`:

```lean
example {P: α → β → Prop}(eap: ∃x, ∀y, P x y): ∀y, ∃x, P x y :=
  let ⟨x,ap⟩ := eap
  λy ↦ _
```

Контекст дырки:

```
P : α → β → Prop
eap : ∃ x, ∀ (y : β), P x y
x : α
ap : ∀ (y : β), P x y
y : β
⊢ ∃ x, P x y
```

Чтобы доказать `∃x, P x y`, нужно предоставить некоторое значение `x` вместе с доказательством `P x y`. Имена переменных предлагают взять `x` в качестве такого `x`:

```lean
example {P: α → β → Prop}(eap: ∃x, ∀y, P x y): ∀y, ∃x, P x y :=
  let ⟨x,ap⟩ := eap
  λy ↦ ⟨x, _⟩
```

Осталось лишь доказать `P x y`. Для этого достаточно применить `ap` к `y`:

```lean
example {P: α → β → Prop}(eap: ∃x, ∀y, P x y): ∀y, ∃x, P x y :=
  let ⟨x,ap⟩ := eap
  λy ↦ ⟨x, ap y⟩
```

Это завершает доказательство последнего из примеров.

Упражнения на связки и кванторы, которые читателю предстоит решить, находятся в файле `Basics.lean`. Решение этих упражнений сводится к замене заглушки `sorry` на корректное доказательство соответствующего высказывания.

Для решения этих упражнений не обязательно использовать продвинутые возможности Lean вроде сопоставления с образцом. Каждое из высказываний можно доказать, используя лишь типизированные лямбда-выражения и определённые для связок и квантора существования функции.

Простые упражнения являются обязательными. Их значение трудно переоценить: **если читатель не способен решить простые упражнения на связки и кванторы, то дальше книгу он может не читать.** Последующий текст будет полагаться на всё более развитые навыки построения доказательств.

Особняком стоят упражнения на классическую логику. Их решать не обязательно (хотя ознакомиться с ними всё же полезно). Мы ближе познакомимся с классической логикой в будущем, когда будем рассматривать аксиому выбора.

## Равенство

Равенство в Lean определено как индуктивное семейство типов `Eq`. Оставим в очередной раз на потом обзор индуктивных семейств, и рассмотрим равенство с точки зрения его свойств.

Два ключевых свойства равенства

- Любое значение равно самому себе
- Равные значения взаимозаменяемы

Первое свойство называется *рефлексивностью,* и в Lean его выражает функция `Eq.refl`:

```
Eq.refl: {α: Sort u} → (a: α) → a = a
```

Эта функция также называется `rfl`.

Если значения взаимозаменяемы, то любое свойство, что верно для одного значения, верно и для другого. Функция `Eq.subst` утверждает в точности это:

```
Eq.subst: {α: Sort u} → {motive: α → Prop} → {a b: α} →
  (eq: a = b) → (m: motive a) → motive b
```

Функция `Eq.ndrec` обобщает эту идею за пределы `Prop`:

```
Eq.ndrec: {α: Sort u} → {a: α} → {motive: α → Sort v} →
  (m: motive a) → {b: α} → (eq: a = b) → motive b
```

Иной порядок аргументов у `Eq.ndrec` по сравнению с `Eq.subst` связан с тем, что `Eq.ndrec` представляет собой упрощённую версию рекурсора индуктивного семейства `Eq`.

Докажем теперь несколько свойств равенства. Для начала докажем *симметричность*: если `x = y`, то и `y = x`.

```lean
example {x y: α}(e: x = y): y = x :=
  e.subst (motive := λt ↦ t = x) (rfl: x = x)
```

Доказательство работает следующим образом: поскольку равенство рефлексивно, x удовлетворяет свойству `λt ↦ t = x`. Но `x = y`, и потому `y` должно удовлетворять тому же свойству.

Lean позволяет записать это доказательство короче:

```lean
example {x y: α}(e: x = y): y = x :=
  e ▸ (rfl: x = x)
```

Но в целях наглядности, мы пока будем использовать `Eq.subst`, явно указывая мотив.

*Транзитивность* равенства означает, что если `x = y` и `y = z`, то тогда `x = y`. Она доказывается почти так же, как и симметричность:

```lean
example {x y z: α}(xy: x = y)(yz: y = z): x = z :=
  yz.subst (motive := λt ↦ x = t) (xy: x = y)
```

Применение функции сохраняет равенство: если `x = y`, то `f x = f y`. И снова то же самое доказательство, только с другим мотивом:

```lean
example {x y: α}{f: α → β}(e: x = y): f x = f y :=
  e.subst (motive := λt ↦ f x = f t) (rfl: f x = f x)
```

Симметричность, транзитивность и применение функции к обеим частям равенства уже определены в Lean как `Eq.symm`, `Eq.trans` и `Eq.congrArg`.

Мы рассмотрели примеры того, как два значения могут быть равны. Рассмотрим теперь, как два значения могут быть *не равны,* иначе говоря, каким образом из равенства двух значений может следовать абсурд.

В качестве таких значений возьмём значения `false` и `true` типа `Bool`. Этот индуктивный тип определён в Lean следующим образом:

```lean
inductive Bool : Type where
| false : Bool
| true : Bool
```

Рекурсором `Bool` является функция `Bool.rec`:

```
Bool.rec: {motive: Bool → Sort u} →
  motive false → motive true →
  (t: Bool) → motive t
```

Вместе с рекурсором, Lean также определяет различные полезные функции. Одной из них является функция `Bool.casesOn`, определенная следующим образом:

```lean
def Bool.casesOn {motive : Bool → Sort u} →
    (b: Bool) → motive false → motive true : motive t :=
  Bool.rec f t b
```

Наша задача состоит в том, чтобы доказать, что из `false = true` следует абсурд. Для этого рассмотрим следующее определение, также вводимое Lean вместе с индуктивным типом:

```lean
def Bool.noConfusionType (P: Sort u)(x:Bool)(y:Bool): Sort u :=
  x.casesOn (y.casesOn (P → P) P) (y.casesOn P (P → P))
```

Вычислим `Bool.noConfusionType False a b` для различных значений `a` и `b`:

```lean
#reduce Bool.noConfusionType False false false  -- False → False
#reduce Bool.noConfusionType False false true   -- False
#reduce Bool.noConfusionType False true false   -- False
#reduce Bool.noConfusionType False true true    -- False → False
```

Видно, что функция `Bool.noConfusionType P`, будучи применена к одним и тем же константам типа `Bool`, вычисляется в тип `P → P`, когда же применённая к различным константам, вычисляется в `P`.

Определим теперь функцию `bool_d`, которая для любого типа `P` и любого значения `b` типа `Bool` строит значение типа `Bool.noConfusionType P b b`. Начнём построение требуемого выражения с применения `Bool.casesOn`:

```lean
def bool_d {P: Sort u}(b: Bool): Bool.noConfusionType P b b :=
  b.casesOn _ _
```

Посмотрим на контекст левой дырки:

```
b : Bool
⊢ Bool.noConfusionType P false false
```

Тип дырки `Bool.noConfusionType P false false` вычислительно равен типу `P → P`, так что функция `λp ↦ p` закрывает её:

```lean
def bool_d {P: Sort u}(b: Bool): Bool.noConfusionType P b b :=
  b.casesOn (λp ↦ p) _
```

Правая дырка имеет тип `Bool.noConfusionType P true true`, и потому закрывается так же:

```lean
def bool_d {P: Sort u}(b: Bool): Bool.noConfusionType P b b :=
  b.casesOn (λp ↦ p) (λp ↦ p)
```

С помощью функции `bool_d` мы можем наконец доказать, что `false` не равно `true`:

```lean
example (h: false = true): False :=
  Eq.subst (motive := λt ↦ Bool.noConfusionType _ false t) h (bool_d false)
```

Посмотрим внимательнее на это доказательство. Выражение `bool_d false` является значением типа `Bool.noConfusionType False false false`. Гипотетическое свидетельство равенства `false` и `true` позволяет преобразовать его в значение типа `Bool.noConfusionType False false true`. Но тип `Bool.noConfusionType False false true` вычислительно равен `False`, и потому построенное выражение является свидетельством абсурда.

Вместе с индуктивным типом `Bool`, Lean уже определил функцию `Bool.noConfusion`, обобщающую это доказательство:

```
Bool.noConfusion: {P : Sort u} → {a b : Bool} →
  (eq: a = b) → Bool.noConfusionType P a b
```

Так что значение произвольного типа `P` можно получить, просто применив `Bool.noConfusion` к гипотетическому свидетельству равенства `false` и `true`.

Мы можем различить два значения типа `Bool` только благодаря разбору во вселенную типов — отображению значения в тот или иной тип в зависимости от того, вычисляется ли оно в `false` или `true`.

Как мы говорили ранее, исчисление индуктивных построений не допускает подобный разбор для индуктивных типов в `Prop`. Таким образом нет никакой возможности различить два значения индуктивного типа в `Prop`. Нельзя, например, доказать, что `Or.inl p ≠ Or.inr q`.

На самом деле, невозможность различать значения не ограничивается индуктивными типами. Никакие два значения произвольного типа в `Prop` не могут быть различены.

И тут мы приходим к важному принципу: неразличимые значения неотличимы от равных.

В исчислении построений, один тип может быть заменён другим, если эти типы вычислительно равны. В Lean, вычислительное равенство заменяется на *равенство по определению.* Два значения равны по определению, если они вычислительно равны, но кроме того, в Lean любые два свидетельства истинности одного и того же высказывания равны по определению.

Это позволяет доказать, к примеру, следующее:

```lean
example (P Q: Prop)(p: P)(q: Q): Or.inl p = Or.inr q :=
  rfl
```

Таким образом, различные доказательства одного и того же высказывания в Lean представляют собой различные записи одного и того же свидетельства истинности высказывания — аналогично тому, как одно и то же число может быть записано множеством способов.

В будущем мы увидим, зачем нужно это отождествление, и познакомимся с другими примерами отождествления неразличимых значений.

А сейчас обратим внимание на следующее: нетривиальное равенство порождает различие между формой и смыслом. Возьмём для для примера знаменитое равенство:

$$0{,}(9) = 1$$

Записи этих чисел, очевидно, различны. Выражения, которые могут соответствовать этим записям, также различны. Но свойства вещественных чисел позволяют построить равенство между значениями, тем самым выявляя, что речь идёт про одно и то же число.
