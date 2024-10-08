# Логика

Математика это в первую очередь не вычисления, а доказательства. Традиционно, доказательство определяют как рассуждение, убедительное настолько, что тот, кто его воспринял, будет готов убеждать других с помощью *того же* рассуждения. Математическое доказательство убеждает, что высказываемое утверждение без сомнения является истинным, а противное — невозможно.

Но смысл слов определяется тем, как их используют, и в математике слова используют значительно иначе, чем в обычной жизни. И отличаются не только сложные понятия вроде «убедительности», даже базовые логические конструкции вроде «из $P$ следует $Q$» используются иначе, чем в быту.

Обычно, точный смысл слов познаётся в процессе взаимодействия с людьми, обладающими нужными знаниями. Но в математике смысл слов определён настолько точно, что его можно обозначить не только с помощью общих принципов, но даже с помощью формальных правил.

Мы сформулируем принципы и правила естественного вывода для логики первого порядка. Эта логика является основой многих математических теорий, включая аксиоматическую теорию множеств. А рассматриваемые идеи станут основой и для исчисления построений — формальной системы, которую мы будем использовать в будущем.

Естественный вывод это набор правил, позволяющих вывести заключение из посылок. Посылки и заключение являются *суждениями*, называемыми также *утверждениями*

Утверждение это утверждаемое высказывание — то есть высказывание, которое мы признаём истинным. Оно записывается после знака $\vdash$ (турникет). Так, например, утверждение, что $1+2 = 3$ записывается так:

$$\vdash 1+2 = 3$$

Эту запись можно читать следующим образом: «я утверждаю (я знаю), что $1+2 = 3$».

Высказывания формируются из логических связок и констант, кванторов и предикатов (отношений). Предикаты применяются к одному или более выражению. Например, в высказывании $1 + 2 = 3$ отношение $(=)$ применяется к выражениям $1+2$ и $3$.

Логические связки формируют новые высказывания из существующих: если $P$ и $Q$ — высказывания, то высказываниями являются также $P → Q$ («если $P$, то $Q$»), $P ∧ Q$ («$P$ и $Q$»), $P ∨ Q$ («$P$ или $Q$»), $P ↔ Q$ («$P$ равносильно $Q$»), и $¬P$ («не $P$»).

Кванторы формируют высказывание, связывая переменную в логической формуле: например, $∃x.\; 2 = x$ («существует такое $x$, что $2 = x$») связывает переменную $x$ в формуле $2 = x$.

Логические константы являются высказываниями. Единственной константой которую мы рассмотрим является $⊥$ (абсурд).

Выражения это обычные математически выражения. Они строятся из констант, функциональных символов и переменных. Мы считаем, что выражению соответствует единственное конкретное значение.

Правила, по которым из посылок выводится заключение, имеют следующий вид:

$$\cfrac{\cal A_1 \qquad \cdots \qquad \cal A_n}{\cal B}$$

Здесь $\cal A_1, \dots, \cal A_n$ это посылки, когда же $\cal B$ — заключение.

Некоторые высказывания мы утверждаем без доказательства — они называются *аксиомами*. Кроме аксиом бывают также *схемы аксиом* — они отличаются от аксиом наличием метапеременных, и становятся утверждениями после подстановки конкретных формул на место метапеременных.

Обозначив сеттинг, разберём последовательно все связки и кванторы.

## Импликация

Импликация $P → Q$ (если $P$, то $Q$) означает, что из $P$ следует $Q$. Конкретный смысл этого высказывания мы обозначим следующим принципами.

Мы можем утверждать $P → Q$ если располагаем таким рассуждением, что оно, будучи соединено с доказательством $P$, автоматически бы давало доказательство $Q$. Двойственно, если мы располагаем доказательством $P → Q$, то тогда, если мы знаем что верно $P$, то можем утверждать и $Q$.

Чтобы построить требуемое для доказательства $P → Q$ рассуждение, нам нужен способ временно постулировать истинность $P$. Таким способом являются *гипотетические суждения*.

Гипотетическое суждение отличается от обычного утверждения наличием *контекста* — списка предположений по левую сторону от турникета. Например, утверждение, что в предположении $f(2) = 2$ и $f(3) = 6$ верно $f(2) + f(3) = 8$ записывается следующим образом:

$$(f(2) = 2), (f(3) = 6) \vdash f(2) + f(3) = 8$$

Эту запись можно читать следующим образом: «в предположении, что $f(2) = 2$ и $f(3) = 3$ я утверждаю, что $f(2) + f(3) = 8$».

Обозначая произвольный (возможно даже пустой) контекст как $Γ$, запишем следующие два правила вывода для предположений:

$$\cfrac{}{Γ,A \vdash A}\qquad \cfrac{Γ \vdash Z}{Γ,A \vdash Z}$$

Первое правило, называемое рефлексивностью, выражает то, что в предположении $A$ верно $A$. Это соответствует предназначению предположений: временно постулировать высказывание. При этом по левую сторону от $A$ может быть произвольный набор предположений. Это правило позволяет вводить и использовать предположения.

Второе правило, называемое монотонностью, выражает то, что верно без $A$ остаётся верным если предположить $A$. Это правило позволяет *не использовать* предположения.

Определив гипотетические суждения, сформулируем теперь правила для импликации:

$$\cfrac{Γ,A \vdash B}{Γ \vdash A → B} \qquad \cfrac{Γ \vdash A \qquad Γ\vdash A → B}{Γ \vdash B}$$

Эти правила называются, соответственно, введением и удалением импликации. Они соответствуют определяющим импликацию принципам (мы это наглядно покажем чуть позже).

Множеству предположений соответствует цепь импликаций:

$$\cfrac{P, Q \vdash R}{\cfrac{P \vdash Q → R}{\vdash P → (Q → R)}}$$

Подобную цепь можно читать следующим образом: если $P$, и если $Q$, то $R$. Мы полагаем, что импликация правоассоциативна, и записываем это высказывание без скобок как $P → Q → R$.

Определив все необходимые правила для импликации, рассмотрим пример. Докажем следующее высказывание: если из $P$ следует $Q$, и если из $Q$ следует $R$, то тогда из $P$ следует $R$.

Мы докажем его двумя способами: сначала записав доказательство как список предположений и утверждений, где каждое утверждение следует из предыдущих утверждений или предположений. Затем, мы разберём полный вывод требуемого утверждения с помощью правил.

Доказываемое высказывание записывается символьно как $(P → Q) → (Q → R) → P → R$. Запишем само доказательство:

1. Пусть $P → Q$
   1. Пусть $Q → R$
      1. Пусть $P$
         1. Тогда $Q$
         2. И затем $R$
      2. Следовательно, $P → R$
   2. Следовательно, $(Q → R) → P → R$
2. Следовательно, $(P → Q) → (Q → R) → P → R$

Уровень вложенности соответствует области действия предположений. Слово «пусть» вводит предположение и увеличивает отступ, когда же слово «следовательно» снимает предположение, уменьшает отступ и вводит импликацию.

Суждения, выводимые с помощью удаления импликации, просто пишутся друг за другом.

Теперь полностью выведем утверждения используя правила вывода. Сначала мы должны привести все предположения к одному контексту, сделаем это:

$$
\cfrac
  { (P → Q) \vdash P → Q}
  {\cfrac
    {(P → Q), (Q → R) \vdash P → Q}
    {(P → Q), (Q → R),P \vdash P → Q}}
\qquad
\cfrac
  {(P → Q), (Q → R) \vdash Q → R}
  {(P → Q), (Q → R),P \vdash Q → R}
$$

Затем дважды используем удаление импликации:

$$
\cfrac{(P → Q),(Q → R),P \vdash P \qquad (P → Q),(Q → R),P \vdash P → Q}
{(P → Q),(Q → R),P \vdash Q}
$$
$$
\cfrac{(P → Q),(Q → R),P \vdash Q \qquad (P → Q),(Q → R),P \vdash Q → R}
{(P → Q),(Q → R),P \vdash R}
$$

И, наконец, снимем предположения, последовательно вводя импликации:

$$
\cfrac
  {(P → Q),(Q → R),P \vdash R}
  {\cfrac
    {(P → Q),(Q → R) \vdash P → R}
    {\cfrac
      {(P → Q) \vdash (Q → R) → P → R}
      {\vdash (P → Q) → (Q → R) → P → R}}}
$$

Всё доказательство целиком можно записать как одно большое дерево вывода:

```{figure} /_img/imp-ex.svg
```

Даже для столь простого утверждения соответствующее ему дерево вывода весьма громоздко. Поэтому мы будем использовать доказательства в виде списка. Правила вывода при этом определяют то, какие последовательности утверждений допустимы.

Мы говорили, что смысл логических связок в математике отличается от смысла похожих высказываний в обычной жизни. Чтобы показать это наглядно, докажем, что для любых высказываний $P$ и $Q$ верно $P → Q → P$:

$$
\cfrac
  {P \vdash P}
  {\cfrac
    {P,Q \vdash P}
    {\cfrac
      {P \vdash Q → P}
      {\vdash P → Q → P}}}
$$

С одной стороны, это высказывание аналогично высказыванию «из $P$ следует $P$», но с неиспользованным предположением $Q$. Но с другой стороны оно означает следующее: пусть верно $P$. Тогда из $Q$ следует $P$.

Иначе говоря, высказывание $Q → P$ может быть истинным для логически никак не связанных высказываний $P$ и $Q$. Так, например, верно высказывание «если $1=1$, то $2+3 = 5$».

Это значительно отличается от обычного понятия следствия, где предположения и вывод логически связаны друг с другом. Высказывание вроде «если Лондон это столица Великобритании, то $3\cdot 3 = 9$» алогично в быту, но допустимо в том смысле, в котором мы используем импликацию в математике.

Мы говорили, что можем утверждать $P → Q$ в том случае, если располагаем рассуждением, которое в сочетании с доказательством $P$ даёт доказательство $Q$. Чтобы этот принцип выполнялся, нам нужен метод, превращающий последовательное введение и удаление импликации в прямое доказательство следствия.

Покажем этот метод на примере использования утверждения $P → Q → P$.

```{figure} /_img/imp-red.svg
```

Редукция импликации осуществляется в три шага:

1. Сначала подставляем доказательство $P$ во все места, где используется правило рефлексивности для $P$: в данном случае, на место $P \vdash P$
2. Затем стираем предположение $P$ в суждениях вида $Γ, P, Δ \vdash \cdots$.Так $P,Q \vdash P$ превращается в $Q \vdash P$
3. Наконец, стираем последовательные введение и удаление импликации

Таким образом, наши правила вывода действительно соответствуют определяющему импликацию принципу.

В высказывании $P → Q$ роли составляющих его высказываний $P$ и $Q$ существенно различны: тот, кто использует утверждение $P → Q$ должен предоставить доказательство $P$ чтобы получить доказательство $Q$. Двойственно, когда мы доказываем $P → Q$, мы рассуждаем так, будто обладаем доказательством $P$, и должны построить доказательство $Q$.

Обобщим эту идею на составные высказывания. Рассмотрим сначала высказывание $P → Q → R$. Тот, кто использует это утверждение, должен предоставить доказательство $P$ чтобы получить доказательство $Q → R$. Но затем, чтобы получить $R$, он должен предоставить доказательство $Q$. Двойственно, когда мы доказываем $P → Q → R$, мы предполагаем $P$ и $Q$ и должны доказать $R$.

Таким образом, в высказывании $P → Q → R$ высказывания $P$ и $Q$ имеют одну и ту же роль, отличающуюся от роли $R$.

Теперь рассмотрим высказывание $(P → Q) → R$. Тот, кто использует это утверждение, должен предоставить доказательство $P → Q$. Но при построение этого доказательства он предполагает $P$ и должен доказать $Q$. Когда же мы доказываем $(P → Q) → R$, мы предполагаем $P → Q$. Но чтобы воспользоваться этим предположением, мы должны предоставить доказательство $P$.

Таким образом, в случае $(P → Q) → R$ доказательства высказываний $P$ и $R$ строит доказывающий утверждение, когда же доказательство $Q$ строит тот, кто использует утверждение.

Обобщением этих рассуждений является понятие полярности. Полярность высказываний определяется рекурсивно:

1. Высказывание целиком имеет положительную полярность
2. Если $P → Q$ имеет положительную полярность, то полярность $P$ отрицательна, а полярность $Q$ — положительна
3. Если же $P → Q$ имеет отрицательную полярность, то тогда полярность $P$ положительна, а полярность $Q$ отрицательна

В качестве примера разберём полярность высказывания $(S → P) → (Q → R)$.

1. Высказывание  $(S → P) → (Q → R)$ целиком имеет положительную полярность
2. Высказывание $S → P$ имеет отрицательную полярность, когда же полярность высказывания $Q → R$ положительна
3. $S$ имеет положительную полярность когда же $P$ — отрицательную, $Q$ имеет отрицательную полярность, когда же $R$ — положительную.

Таким образом мы разобрали все полярности этого выражения.

## Квантор всеобщности

Из выражений, отношений и связок можно составлять не только высказывания, но и формулы вроде $x + 1 > 0$. Они отличаются от высказываний наличием свободных переменных в выражении. Подставляя в формулу различные значения можно получить различные высказывания, например $2+1 > 0$ или $-3+1 > 0$.

Формула со свободными переменными сама по себе не является высказыванием, так как непонятно, о каких значениях идёт речь. Но кроме непосредственно подстановки, возможные значения можно обозначить с помощью квантора.

Пусть $\phi$ это формула со свободной переменной $x$. Высказывание $∀x.\; \phi$ («для любого $x$ верно $\phi$») означает, что $\phi$ верно для любого значения на месте переменной $x$.

Мы можем утверждать $∀{\color{red}x}.\; \phi$ в том случае, когда располагаем рассуждением, с помощью которого можно доказать $\phi[{\color{red}x} := {\color{red}t}]$ для любого значения ${\color{red}t}$. Двойственно, если мы располагаем доказательством $∀{\color{red}x}.\; \phi$, то можем утверждать $\phi[{\color{red}x} := {\color{red}t}]$ для любого ${\color{red}t}$.

Чтобы построить доказательство $∀x.\; \phi$ нам нужен способ временно предположить, что $x$ это некоторое значение. Для этого мы расширяем понятие контекста: теперь это список как высказываний, так и переменных.

Например, утверждение, что $x+1 = 3$ в предположении, что $x$ это значение, равное двум, записывается следующим образом:

$$x, x=2 \vdash x + 1 = 3$$

Эту запись можно читать следующим образом: «в предположении, что $x$ — значение и $x = 2$, я утверждаю, что $x + 1 = 3$».

Для введения переменных в контекст нам потребуется новое правило вывода:

$$\cfrac{Γ \vdash P}{Γ,{\color{red}x} \vdash P}\;{\color{red}x}\mathrel\#Γ,P$$

Запись ${\color{red}x}\mathrel\#Γ,P$ означает, что переменная ${\color{red}x}$ не входит ни в контекст $Γ$, ни в высказывание $P$. Это важное ограничение: мы предполагаем произвольное значение, никак не связанное с другими.

Правила для предположений остаются теми же, но с учётом того, что высказывания могут использовать только те переменные, которые уже есть в контексте. Так, например, в контексте $Γ,A$ высказывание $A$ может содержать только те свободные переменные, которые уже есть в $Γ$. При этом если в контексте уже есть переменная, то во всех рассуждениях с этим контекстом мы воспринимаем эту переменную как полноценное значение.

Учитывая всё сказанное, запишем правила введения и удаления квантора всеобщности:

$$\cfrac{Γ,{\color{red}x} \vdash \phi}{Γ\vdash ∀{\color{red}x}.\;\phi}
\qquad
\cfrac{Γ \vdash ∀{\color{red}x}.\;\phi}{Γ \vdash \phi[{\color{red}x} := {\color{red}t}]}$$

Эти правила похожи на соответствующие правила для импликации.

Переменная $x$ в $∀x.\; \phi$ связывается точно также, как связываются переменные в лямбда выражении. И точно также мы считаем альфа-эквивалентные высказывания одним и тем же высказыванием.

Квантор захватывает всё, что справа него: например, $∀x.\; \phi → P$ это то же самое, что и $∀x.\; (\phi → P)$. Запись $∀x\,y.\; \phi$ означает высказывание $∀x.\;∀y.\; \phi$.

Рассмотрим теперь пример рассуждения, использующего импликацию и квантор всеобщности.

Предположим, что нам дано некоторое отношение $R$, про которое известно следующее:

1. Для любых трёх чисел $a$, $b$ и $c$, если $R(a, b)$, то $R(a, b+c)$
2. Для любых трёх чисел $a$, $b$ и $c$, если $R(a+c, b+c)$, то $R(a, b)$

Докажем следующее утверждение: для любых чисел $n$ и $k$, если $R(k,n)$, то и $R(0,n)$.

1. Пусть $n$ и $k$ — числа
   1. Пусть $R(k,n)$
      1. $R(k,n) → R(k, n+k)$ (первое свойство)
      2. Отсюда $R(k, n+k)$
      3. $k = 0+k$
      4. Отсюда $R(0+k, n+k)$
      5. $R(0+k, n+k) → R(0,n)$ (второе свойство)
      6. Отсюда $R(0,n)$
   2. Следовательно, $R(k,n) → R(0,n)$
2. Следовательно, $∀n\,k.\; R(k,n) → R(0,n)$

Рассмотрим вывод, соответствующий шагам этого доказательства.

Сначала нам нужно ввести свойства отношения $R$ в нужный контекст. Покажем как на примере первого свойства $R$ (второе свойство вводится аналогично):

$$
\cfrac
  {\vdash ∀a\,b\,c.\; R(a,b) → R(a, b+c)}
  {\cfrac
    {n \vdash ∀a\,b\,c.\; R(a,b) → R(a, b+c)}
    {\cfrac
      {n,k\vdash ∀a\,b\,c.\; R(a,b) → R(a, b+c)}
      {n,k,R(k,n)\vdash ∀a\,b\,c.\; R(a,b) → R(a, b+c)}}}
$$

В контексте с переменными $n$ и $k$ мы можем применить удаление квантора всеобщности:

$$
\cfrac
  {n,k,R(k,n)\vdash ∀a\,b\,c.\; R(a,b) → R(a, b+c)}
  {\cfrac
    {n,k,R(k,n)\vdash ∀b\,c.\; R(k,b) → R(k, b+c)}
    {\cfrac
      {n,k,R(k,n)\vdash ∀c.\; R(k,n) → R(k, n+c)}
      {n,k,R(k,n)\vdash R(k,n) → R(k, n+k)}}}
$$

Дальнейшие утверждения в доказательстве, кроме равенства и его использования, выводятся с помощью удаления импликации. Подробный разбор отношения равенства мы оставим на потом.

Вывод завершает последовательное введение импликации и квантора всеобщности:

$$
\cfrac
  {n,k,R(k,n)\vdash R(0,n)}
  {\cfrac
    {n,k \vdash R(k,n) → R(0,n)}
    {\cfrac
      {n\vdash ∀k.\; R(k,n) → R(0,n)}
      {\vdash ∀n\,k.\; R(k,n) → R(0,n)}}}
$$

Теперь рассмотрим как редуцировать последовательное введение и удаление квантора всеобщности, тем самым получив прямое доказательство для данного значения $t$.

Условно, редукцию можно описать следующим образом:

```{figure} /_img/all-red.svg
```

Последовательно же мы делаем следующее:

1. Всюду при предположении значения $x$ подставляем $t$ на место $x$ в выражения
2. Стираем $x$ из контекстов
3. Стираем введение и удаление квантора всеобщности

Таким образом правила для квантора всеобщности соответствуют определяющим его принципам.

Когда мы рассматривали импликацию, мы замечали, что различные части высказывания $P → Q$ имеют различные роли. Аналогичные рассуждения можно применить и к квантору всеобщности. Однако, в логике первого порядка высказывания не являются значениями, и поэтому положительная полярность значений может быть обусловлена только импликацией.

## Конъюнкция и дизъюнкция

Высказывание $P ∧ Q$ («$P$ и $Q$») означает, что верны оба высказывания, когда же высказывание $P ∨ Q$ («$P$ или $Q$») означает, что верно по крайней мере одно из них.

Мы можем утверждать высказывание $P ∧ Q$ в том случае, когда располагаем доказательствами как $P$, так и $Q$. Двойственно, если мы располагаем доказательством $P ∧ Q$, то можем утверждать любое из этих высказываний.

Высказывание $P ∨ Q$ же мы можем утверждать в том случае, когда располагаем либо доказательством $P$, либо доказательством $Q$. Принцип использования у $P ∨ Q$, однако, несколько сложнее, чем у $P ∧ Q$. Пусть мы располагаем двумя рассуждениями: одно доказывает некоторое высказывание $R$ в предположении $P$, другое же доказывает $R$ в предположении $Q$. Тогда, если мы располагаем доказательством $P ∨ Q$, то можем утверждать $R$.

Запишем теперь соответствующие правила введения и удаления. Сначала для конъюнкции:

$$
\cfrac{Γ \vdash P \qquad Γ \vdash Q}{Γ \vdash P ∧ Q}
\qquad
\cfrac{Γ \vdash P ∧ Q}{Γ \vdash P}
\qquad
\cfrac{Γ \vdash P ∧ Q}{Γ \vdash Q}
$$

Затем для дизъюнкции:

$$
\cfrac{Γ \vdash P}{Γ \vdash P ∨ Q}
\qquad
\cfrac{Γ \vdash Q}{Γ \vdash P ∨ Q}
\qquad
\cfrac{Γ \vdash P ∨ Q \qquad Γ,P \vdash R \qquad Γ,Q \vdash R}{Γ \vdash R}
$$

Конъюнкция и дизъюнкция связываются с высказываниями сильнее, чем импликация: например, $S → P ∧ Q$ означает $S → (P ∧ Q)$. Запись $P ∨ Q ∧ R$ означает $P ∨ (Q ∧ R)$, однако в подобных формулах принято использовать скобки.

Рассмотрим теперь пример доказательства с конъюнкцией и дизъюнкцией. Докажем следующее утверждение: если $P$ и $Q ∨ R$, то тогда $P ∧ Q$ или $P ∧ R$.

1. Пусть $P ∧ (Q ∨ R)$
   1. Тогда $P$
   2. И $Q ∨ R$
   3. Разберём $Q ∨ R$
      1. Пусть $Q$
         1. Тогда $P ∧ Q$
         2. И, следовательно, $(P ∧ Q) ∨ (P ∧ R)$
      2. Пусть $R$
         1. Тогда $P ∧ R$
         2. И, следовательно, $(P ∧ Q) ∨ (P ∧ R)$
2. Следовательно, $P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)$

В этом доказательстве используются все четыре правила:

1. С помощью удаления конъюнкции мы получаем $P$ и $Q ∨ R$ из $P ∧ (Q ∨ R)$
2. Введение конъюнкции позволяет получить $P ∧ Q$ из $P$ и $Q$
3. Введение дизъюнкции превращает $P ∧ Q$ в $(P ∧ Q) ∨ (P ∧ R)$
4. И, наконец, удаление дизъюнкции позволяет получить $(P ∧ Q) ∨ (P ∧ R)$ из соответствующих рассуждений для $P$ и для $R$

Как и для остальных связок, последовательное введение и удаление конъюнкции или дизъюнкции в доказательстве можно редуцировать.

В случае конъюнкции редукцию совсем просто выполнить:

```{figure} /_img/conj-red.svg
```

Для дизъюнкции она сложнее, но не сильно сложнее:

```{figure} /_img/disj-red.svg
```

Предположения стираются по тому же принципу что и при редукции импликации.

Ни конъюнкция, ни дизъюнкция не влияют на полярность выражений, из которых они состоят. Однако, с полярностью связана возможность выбора высказывания: когда мы доказываем $P ∧ Q$, мы должны предоставить оба доказательства, но когда используем $P ∧ Q$, то можем выбрать то, какое именно из утверждений нужно. Двойственно, когда мы доказываем $P ∨ Q$, то вольны выбрать любое из них для доказательства, но при использовании $P ∨ Q$ должны рассмотреть обе возможности.

Высказывание $P ↔ Q$ («$P$ равносильно $Q$») означает равносильность высказываний $P$ и $Q$. Оно определяется как конъюнкция импликаций:

$$(P ↔ Q) := (P → Q) ∧ (Q → P)$$

## Отрицание

Отрицание $¬P$ означает невозможность $P$ в сильном смысле этого слова: из $P$ следует абсурд. Это сокращённая запись высказывания $P → ⊥$.

Чтобы понять сущность абсурда, рассмотрим следующее рассуждение:

1. Пусть верно $P ∨ Q$
2. Пусть $P$ невозможно
3. Тогда верно $Q$

Знание того, что $P$ не может быть истинным позволяет отсечь ветвь дизъюнкции и получить $Q$.

Но наличие одновременно доказательств $P$ и $¬P$ позволяет таким образом вывести произвольное высказывание $Q$:

1. Мы знаем, что $P$
2. Следовательно, $P ∨ Q$ (введение дизъюнкции!)
3. Мы знаем, что $¬P$
4. Следовательно, $Q$

Отсюда, учитывая определение $¬P$, мы получаем, что *из абсурда следует что угодно*. Этот принцип выражается следующим правилом вывода:

$$\cfrac{Γ \vdash \bot}{Γ \vdash Q}$$

Ранее мы замечали, что если существует доказательство $Q$, то тогда высказывание $P → Q$ верно для любого высказывания $P$. Теперь же мы видим двойственное свойство: если существует доказательство $¬P$, то тогда высказывание $P → Q$ верно для любого $Q$.

Это свойство снова противоречит бытовому представлению о следствии, но вполне соответствует определяющему импликацию принципу: давать доказательство $Q$ при наличии доказательства $P$.

В непротиворечивой теории абсурд может быть доказан только при наличии дополнительных противоречивых предположений. И если предположение $P$ абсурдно, то любое изощрённое доказательство $P → Q$ оказывается бессодержательным, так как из $P$ следует вообще любое высказывание. Содержательным оказывается лишь доказательство $P → \bot$, так как оно явно показывает невозможность $P$.

Рассмотрим теперь пример доказательства с отрицанием. Докажем следующее утверждение: если $P → Q$ и $¬Q$, то тогда $¬P$.

1. Пусть $P → Q$ и пусть $¬Q$
   1. Пусть $P$
      1. Тогда $Q$
      2. Что абсурдно, так как $¬Q$
   2. Следовательно, $¬P$
2. Следовательно, $(P → Q) → ¬Q → ¬P$

## Квантор существования

Высказывание $∃x.\;\phi$ («существует такое $x$ что $\phi$») означает, что существует такое значение $t$ что верно $\phi[x:=t]$.

Мы можем утверждать $∃x.\;\phi$ в том случае, когда располагаем доказательством $\phi[x:=t]$ для некоторого значения $t$. Принцип использования квантора существования сложнее и похож на соответствующий принцип для импликации. Пусть мы располагаем рассуждением, которое, предполагая наличие значения $x$ удовлетворяющего свойству $\phi$, доказывает некоторое высказывание $P$. Тогда, если мы знаем, что $∃x.\;\phi$, то можем утверждать $P$.

Запишем правила введения и удаления, соответствующие этим принципам:

$$
\cfrac{Γ \vdash \phi[{\color{red}x} := {\color{red} t}]}{Γ \vdash ∃{\color{red}x}.\;\phi}
\qquad
\cfrac{Γ \vdash ∃{\color{red}x}.\; \phi \qquad Γ,{\color{red}x},\phi \vdash P}{Γ \vdash P}
$$

Особенности, касающиеся синтаксиса и захвата переменных, у квантора существования те же, что и у всеобщности: квантор захватывает всё, что справа и связывает соответствующую переменную. И как и раньше, мы считаем альфа-эквивалентные высказывания одним и тем же высказыванием.

Рассмотрим пример доказательства с использованием квантора существования. Докажем следующее: если не существует такого $x$, что $\phi$, то тогда для любого $x$ верно $¬\phi$.

1. Пусть $¬∃x.\;\phi$
   1. Пусть $x$ это некоторое значение
      1. Пусть $\phi$
         1. Тогда $∃x.\;\phi$
         2. Что абсурдно, так как $¬∃x.\;\phi$
      2. Следовательно, $¬\phi$
   2. Следовательно, $∀x.\; ¬\phi$
2. Следовательно, $(¬∃x.\;\phi) → ∀x.\; ¬\phi$

Кванторы всеобщности и существования можно совмещать в высказывании, причём его смысл зависит от их порядка. Рассмотрим влияние порядка кванторов на смысл высказываний на паре примеров.

Сначала докажем следующее высказывание: для любого $x$ существует такое $y$, что $x = y$.

1. Пусть $x$ — значение
   1. $x = x$
   2. Значит, $∃y.\; x = y$
2. Следовательно, $∀x.\;∃y.\; x = y$

В доказательстве этого высказывания мы сначала предположили наличие значения $x$ и затем выбрали значение $y$ в зависимости от значения $x$.

При другом порядке кванторов мы должны были бы сначала выбрать значение $x$, а уже затем показать, что соответствующее этому значению свойство выполняется для любого $y$. Чтобы показать это наглядно, докажем следующее высказывание: существует такое число $x$, что для любого $y$ верно $x \cdot y = x$.

1. $∀y.\; 0 \cdot y = 0$
2. Следовательно, $∃x.\; ∀y.\; x \cdot y = x$

Квантор существования двойственен квантору всеобщности в смысле полярности значения: если в случае $∀x.\;\phi$ мы предполагаем $x$ и должны доказать $\phi$, то в случае $∃x.\; \phi$ мы должны как найти подходящее значение, так и доказать соответствующее ему высказывание.

Двойственность можно заметить и в плане выбора значения: если при доказательстве $∀x.\; \phi$ мы ожидаем любое $x$, но при использовании $∀x.\; \phi$ вольны выбрать любое значение для подстановки, то в случае $∃x.\; \phi$ мы выбираем подходящее значение когда доказываем высказывание, когда же при использовании $∃x.\; \phi$ мы должны ожидать любое значение удовлетворяющее свойству $\phi$. Эта двойственность в выборе схожа с двойственностью $P ∧ Q$ и $P ∨ Q$.

Как и в случае с квантором всеобщности, доказательство с последовательным введением и удалением квантора существования можно редуцировать. Условно, редукцию можно описать так:

```{figure} /_img/ex-red.svg
```

Чтобы выполнить редукцию, нужно сначала преобразовать доказательство $Γ,x,\phi \vdash P$ в доказательство $Γ,\phi[x:=t] \vdash P$ действуя также, как и при редукции квантора всеобщности. Затем доказательство $Γ,\phi[x:=t] \vdash P$ преобразуется в доказательство $Γ \vdash P$ точно так же, как и при редукции импликации.

Квантор существования завершает список логических конструкций в логике первого порядка. Нам осталось лишь рассмотреть принцип, разделяющий конструктивную (интуиционистскую) и классическую логики.

## Принцип исключённого третьего

Для каждого высказывания $P$ принцип исключённого третьего утверждает $P ∨ ¬P$. На первый взгляд это совершенно очевидное утверждение: высказывание либо истинно, либо ложно, как же иначе? Но здесь также есть различие между математикой и обычной жизнью.

В математических теориях есть высказывания, которые невозможно ни доказать, ни опровергнуть. Самым известным (и, наверное, первым) примером такого высказывания является аксиома параллельности в нейтральной геометрии. Это высказывание недоказуемо в ней, и более того, добавив его или его отрицание к аксиомам, мы получаем различные геометрии: евклидову и гиперболическую, соответственно.

Другим примером является континуум-гипотеза в теории множеств — и как и в случае с геометрией, добавление этого высказывания или его отрицания к аксиомам приводит к различным новым теориям множеств.

Пусть $E$ это именно подобное высказывание. Как и для любого другого высказывания, принцип исключённого третьего утверждает, что

$$E ∨ ¬E$$

Это *довольно странное* утверждение: мы утверждаем, что по крайней мере одно из высказываний истинно, однако невозможно в принципе утверждать ни одно из них.

Но странности на этом не заканчиваются. Принцип исключённого третьего также позволяет вывести следующее утверждение:

$$∃n.\; (n = 0 ∧ E) ∨ (n = 1 ∧ ¬E)$$

Мы оказываемся в противоестественной ситуации: мы утверждаем «существует число!», однако в принципе невозможно назвать ни одно число, которое бы удовлетворяло требуемому свойству.

Есть два способа разрешить подобную ситуацию. Конструктивная (или интуиционистская) математика не признаёт принцип исключённого третьего, и в ней подобная проблема не возникает: каждому доказательству существования соответствует некоторое построенное значение, а каждой дизъюнкции — конкретное доказанное значение.

Классическая математика принимает принцип исключение третьего и никак не обосновывает его в понятиях самой логики. Вместо этого она сопоставляет логической теории различные её модели, в которых каждое высказывание имеет определённое логическое значение. При этом в одних моделях высказывание $E$ оказывается истинным, а в других — ложным. И во всех моделях соответствующие им значения $n$ существуют, хотя могут быть различны в различных моделях.

Таким образом, классическая логика это логика реальности — в реальности вещи либо имеют место, либо не имеют места быть, хотя мы можем не знать, что именно из этого истинно. Конструктивная логика же это логика фактов: мы утверждаем высказывание только тогда, когда мы можем установить факт его истинности. И не существует метода, показывающего истинность или ложность произвольного высказывания.

В этой книге мы будем использовать конструктивную логику везде, где это возможно, переключаясь на классическую логику там, где конструктивное доказательство невозможно или непрактично. Кроме эстетических, на это есть также и практические причины.

Различные объекты в математике образуют математические структуры, которые называются категориями, и у этих категорий может быть внутренняя логика. Эта логика, как правило, конструктивна. Доказательство снаружи может быть перенесено вовнутрь, тем самым превращаясь в доказательство утверждения про объекты этой категории. Но это возможно только в случае, когда доказательство совместимо со внутренней логикой категории, что в случае большинства интересных категорий означает конструктивность.

Хотя принцип исключённого третьего не выполняется в конструктивной логике, его отрицание в этой логике ложно:

1. Пусть $¬(P ∨ ¬P)$
   1. Пусть $P$
      1. Тогда $P ∨ ¬P$
      2. Что абсурдно, так как $¬(P ∨ ¬P)$
   2. Следовательно, $¬P$
   3. Тогда снова $P ∨ ¬P$
   4. Что абсурдно, так как $¬(P ∨ ¬P)$
2. Следовательно, $¬¬(P ∨ ¬P)$

Таким образом, название «принцип исключённого третьего» является вводящим в заблуждение: речь идёт не о каком-то третьем логическом значении, а о предположении какого-либо значения без явных свидетельств.

Эквивалентным принципу исключению третьего является закон двойного отрицания, который утверждает, что из $¬¬P$ следует $P$. Рассуждение выше фактически доказывает, что из закона двойного отрицания следует принцип исключённого третьего, доказательство в другую сторону же сводится с разбору дизъюнкции.

В конструктивной логике принцип исключённого третьего можно использовать при доказательстве отрицания. Покажем это, доказав следующее: если из $P ∨ ¬P$ следует $¬Q$, то тогда $¬Q$.

1. Пусть $P ∨ ¬P → ¬Q$
   1. Пусть $Q$
      1. Пусть $P$
         1. Тогда $P ∨ ¬P$
         2. И, следовательно, $¬Q$
         3. Что абсурдно, так как $Q$
      2. Следовательно, $¬P$
      3. И снова $P ∨ ¬P$
      4. И, следовательно, $¬Q$
      5. Что абсурдно, так как $Q$
   2. Следовательно, $¬Q$
2. Следовательно, $(P ∨ ¬P → ¬Q) → ¬Q$

Приведём теперь пример утверждения, выводимого только в классической логике. Докажем, что если из $P$ следует $Q$, то тогда $¬P$ или $Q$.

1. Пусть $P → Q$
   1. Разберём $P ∨ ¬P$
      1. Пусть $P$. Тогда $Q$ и, следовательно, $¬P ∨ Q$
      2. Пусть $¬P$. Тогда $¬P ∨ Q$
2. Следовательно, $(P → Q) → ¬P ∨ Q$

## Логика первого порядка

В заключение сформулируем логику первого порядка, правила для который мы всё это время рассматривали.

Синтаксис выражений и формул:

$$\begin{array}{rcll}
{\color{red}term} & ::= & {\color{red}var} & \text{(переменная)} \\
& | & {\color{red}const} & \text{(константа)} \\
& | & {\color{red}fun}\, (\,{\color{red}\overline{term}}\,) & \text{(функция)} \\
\\
{\color{red}prop} & ::= & {\color{red}pred}\,(\,{\color{red} \overline {term}}\,) & \text{(предикат)} \\
 & | & \bot & \text{(абсурд)}\\
 & | & {\color{red}prop} ∧ {\color{red} prop} & \text{(конъюнкция)} \\
 & | & {\color{red}prop} ∨ {\color{red} prop} & \text{(дизъюнкция)} \\
 & | & {\color{red}prop} → {\color{red} prop} & \text{(следствие)} \\
 & | & ∀\,{\color{red}var}\, .\; {\color{red} prop} & \text{(всеобщность)} \\
 & | & ∃\,{\color{red}var}\, .\; {\color{red} prop} & \text{(существование)}
\end{array}$$

${\color{red}pred}$, ${\color{red}fun}$ и ${\color{red}const}$ означают конечные наборы отношений, функциональных символов и констант. Этот набор у каждой теории свой. Например, теория множеств вводит только отношения $(=)$ и $(∈)$, когда же арифметика Пеано вводит отношение $(=)$, функциональный символ $S$ и константу $0$.

Логика определяется тем, какие высказывания в ней можно выражать, и тем, какие утверждения выводимы. Рассмотренный нами естественный вывод это одна из многих систем дедукции для логики первого порядка. Тем не менее, запишем ещё раз все правила вывода.

Предположения:

$$\cfrac{}{Γ,P \vdash P}\qquad \cfrac{Γ \vdash Q}{Γ,P \vdash Q}
\qquad
\cfrac{Γ \vdash Q}{Γ,{\color{red}x} \vdash Q}$$

Импликация:

$$\cfrac{Γ,P \vdash Q}{Γ \vdash P → Q}
  \qquad \cfrac{Γ \vdash P \qquad Γ\vdash P → Q}{Γ \vdash Q}$$

Конъюнкция:

$$\cfrac{Γ \vdash P \qquad Γ \vdash Q}{Γ \vdash P ∧ Q}
\qquad
\cfrac{Γ \vdash P ∧ Q}{Γ \vdash P}
\qquad
\cfrac{Γ \vdash P ∧ Q}{Γ \vdash Q}$$

Дизъюнкция:

$$\cfrac{Γ \vdash P}{Γ \vdash P ∨ Q}
\qquad
\cfrac{Γ \vdash Q}{Γ \vdash P ∨ Q}
\qquad
\cfrac{Γ \vdash P ∨ Q \qquad Γ,P \vdash R \qquad Γ,Q \vdash R}{Γ \vdash R}$$

Абсурд:

$$\cfrac{Γ \vdash \bot}{Γ \vdash Q}$$

Квантор всеобщности:

$$\cfrac{Γ,{\color{red}x} \vdash \phi}{Γ\vdash ∀{\color{red}x}.\;\phi}
\qquad
\cfrac{Γ \vdash ∀{\color{red}x}.\;\phi}{Γ \vdash \phi[{\color{red}x} := {\color{red}t}]}$$

Квантор существования:

$$\cfrac{Γ \vdash \phi[{\color{red}x} := {\color{red} t}]}{Γ \vdash ∃{\color{red}x}.\;\phi}
\qquad
\cfrac{Γ \vdash ∃{\color{red}x}.\; \phi \qquad Γ,{\color{red}x},\phi \vdash P}{Γ \vdash P}$$

Вместе с синтаксисом формул, правила вывода завершают описание логики первого порядка.
