-- Коментарий начинается с `--`
-- Lean это действительно интерактивный прувер, и в нем можно получить ответ,
-- просто введя команду в текстовый редактор

-- Команда `#check` позволяет проверить, что выражение корректно типизированно
#check ((λα β: Type => λx:α => λ_:β => x) : ∀α β: Type, α → β → α)
-- Lean во многих случаях может сам вывести тип, и нам не нужно его указыать
#check λ(α β: Type)(x:α)(_:β) => x

-- Другой способ выразить, что выражениие имеет определённый тип, это пример
-- Пример это определение без имени
example: ∀α β: Type, α → β → α := λ(α β: Type)(x:α)(_:β) => x
-- `∀α β: Type` и `λ(α β: Type)` дублируют друг друга. Но есть короткая запись:
example (α β: Type): α → β → α := λ(x:α)(_:β) => x
-- Или даже:
example (α β: Type)(x:α)(_:β): α := x

-- Можно ввести определение
def f1 (α β: Type)(x:α)(_:β): α := x
-- И использовать его:
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
-- Или лишь некоторые, по имени:
#check f2 (β := Nat) 3 5

-- Lean позволяет определить функцию сразу для всех вселенных:
example {α β: Sort u}(x:α)(_:β): α := x
-- И явное указание вселенной можно опустить
example (x:α)(_:β): α := x

-- Типы данных

#print Bool

-- inductive Bool : Type where
  -- /-- The boolean value `false`, not to be confused with the proposition `False`. -/
  -- | false : Bool
  -- /-- The boolean value `true`, not to be confused with the proposition `True`. -/
  -- | true : Bool
--
-- export Bool (false true)

#print false
#print true

def neg (b:Bool): Bool :=
  match b with
  | false => true
  | true  => false

#reduce neg false
#reduce neg true

example: Bool → Bool
| false => true    | true  => false

example: Bool → Bool → Bool
| false, false => false    | false, true  => true
| true,  false => true     | true,  true  => false

#print Nat

def pred: Nat → Nat
| Nat.zero   => 0
| Nat.succ n => n

#reduce pred (pred 5)

def add1 (n:Nat): Nat → Nat
| 0          => n
| Nat.succ k => add1 n.succ k

def add2 (n:Nat): Nat → Nat
| 0          => n
| Nat.succ k => (add2 n k).succ

-- def il: Nat → Nat
-- | 0 => 0
-- | Nat.succ n => il n.succ

#print add2
#print Nat.brecOn
#print Nat.rec

-- recursor Nat.rec.{u} : {motive : Nat → Sort u} →
  -- motive Nat.zero → ((n : Nat) → motive n → motive (Nat.succ n)) → (t : Nat) → motive t

def natRec {M: Nat → Sort u}(z: M Nat.zero)(f: ∀n:Nat, M n → M n.succ): (t: Nat) → M t
| Nat.zero   => z
| Nat.succ n => f n (natRec z f n)

#reduce (λn => Nat.rec (motive := λ_ => Nat) n (λ_ s => s.succ)) 2 3

#reduce (Nat.rec 2 (λ_ s => s.succ) : Nat → Nat) 3
#reduce (λ_ s => s.succ) 2 $ (Nat.rec 2 (λ_ s => s.succ) : Nat → Nat) 2
#reduce (λ_ s => s.succ) 2 $ (λ_ s => s.succ) 1 $ (Nat.rec 2 (λ_ s => s.succ) : Nat → Nat) 1
#reduce (λ_ s => s.succ) 2 $ (λ_ s => s.succ) 1 $ (λ_ s => s.succ) 0 $
  (Nat.rec 2 (λ_ s => s.succ) : Nat → Nat) 0
#reduce (λ_ s => s.succ) 2 $ (λ_ s => s.succ) 1 $ (λ_ s => s.succ) 0 $ 2

#print Bool.rec
#print Nat.casesOn

#print Prod

#reduce ( (Prod.mk 2 3).casesOn (λx y => (y,x)) : Nat×Nat )

-- structure Prod (α : Type u) (β : Type v) where
--   /-- The first projection out of a pair. if `p : α × β` then `p.1 : α`. -/
--   fst : α
--   /-- The second projection out of a pair. if `p : α × β` then `p.2 : β`. -/
--   snd : β

#reduce (2,3).fst
#reduce (2,3).snd

#reduce ( {snd := 3, fst := 2} : Nat×Nat )
#reduce ( ⟨2,3⟩ : Nat×Nat )

#print Sum

-- inductive Sum (α : Type u) (β : Type v) where
--   /-- Left injection into the sum type `α ⊕ β`. If `a : α` then `.inl a : α ⊕ β`. -/
--   | inl (val : α) : Sum α β
--   /-- Right injection into the sum type `α ⊕ β`. If `b : β` then `.inr b : α ⊕ β`. -/
--   | inr (val : β) : Sum α β

#reduce ( (Sum.inl 3).casesOn pred Nat.succ : Nat )
#reduce ( (Sum.inr 3).casesOn pred Nat.succ : Nat )

#print Empty

#check λe:Empty => e

#print Empty.rec

#check λe:Empty => (e.rec : Nat)

def BoolEq (a: Bool)(b: Bool): Prop :=
  a.rec (b.rec True False) (b.rec False True)

example: ∀b:Bool, BoolEq b b := Bool.rec ⟨⟩ ⟨⟩

example (P Q: Type)(pq: P ⊕ Q): Prop := pq.rec (λ_ => False) (λ_ => True)
-- example (P Q: Prop)(pq: P ∨ Q): Prop := pq.rec (λ_ => False) (λ_ => True)

#check Decidable.byContradiction
#check Bool.and_true
#check decidable_of_decidable_of_iff

instance {P Q: Prop}: [Decidable P] → [Decidable Q] → Decidable (P ∧ Q)
| isFalse np, _          => isFalse $ λpq => np pq.left
| _,          isFalse nq => isFalse $ λpq => nq pq.right
| isTrue p,   isTrue q   => isTrue  $ ⟨p,q⟩

instance {P Q: Prop}: [Decidable P] → [Decidable Q] → Decidable (P ∨ Q)
| isFalse np, isFalse nq => isFalse $ λpq => pq.elim np nq
| isTrue p,   _          => isTrue  $ Or.inl p
| _,          isTrue q   => isTrue  $ Or.inr q

theorem decide_and {P Q: Prop}[dp: Decidable P][dq:Decidable Q]
  : decide (P ∧ Q) = (decide P && decide Q) :=
by
  apply dite P <;> (intro; simp [*])

theorem decide_or {P Q: Prop}[dp: Decidable P][dq:Decidable Q]
  : decide (P ∨ Q) = (decide P || decide Q) :=
by
  apply dite P <;> (intro; simp [*])
