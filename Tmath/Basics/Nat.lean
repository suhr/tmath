set_option pp.proofs true

#print Or.rec
example {c: Prop} (h: Or a b) (left: a → c) (right: b → c): c :=
  Or.rec left right h

#print False.rec
example {C: Sort u} (h: False): C :=
  h.rec

#print Exists.rec
example {α: Sort u} {p: α → Prop} {b: Prop}
    (h₁: Exists (λx ↦ p x)) (h₂: ∀a: α, p a → b): b :=
  Exists.rec h₂ h₁

#check Iff
#check Iff.intro
#check Iff.mp
#check Iff.mpr

#check rfl
#check Eq.subst
#check Eq.symm
#check Eq.trans
#check congrArg

#check id
#check absurd

#check Function.comp

example (nq: ¬q)(h: p → q): ¬p :=
  nq ∘ h

example (np: ¬p): ¬(p ∧ q) :=
  np ∘ And.left

#check Not.elim

-- Натуральные числа это индуктивный тип

-- inductive Nat where
-- | zero: Nat
-- | succ (n: Nat): Nat
#check Nat

#print Nat.rec     -- Рекурсор
#print Nat.recOn   -- Также рекурсор
#print Nat.casesOn -- Разбор без рекурсии

example (n: Nat): Nat :=
  match n with
  | Nat.zero => 1
  | Nat.succ n => n

-- Сложение

#check Nat.add
example: Nat → Nat → Nat
| a, Nat.zero   => a
| a, Nat.succ b => Nat.succ (Nat.add a b)

noncomputable
example (n k: Nat): Nat :=
  k.recOn n (λ_ s ↦ Nat.succ s)

#eval 2 + 3
#reduce λn ↦ n + 3

example: 1 + 1 = 2 := rfl

theorem add_zero  (n: Nat):   n + 0 = n                  := rfl
theorem add_one   (n: Nat):   n + 1 = n.succ             := rfl
theorem add_succ  (n k: Nat): n + k.succ = (n + k).succ  := rfl

-- Индуктивное доказательство без тактик

theorem zero_add (n: Nat): 0 + n = n :=
  n.recOn
    (show 0 + 0 = 0 from rfl)
    (λn (h: 0 + n = n) ↦
      show 0 + n.succ = n.succ from
      congrArg Nat.succ h)

theorem zero_add_match: (n: Nat) → 0 + n = n
| 0 => show 0 + 0 = 0 from rfl
| Nat.succ n =>
  show 0 + n.succ = n.succ from
  congrArg Nat.succ (zero_add_match n)

example (n: Nat): 0 + n = n :=
  n.recOn
    rfl
    (λn (h: 0 + n = n) ↦
      calc
        0 + n.succ = (0 + n).succ := add_succ 0 n
        _          = n.succ       := h.symm ▸ (rfl : n.succ = n.succ))

-- Доказательство с тактиками

example (n: Nat): 0 + n = n := by
  refine n.recOn ?z ?s
  · show 0 + 0 = 0
    exact rfl
  · intro n (h: 0 + n = n)
    show 0 + n.succ = n.succ
    exact congrArg Nat.succ h

example (n: Nat): 0 + n = n := by
  refine n.recOn rfl (λn h ↦ ?_)
  rw [add_succ]
  rw [h]

example (n: Nat): 0 + n = n := by
  refine n.recOn rfl (λn h ↦ ?_)
  show (0 + n).succ = n.succ
  rw [h]

example (n: Nat): 0 + n = n :=
  n.recOn rfl (λn h ↦ by rw [add_succ, h])

-- Упражнения

theorem succ_add (n k: Nat): n.succ + k = (n + k).succ := by
  refine k.recOn rfl (λk h ↦ ?s)
  show n.succ + k.succ = (n + k.succ).succ
  rw [add_succ, h, add_succ]

theorem add_comm (n k: Nat): n + k = k + n :=
  n.recOn
    (by rw[zero_add, add_zero])
    (λn (h: n + k = k + n) ↦ by rw [add_succ, succ_add, h])

-- Ассоциативность сложения

theorem add_assoc (m n k: Nat): (m + n) + k = m + (n + k) := by
  refine k.recOn rfl (λk h ↦ ?_)
  calc
    (m + n) + k.succ = ((m + n) + k).succ := by rw [add_succ]
    _                = (m + (n + k)).succ := by rw [h]
    _                = m + (n + k).succ   := by rw [←add_succ]
    _                = m + (n + k.succ)   := by rw [←add_succ]

example (m n k: Nat): (m + n) + k = m + (n + k) := by
  refine k.recOn rfl (λk h ↦ ?s)
  calc
    (m + n) + k.succ = ((m + n) + k).succ := rfl
    _                = (m + (n + k)).succ := by rw [h]

-- Тактика simp

example {m n k: Nat}: (m + n) + k = m + (n + k) :=
  k.recOn rfl (λk h ↦ by simp only [add_succ, h])


-- ac_rfl

example (a b c d e: Nat): (((a + b) + c) + d) + e = (c + ((b + e) + a)) + d :=
  by ac_rfl

#print Nat.pred

theorem pred_zero: (0: Nat).pred = 0 := rfl
theorem pred_succ (n: Nat): n.succ.pred = n := rfl

theorem succ_cancel {n k: Nat}(e: n.succ = k.succ): n = k :=
  congrArg Nat.pred e

theorem add_right_cancel {m n k: Nat}: (m+k = n+k) → m = n :=
  k.recOn id (λ_ h ↦ λe ↦ h (succ_cancel e))

theorem add_left_cancel {m n k: Nat}: (k+m = k+n) → m = n :=
  add_comm m k ▸ add_comm k n ▸ add_right_cancel

theorem add_eq_zero_left {n k: Nat}: (n + k = 0) → n = 0 :=
  k.recOn id (λk h ↦ λ(e: n+k.succ = 0) ↦ h (congrArg Nat.pred e))

theorem add_eq_zero_right {n k: Nat}: (n + k = 0) → k = 0 :=
  add_comm k n ▸ add_eq_zero_left

theorem succ_ne_zero (n:Nat): n.succ ≠ 0 := Nat.noConfusion

theorem succ_ne_self (n:Nat): n.succ ≠ n :=
  n.recOn
    (succ_ne_zero 0)
    (λn (h: n.succ ≠ n) ↦ λ(e: n.succ.succ = n.succ) ↦ h (succ_cancel e))

-- Суммируя, тактики:
-- refine, exact, show, intro, rw, simp, suffices, ac_rfl

-- Сравнение

-- Индуктивное семейство типов

#print Nat.le

-- Nat.le.rec: ∀{n: Nat} {motive: ∀k: Nat, n ≤ a → Prop},
--   motive n Nat.le.refl →
--   (∀{k: Nat} (h: n ≤ k), motive k h → motive k.succ (Nat.le.step h)) →
--   ∀{k: Nat} (h: n ≤ k), motive k h
#print Nat.le.rec
#print Nat.le.recOn

-- Eq.rec.{u, v}: ∀{α: Sort v} {a: α} {motive: (b: α) → a = b → Sort u},
--   motive a (Eq.refl a) →
--   ∀{b: α} (t: a = b), motive b t
#print Eq.rec

#check Nat.lt

theorem le_refl (n: Nat): n ≤ n := Nat.le.refl
theorem le_succ (n: Nat): n ≤ n.succ := Nat.le.step (le_refl n)
theorem le_succ_of_le {n k: Nat}: n ≤ k → n ≤ k.succ := Nat.le.step

theorem le_trans {m n k: Nat}(mn: m ≤ n)(nk: n ≤ k): m ≤ k :=
  nk.recOn
    (show m ≤ n from mn)
    (λ{k} (_: n ≤ k) (h: m ≤ k) ↦
      show m ≤ k.succ from le_succ_of_le h)

example {m n k: Nat}(mn: m ≤ n)(nk: n ≤ k): m ≤ k :=
  calc
    m ≤ n := mn
    n ≤ k := nk

theorem le_of_succ_le {n k: Nat}(le: n.succ ≤ k): n ≤ k :=
  le.recOn
    (show n ≤ n.succ from le_succ n)
    (λ{k} (_: n.succ ≤ k) (h: n ≤ k) ↦
      show n ≤ k.succ from le_succ_of_le h)

theorem succ_le_succ {n m: Nat}(le: n ≤ m): n.succ ≤ m.succ :=
  le.recOn (le_refl n.succ) (λ{m} _ (h: n.succ ≤ m.succ) ↦ le_succ_of_le h)

theorem zero_le (n: Nat): 0 ≤ n :=
  n.recOn (le_refl 0) (λ_ h ↦ le_succ_of_le h)

theorem zero_lt_succ (n: Nat): 0 < n.succ :=
  succ_le_succ (zero_le n)


theorem pred_le (n: Nat): n.pred ≤ n :=
  match n with
  | Nat.zero   => le_refl 0
  | Nat.succ _ => le_succ _

theorem pred_lt {n: Nat}(pn: n ≠ 0): n.pred < n :=
  match n with
  | Nat.zero => absurd rfl pn
  | Nat.succ n => succ_le_succ (le_refl n)

theorem pred_le_of_le {n k: Nat}(le: n ≤ k): n.pred ≤ k :=
  le_trans (pred_le n) le

theorem pred_le_pred {n k: Nat}(le: n ≤ k): n.pred ≤ k.pred := by
  refine le.recOn (le_refl n.pred) ?_
  intro k _ (h: n.pred ≤ k.pred)
  calc
    n.pred ≤ k.pred := h
    _      ≤ k      := pred_le k

theorem le_of_succ_le_succ {n m: Nat}: n.succ ≤ m.succ → n ≤ m :=
  pred_le_pred


-- Доказательство найдено с помощью #reduce not_succ_le_zero
theorem not_one_le_zero: ¬1 ≤ 0 := by
  suffices any_zero: ∀k, 1 ≤ k → k = 0 → False from
    λh ↦ any_zero 0 h rfl
  exact λk ok ↦ ok.recOn
    (λ(h: 1 = 0) ↦ succ_ne_zero 0 h)
    (λ{k} _ _ (ksz: k.succ = 0) ↦ succ_ne_zero k ksz)

example: ∀k: Nat, 1 ≤ k → k = 0 → False :=
  λk ok ↦ @Nat.le.recOn _ (λk _ ↦ k = 0 → False) k ok
    (λ(h: 1 = 0) ↦ succ_ne_zero 0 h)
    (λ{k} _ _ (ksz: k.succ = 0) ↦ succ_ne_zero k ksz)


theorem not_succ_le_zero (n: Nat): ¬n.succ ≤ 0 :=
  n.recOn
    not_one_le_zero
    (λn (h: ¬n.succ ≤ 0) ↦ h ∘ pred_le_pred)

theorem not_succ_le_self (n: Nat): ¬n.succ ≤ n :=
  n.recOn
    not_one_le_zero
    (λ_ h ↦ h ∘ le_of_succ_le_succ)

theorem eq_zero_of_le_zero {n: Nat} (h: n ≤ 0): n = 0 :=
  match n with
  | Nat.zero => rfl
  | Nat.succ n => absurd h (not_succ_le_zero n)

theorem lt_irrefl (n: Nat): ¬n < n :=
  n.recOn (not_succ_le_zero 0) (λ_ h ↦ h ∘ le_of_succ_le_succ)

theorem pos_iff_ne_zero {n: Nat}: 0 < n ↔ n ≠ 0 :=
  ⟨λh: 0 < n ↦ λn0: n = 0 ↦ not_succ_le_zero 0 (n0 ▸ h),
  n.casesOn (λh: 0 ≠ 0 ↦ absurd rfl h) (λn _ ↦ zero_lt_succ n)⟩


theorem le_add (n k: Nat): n ≤ n + k :=
  k.recOn (le_refl n) (λk (h: n ≤ n + k) ↦ le_succ_of_le h)

theorem le_add_of_le {m n: Nat}(k: Nat)(le: m ≤ n): m ≤ n + k :=
  k.recOn le (λk (h: m ≤ n + k) ↦ le_succ_of_le h)

theorem add_le_add_left {n k: Nat}(l: n ≤ k): ∀p, n + p ≤ k + p := by
  refine l.recOn ?_ ?_
  · exact λp ↦ le_refl (n + p)
  · intro k _ (h: ∀p, n + p ≤ k + p) p
    show n + p ≤ k.succ + p
    exact (succ_add k p).symm ▸ le_succ_of_le (h p)

theorem le_of_add_le_add_left {m n k: Nat}: (h: m + n ≤ m + k) → n ≤ k := by
  refine m.recOn ?_ ?_
  · simp only [zero_add]
    exact id
  · intro m (ih: m + n ≤ m + k → n ≤ k) (h: m.succ + n ≤ m.succ + k)
    suffices le: (m + n).succ ≤ (m + k).succ from ih (le_of_succ_le_succ le)
    exact succ_add m n ▸ succ_add m k ▸ h

theorem not_add_le_self (n: Nat){k: Nat}(pk: 0 < k): ¬(n + k ≤ n) := by
  refine pk.recOn ?_ ?_
  · exact not_succ_le_self n
  · intro k _ (h: ¬n + k ≤ n)
    exact h ∘ le_of_succ_le


#check Nat.exists_eq_add_of_le
theorem exists_of_le {n k: Nat}(le: n ≤ k): ∃p, n + p = k :=
  le.recOn
    ⟨0, rfl⟩
    (λ_ ⟨p,h⟩ ↦ ⟨p.succ, congrArg Nat.succ h⟩)

theorem le_of_exists {n k: Nat}: (ex: ∃d, n + d = k) → n ≤ k := by
  refine k.recOn ?_ ?_
  · intro ex
    show n ≤ 0
    let ⟨d, (hd: n + d = 0)⟩ := ex
    suffices nz: n = 0 from nz ▸ le_refl n
    exact add_eq_zero_left hd
  · intro k _ ex
    show n ≤ k.succ
    let ⟨d, (hd: n + d = k.succ)⟩ := ex
    suffices h: n ≤ n + d from hd ▸ h
    exact le_add n d


theorem le_antisymm {n k: Nat}(nk: n ≤ k): (kn: k ≤ n) → n = k :=
  nk.recOn
    (λ_ ↦ rfl)
    (λ{k} (nk: n ≤ k) _ (ksn: k.succ ≤ n) ↦
      absurd (le_trans ksn nk) (not_succ_le_self k))

theorem eq_or_lt_of_le {n m: Nat}(nm: n ≤ m): (n = m) ∨ (n < m) := by
  suffices h: ∀m, n ≤ m → (n = m) ∨ (n < m) from h m nm
  refine n.recOn ?_ ?_
  · intro m (zm: Nat.zero ≤ m)
    show 0 = m ∨ 0 < m
    exact match m with
    | Nat.zero => Or.inl rfl
    | Nat.succ m => Or.inr (zero_lt_succ m)
  · intro n (ih: ∀m, n ≤ m → n = m ∨ n < m) m (nm: n.succ ≤ m)
    show n.succ = m ∨ n.succ < m
    exact match m with
    | Nat.zero => absurd nm (not_succ_le_zero n)
    | Nat.succ m =>
      match ih m (le_of_succ_le_succ nm) with
      | Or.inl h => Or.inl (h ▸ rfl)
      | Or.inr h => Or.inr (succ_le_succ h)

theorem lt_or_ge (n k: Nat): n < k ∨ k ≤ n :=
  suffices h: ∀n, n < k ∨ k ≤ n from h n
  k.recOn
    (λn ↦ Or.inr (zero_le n))
    (λk (ih: ∀n, n < k ∨ k ≤ n) n ↦
      show n < k.succ ∨ k.succ ≤ n from
      match n with
      | Nat.zero => Or.inl (zero_lt_succ k)
      | Nat.succ n =>
        match ih n with
        | Or.inl h => Or.inl (succ_le_succ h)
        | Or.inr h => Or.inr (succ_le_succ h))

theorem not_le_of_gt {n k: Nat}(h: n > k): ¬n ≤ k := by
  refine h.recOn ?_ ?_
  · exact not_succ_le_self k
  · intro n (kn: k.succ ≤ n) _
    exact λh: n.succ ≤ k ↦
      not_succ_le_self k (le_trans (le_succ_of_le kn) h)

theorem not_lt_of_ge {n k: Nat}(h: k ≥ n): ¬(k < n) :=
  λlt ↦ not_le_of_gt lt h

-- `<` разрешимо

#check LE.le
#synth LE Nat    -- instLENat
#print instLENat

#check HAdd
#synth HAdd Nat Nat Nat    -- instHAdd
#check instHAdd

#synth Add Nat    -- instAddNat
#check instAddNat

#check HAdd.hAdd 2 3

#check Decidable

#synth Decidable (2 ≤ 3)    -- Nat.decLe

def decLe: (n m: Nat) → Decidable (n ≤ m)
| Nat.zero, Nat.zero     => Decidable.isTrue (le_refl 0)
| Nat.zero, m            => Decidable.isTrue (zero_le m)
| Nat.succ n, Nat.zero   => Decidable.isFalse (not_succ_le_zero n)
| Nat.succ n, Nat.succ m =>
  match decLe n m with
  | Decidable.isTrue h  => Decidable.isTrue (succ_le_succ h)
  | Decidable.isFalse h => Decidable.isFalse (h ∘ le_of_succ_le_succ)

#check decide

#check decide_eq_false
example [inst : Decidable p]: ¬p → (decide p) = false :=
  inst.recOn (λ_ _ ↦ rfl) (λhp hnp ↦ absurd hp hnp)

#check decide_eq_true
example [inst : Decidable p]: p → (decide p) = true :=
  inst.recOn (λhnp hp ↦ absurd hp hnp) (λ_ _ ↦ rfl)

#check of_decide_eq_true
example [inst: Decidable p](eq: (decide p) = true): p :=
  match (generalizing := false) inst with
  | isTrue h => h
  | isFalse h => absurd eq (ne_true_of_eq_false (decide_eq_false h))

example: 0 ≤ 2 := of_decide_eq_true rfl
example: 0 ≤ 2 := by decide

#check ite

example (n k: Nat): Bool :=
  if n ≤ k then
    true
  else
    false

#check dite

example [Decidable p]: p ∨ ¬p :=
  if h: p then Or.inl h
  else Or.inr h

#check if_pos
#check if_neg

#check dif_pos
#check dif_neg

#check propext

#check True

-- Вычитание

#check Nat.sub

#reduce 3 - 2    -- 1
#reduce 2 - 3    -- 0

theorem sub_zero (n: Nat): n - 0 = n := rfl
theorem sub_succ (n k: Nat): n - k.succ = (n - k).pred := rfl

theorem zero_sub (n: Nat): 0 - n = 0 :=
  n.recOn rfl (λ_ ih ↦ congrArg Nat.pred ih)

theorem succ_sub_succ (n m: Nat): n.succ - m.succ = n - m :=
  m.recOn rfl (λm h ↦
    calc
      n.succ - m.succ.succ = (n.succ - m.succ).pred := rfl
      _                    = (n - m).pred           := by rw [h])

theorem sub_self (n: Nat): n - n = 0 :=
  n.recOn rfl (λn h ↦
    calc
      n.succ - n.succ = n - n := succ_sub_succ _ _
      _               = 0     := h)

theorem sub_eq_zero_of_le {n k: Nat}(h: n ≤ k): n - k = 0 :=
  h.recOn
    (sub_self n)
    (λ{k} _ (h: n - k = 0) ↦ by rw [sub_succ, h, pred_zero])

theorem sub_le (n m: Nat): n - m ≤ n := by
  refine m.recOn (le_refl n) ?_
  intro m (h: n - m ≤ n)
  calc
    n - m.succ = (n - m).pred := rfl
    _          ≤ n - m        := pred_le _
    _          ≤ n            := h

theorem sub_lt {n m: Nat}(pn: 0 < n)(pm: 0 < m): n - m < n :=
  match n, m with
  | Nat.zero, _ => absurd pn (lt_irrefl 0)
  | _, Nat.zero => absurd pm (lt_irrefl 0)
  | Nat.succ n, Nat.succ m =>
    calc
      n.succ - m.succ = n - m  := by rw [succ_sub_succ]
      _               < n.succ := succ_le_succ (sub_le n m)

theorem sub_le_sub_left {n m: Nat}(h: n ≤ m)(k: Nat): k - m ≤ k - n :=
  h.recOn
    (le_refl (k - n))
    (λ{m} _ (h: k - m ≤ k - n) ↦ pred_le_of_le h)

theorem sub_le_sub_right {n m: Nat} (le: n ≤ m) (k: Nat): n - k ≤ m - k :=
  suffices h: ∀k, n ≤ m → n - k ≤ m - k from h k le
  λk ↦ k.recOn
    (λle ↦ le)
    (λk (h: n ≤ m → n - k ≤ m - k) (le: n ≤ m) ↦ pred_le_pred (h le))


theorem sub_sub (n m k: Nat): n - m - k = n - (m + k) := by
  refine k.recOn rfl ?_
  intro k (h: n - m - k = n - (m + k))
  calc
    n - m - k.succ = (n - m - k).pred   := rfl
    _              = (n - (m + k)).pred := by rw[h]
    _              = n - (m + k.succ)   := rfl

theorem add_sub_cancel (n m: Nat): n + m - m = n :=
  m.recOn rfl (λm h ↦
    calc
      n + m.succ - m.succ = (n + m).succ - m.succ := rfl
      _                   = n + m - m             := by rw [succ_sub_succ]
      _                   = n                     := by rw [h])

theorem succ_sub {n k: Nat}(h: k ≤ n): n.succ - k = (n - k).succ := by
  let ⟨d, hd⟩ := exists_of_le h
  rw [←hd]
  calc
    (k + d).succ - k = k + d.succ - k   := rfl
    _                = d.succ + k - k   := by rw [add_comm]
    _                = d.succ           := by rw [add_sub_cancel]
    _                = (d + k - k).succ := by rw [add_sub_cancel]
    _                = (k + d - k).succ := by rw [add_comm]

theorem sub_add_comm {n m k: Nat}(h: k ≤ n): n + m - k = n - k + m := by
  refine h.recOn ?_ ?_
  · show k + m - k = k - k + m
    simp only [add_comm, add_sub_cancel, sub_self, add_zero]
  · intro n (le: k ≤ n) (h: n + m - k = n - k + m)
    have k_le_nm: k ≤ n + m := le_add_of_le m le
    calc
      n.succ + m - k = (n + m - k).succ := by rw [succ_add, succ_sub k_le_nm]
      _              = (n - k + m).succ := by rw [h]
      _              = n.succ - k + m   := by rw [←succ_add, succ_sub le]

theorem sub_add_cancel {n k: Nat} (h: k ≤ n): n - k + k = n := by
  have: n + k - k = _ := sub_add_comm h
  rw [←this, add_sub_cancel]

theorem add_sub_assoc {m k: Nat} (h: k ≤ m) (n: Nat): n + m - k = n + (m - k) := by
  let ⟨d, hd⟩ := exists_of_le h
  rw [←hd]
  calc
    n + (k + d) - k = n + d + k - k   := by ac_rfl
    _               = n + d           := add_sub_cancel (n + d) k
    _               = n + (d + k - k) := by rw [add_sub_cancel]
    _               = n + (k + d - k) := by rw [add_comm k d]


-- Умножение

#check Nat.mul
example: Nat → Nat → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)

theorem mul_zero (n: Nat):   n * 0 = 0               := rfl
theorem mul_succ (n k: Nat): n * k.succ = n * k + n  := rfl

-- Упражнения

theorem mul_one (n: Nat):    n * 1 = n :=
  by rw [mul_succ, add_comm, mul_zero, add_zero]

theorem zero_mul (n: Nat): 0 * n = 0 := by
  refine n.recOn rfl (λn (h: 0 * n = 0) ↦ ?_)
  calc
    0 * n.succ = 0 * n + 0 := rfl
    _          = 0         := by rw [h]

theorem succ_mul (n k: Nat): n.succ * k = n * k + k := by
  refine k.recOn rfl (λk h ↦ ?_)
  calc
    n.succ * k.succ = n.succ * k + n.succ  := by rw [mul_succ]
    _               = n * k + k + (n + 1)  := by rw [h]
    _               = n * k + n + (k + 1)  := by simp only [add_assoc, add_comm k]
    _               = n * k.succ + k.succ  := by simp only [mul_succ]

theorem one_mul (n:Nat): 1*n = n := by
  rw [succ_mul, zero_mul, zero_add]

theorem mul_comm (n k: Nat): n * k = k * n :=
  k.recOn
    (show n * 0 = 0 * n by            rw [mul_zero, zero_mul])
    (λk (h: n * k = k * n) ↦
      show n * k.succ = k.succ * n by rw [mul_succ, h, ←succ_mul])

theorem mul_left_distr (n k p: Nat): n * (k + p) = n * k + n * p := by
  refine p.recOn rfl (λp h ↦ ?_)
  show n * (k + p.succ) = n * k + n * p.succ
  simp only [add_succ, mul_succ, h, add_assoc]

theorem mul_right_distr (n k p: Nat): (n + k) * p = n * p + k * p :=
by simp only [mul_comm, mul_left_distr]

theorem mul_assoc (m n k: Nat): (m * n) * k = m * (n * k) := by
  refine k.recOn rfl (λk h ↦ ?_)
  show m * n * k.succ = m * (n * k.succ)
  simp only [mul_succ, h, ←mul_left_distr]

example {a b c d e: Nat}: (((a * b) * c) * d) * e = (c * ((b * e) * a)) * d :=
by ac_rfl

theorem mul_eq_zero {n k: Nat}: (n * k = 0) → n = 0 ∨ k = 0 :=
  match k with
  | 0 => λ_ ↦ Or.inr rfl
  | Nat.succ k => λ(e: n*k + n = 0) ↦ Or.inl (add_eq_zero_right e)


-- Сложная теорема и тактика `suffices`.

theorem mul_left_cancel {m n k: Nat}(pm: m ≠ 0): (m * n = m * k) → n = k := by
  suffices h: ∀n, (m * n = m * k) → n = k from h n
  refine k.recOn ?_ ?_
  · intro n (nk: m * n = 0)
    exact (mul_eq_zero nk).elim (λz: m = 0 ↦ absurd z pm) id
  · intro k (h: ∀n, m * n = m * k → n = k) n
    show (m * n = m * k.succ) → n = k.succ
    exact match n with
    | Nat.zero => λ(e: 0 = m * k + m) ↦
      absurd (add_eq_zero_right e.symm) pm
    | Nat.succ n => λ(e: m * n.succ = m * k.succ) ↦
      congrArg Nat.succ (h n (add_right_cancel e))

theorem pos_of_mul_pos_left {n k: Nat}(h: 0 < n * k): 0 < k :=
  match n with
  | Nat.zero => absurd (zero_mul k ▸ h) (lt_irrefl 0)
  | Nat.succ n =>
    pos_iff_ne_zero.mpr (λhh ↦ (mul_zero n.succ ▸ hh ▸ pos_iff_ne_zero.mp h) rfl)

theorem mul_le_mul_left {n k: Nat}(m: Nat)(h: n ≤ k): m * n ≤ m * k := by
  refine h.recOn (le_refl (m * n)) ?_
  intro k _ ih
  calc
    m * n ≤ m * k + m  := le_add_of_le _ ih
    _     = m * k.succ := by rw [mul_succ]

theorem le_of_mul_le_mul_left {m n k: Nat}(pk: 0 < m): (m * n ≤ m * k) → n ≤ k :=
  match lt_or_ge k n with
  | Or.inr h => λ_ ↦ h
  | Or.inl (nm: k < n) => λ(h: m * n ≤ m * k) ↦ by
    refine absurd h (nm.recOn ?_ ?_)
    · show ¬m * k.succ ≤ m * k
      rw [mul_succ]
      exact not_add_le_self (m*k) pk
    · intro n _ (ih: ¬m * n ≤ m * k) (h: m * n.succ ≤ m * k)
      have := calc
        m * n ≤ m * n + m  := le_add (m*n) m
        _     = m * n.succ := by rw [mul_succ]
        _     ≤ m * k      := h
      exact ih this

theorem mul_sub_left_distrib (m n k: Nat): m * (n - k) = m * n - m * k :=
  if h: n ≥ k then
    m.recOn
      (by rw [zero_mul, zero_mul, zero_mul])
      (λm ih ↦ calc
        m.succ * (n - k) = m * n - m * k + n - k   := by
          rw [succ_mul, ih, ←add_sub_assoc h]
        _                = m.succ * n - m.succ * k := by
          rw [←sub_add_comm (mul_le_mul_left _ h), sub_sub, ←succ_mul, ←succ_mul])
  else by
    have nk: n ≤ k := pred_le_of_le ((lt_or_ge _ _).elim id h.elim)
    have: m * n ≤ m * k := mul_le_mul_left m nk
    rw [sub_eq_zero_of_le nk, sub_eq_zero_of_le this, mul_zero]


-- Сильная индукция

#check Nat.strongInductionOn
#print Nat.strongInductionOn

#print Nat.div
#check measure

def Nat.succRel (n k: Nat) := n.succ = k

def Ind.{u} (r: α → α → Prop) :=
  ∀{M: α → Sort u}, (∀x, (∀y, r y x → M y) → M x) → ∀x, M x

def indSuccRel: Ind Nat.succRel :=
  λ{M} (ind: ∀x, (∀y: Nat, y.succRel x → M y) → M x) ↦ by
    refine Nat.rec ?z (λn (h: M n) ↦ ?_)
    · show M 0
      exact ind 0 (λn s ↦ absurd s (succ_ne_zero n))
    · suffices hk: ∀k, k.succRel n.succ → M k from ind n.succ hk
      intro k s
      have: k = n := congrArg Nat.pred s
      exact this ▸ h

-- inductive Acc {α: Sort u}(r: α → α → Prop): α → Prop where
-- | intro (x: α)(h: (y: α) → r y x → Acc r y): Acc r x
#print Acc

#print Acc.rec
#check Acc.recOn

def wf_of_ind {r: α → α → Prop}(ind: Ind.{0} r): ∀x, Acc r x :=
  ind Acc.intro

noncomputable def ind_of_wf {r: α → α → Prop}(wf: ∀x, Acc r x): Ind r :=
  λ{M} (h: ∀x, (∀y, r y x → M y) → M x) x ↦
    show M x from (wf x).recOn (λx _ (wh: ∀y, r y x → M y) ↦ h x wh)

theorem acc_succ_rel: ∀n, Acc Nat.succRel n :=
  wf_of_ind indSuccRel

#reduce acc_succ_rel 3

#check Acc.inv
example {x y: α}(ax: Acc r x): r y x → Acc r y :=
  ax.recOn (λx (f: ∀y, r y x → Acc r y) _ ↦ f y)

def lt_wf (n: Nat): Acc Nat.lt n := by
  refine n.recOn (Acc.intro 0 ?_) ?_
  · intro y (h: y < 0)
    exact absurd h (not_succ_le_zero y)
  · intro n (an: Acc Nat.lt n)
    suffices ih: ∀m, m < n.succ → Acc Nat.lt m from Acc.intro n.succ ih
    intro m h
    have elt: m = n ∨ m < n := eq_or_lt_of_le (le_of_succ_le_succ h)
    exact elt.elim
      (λ(e: m = n) ↦ e.symm ▸ an)
      (λ(l: m < n) ↦ Acc.inv an l)

def modTwoStep (n: Nat) (f: ∀k: Nat, k < n → Nat): Nat :=
  if h: n ≥ 2 then
    have: n - 2 + 1 ≤ n := sub_add_comm h ▸ sub_le n 1
    f (n - 2) this
  else n

noncomputable
def modTwoFix: Nat → Nat :=
  ind_of_wf lt_wf modTwoStep

#reduce modTwoFix 3

-- InvImage

-- def InvImage {α: Sort u} {β: Sort v} (r: β → β → Prop) (f: α → β): α → α → Prop :=
--   fun a₁ a₂ => r (f a₁) (f a₂)
#check InvImage
#check InvImage.wf
#check invImage

def acc_invImage {x: α}(f: α → β)(acc: Acc r (f x)): Acc (InvImage r f) x := by
  suffices h: ∀y, Acc r y → ∀w, f w = y → Acc (InvImage r f) w
    from h (f x) acc x rfl
  refine λy (a: Acc r y) ↦ a.recOn ?_
  intro z _ (h: ∀y, r y z → ∀t, f t = y → Acc (InvImage r f) t)
  show ∀w, f w = z → Acc (InvImage r f) w
  intro w e
  suffices h: ∀t, r (f t) (f w) → Acc (InvImage r f) t
    from Acc.intro _ h
  exact λt ht ↦ h _ (e ▸ ht) t rfl

def wf_invImage (wf: ∀y: β, Acc r y)(f: α → β): ∀x: α, Acc (InvImage r f) x :=
  λx ↦ acc_invImage f (wf (f x))

def wf_measure: (f: α → Nat) → ∀x: α, Acc (InvImage Nat.lt f) x :=
  wf_invImage lt_wf

noncomputable example (m: α → Nat)(step: ∀x: α, (∀y: α, m y < m x → α) → α): α → α :=
  ind_of_wf (wf_measure m) step

-- @[reducible] def measure.{u}: {α: Sort u} → (α → Nat) → WellFoundedRelation α :=
-- fun {α} f => invImage f Nat.lt_wfRel
#print measure

-- Пример простой нетривиально рекурсивной функции

def modTwo (n: Nat): Nat :=
  if h: n ≥ 2 then modTwo (n - 2)
  else n
termination_by n
decreasing_by
  simp_wf
  show n - 2 + 1 ≤ n
  exact sub_add_comm h ▸ sub_le n 1

def inf_desc {r: α → α → Prop}(arx: Acc r x){p: α → Prop}
    (h: ∀x, p x → ∃y, r y x ∧ p y): p x → False :=
  arx.recOn (λx _ (ih: ∀y, r y x → p y → False) px ↦
    let ⟨y, ⟨ryx, py⟩⟩ := h x px
    ih y ryx py)


-- Деление

def div_rec_lemma {n k: Nat}: (0 < k ∧ k ≤ n) → n - k < n :=
  λ⟨(pk: 0 < k), (kn: k ≤ n)⟩ ↦ sub_lt (le_trans pk kn) pk

#check Nat.div
#check Nat.mod

theorem div_eq (n k: Nat): n / k = if 0 < k ∧ k ≤ n then (n - k) / k + 1 else 0 :=
  Nat.div_eq n k

theorem mod_eq (n k: Nat): n % k = if 0 < k ∧ k ≤ n then (n - k) % k else n :=
  Nat.mod_eq n k


theorem div_eq_if_pos {n k: Nat}(h: 0 < k ∧ k ≤ n): n / k = (n - k) / k + 1 :=
  by rw [div_eq, if_pos h]

theorem div_eq_if_neg {n k: Nat}(h: ¬(0 < k ∧ k ≤ n)): n / k = 0 :=
  by rw [div_eq, if_neg h]

theorem mod_eq_if_pos {n k: Nat}(h: 0 < k ∧ k ≤ n): n % k = (n - k) % k :=
  by rw [mod_eq, if_pos h]

theorem mod_eq_if_neg {n k: Nat}(h: ¬(0 < k ∧ k ≤ n)): n % k = n :=
  by rw [mod_eq, if_neg h]


theorem mod_zero (n: Nat): n % 0 = n := by
  have: ¬(0 < 0 ∧ 0 ≤ n) := lt_irrefl 0 ∘ And.left
  rw [mod_eq_if_neg this]

theorem mod_eq_of_lt {n k: Nat}(h: n < k): n % k = n := by
  have: ¬(0 < k ∧ k ≤ n) := not_le_of_gt h ∘ And.right
  rw [mod_eq_if_neg this]

theorem mod_eq_sub_mod {n k: Nat}(h: n ≥ k): n % k = (n - k) % k := by
  match k with
  | Nat.zero => rw [mod_zero, mod_zero, sub_zero]
  | Nat.succ k =>
    have: 0 < k.succ ∧ k.succ ≤ n := ⟨zero_lt_succ k, h⟩
    rw [mod_eq_if_pos this]

theorem mod_one (n: Nat): n % 1 = 0 := by
  refine n.recOn rfl ?_
  intro n (ih: n % 1 = 0)
  have: (0 < 1) ∧ 1 ≤ n.succ := ⟨by decide, zero_lt_succ n⟩
  calc
    n.succ % 1 = (n.succ - 1) % 1 := by rw [mod_eq_if_pos this]
    _          = (n - 0) % 1      := by rw [succ_sub_succ]
    _          = 0                := ih

theorem zero_mod (n: Nat): 0 % n = 0 :=
  match n with
  | Nat.zero => rfl
  | Nat.succ n => mod_eq_of_lt (zero_lt_succ n)


theorem zero_div (n: Nat): 0 / n = 0 := by
  match n with
  | Nat.zero => rfl
  | Nat.succ n =>
    have: ¬(0 < n.succ ∧ n.succ ≤ 0) := not_succ_le_zero n ∘ And.right
    rw [div_eq_if_neg this]

theorem div_one (n: Nat): n / 1 = n := by
  refine n.recOn (zero_div 1) ?_
  intro n (h: n / 1 = n)
  have: 0 < 1 ∧ 1 ≤ n.succ := ⟨by decide, succ_le_succ (zero_le n)⟩
  calc
    n.succ / 1 = (n.succ - 1) / 1 + 1 := by rw [div_eq_if_pos this]
    _          = (n / 1).succ         := rfl
    _          = n.succ               := by rw [h]


def divmod_ind.{u}
    {motive: Nat → Nat → Sort u}
    (base: ∀n k, ¬(0 < k ∧ k ≤ n) → motive n k)
    (ind: ∀n k, 0 < k ∧ k ≤ n → motive (n - k) k → motive n k)
    (n k: Nat): motive n k :=
  if h: 0 < k ∧ k ≤ n then
    ind n k h (divmod_ind base ind (n - k) k)
  else
    base n k h
termination_by n
decreasing_by exact div_rec_lemma h

theorem mod_add_div (n k: Nat): n % k + k * (n / k) = n := by
  refine divmod_ind (motive := λn k ↦ n % k + k * (n / k) = n) ?_ ?_ n k
  · intro n k (h: ¬(0 < k ∧ k ≤ n))
    calc
      n % k + k * (n / k) = n + k * 0 := by rw [div_eq_if_neg h, mod_eq_if_neg h]
      _                   = n         := by rw [mul_zero, add_zero]
  · intro n k (h: 0 < k ∧ k ≤ n)
    intro (ih: (n - k) % k + k * ((n - k) / k) = n - k)
    calc
      n % k + k * (n / k) = (n - k) % k + k * ((n - k) / k + 1) :=
        by rw [div_eq_if_pos h, mod_eq_if_pos h]
      _ = (n - k) % k + k * ((n - k) / k) + k :=
        by simp only [add_assoc, mul_succ]
      _ = n :=
        by simp only [ih, sub_add_cancel h.right]


theorem add_div_right (n: Nat){k: Nat}(h: 0 < k): (n + k) / k = (n / k).succ := by
  have: k ≤ n + k := add_comm k n ▸ le_add k n
  calc
    (n + k) / k = (n + k - k) / k + 1 := by rw [div_eq_if_pos ⟨h, this⟩]
    _           = (n / k).succ        := by rw [add_sub_cancel]

theorem add_mod_right (n k: Nat): (n + k) % k = n % k := by
  match eq_or_lt_of_le (zero_le k) with
  | Or.inl (zk: 0 = k) => rw [← zk, add_zero]
  | Or.inr (pk: 0 < k) =>
    have: 0 < k ∧ k ≤ n + k := ⟨pk, add_comm n k ▸ le_add k n⟩
    calc
      (n + k) % k = (n + k - k) % k := by rw [mod_eq_if_pos this]
      _           = n % k           := by rw [add_sub_cancel]

theorem add_mod_left (n k: Nat): (k + n) % k = n % k :=
  add_comm n k ▸ add_mod_right n k

theorem add_mul_div_left (m n: Nat){k: Nat}(h: 0 < k): (m + k * n) / k = m / k + n := by
  refine n.recOn rfl ?_
  intro n (ih: (m + k * n) / k = m / k + n)
  have := calc
    k ≤ k + (m + k * n) := le_add k (m + k * n)
    _ = m + (k * n + k) := by ac_rfl
    _ = m + k * n.succ  := by rw [mul_succ]
  calc
    (m + k * n.succ) / k = (m + k * n.succ - k) / k + 1 := by
      rw[div_eq_if_pos (And.intro h this)]
    (m + k * n.succ - k) / k + 1 = m / k + n + 1 := by
      rw [mul_succ, ←add_assoc, add_sub_cancel, ih]

theorem mul_div_cancel (m: Nat){n: Nat}(h: 0 < n): m * n / n = m := by
  calc
    m * n / n = (0 + n * m) / n := by rw [zero_add, mul_comm]
    _         = 0 / n + m       := add_mul_div_left 0 m h
    _         = m               := by rw [zero_div, zero_add]

theorem add_mul_mod_self_left (m n k: Nat): (m + k * n) % k = m % k := by
  refine n.recOn rfl ?_
  intro n (ih: (m + k * n) % k = m % k)
  calc
    (m + k * n.succ) % k = (m + k * n) % k := by rw [mul_succ, ←add_assoc, add_mod_right]
    _                    = m % k           := ih

theorem add_mul_mod_self_right (m n k: Nat): (m + n * k) % k = m % k :=
  mul_comm n k ▸ add_mul_mod_self_left m n k

theorem mul_mod_left (n k: Nat): n * k % k = 0 := by
  have: (0 + n*k) % k = 0 := zero_mod n ▸ add_mul_mod_self_right 0 n k
  exact zero_add (n*k) ▸ this

theorem mul_mod_right (n k: Nat): k * n % k = 0 :=
  mul_comm k n ▸ mul_mod_left n k

theorem mod_lt (n: Nat){k: Nat}: 0 < k → n % k < k := by
  refine divmod_ind (motive := λn k ↦ 0 < k → n % k < k) ?_ ?_ n k
  · intro n k (h: ¬(0 < k ∧ k ≤ n)) (pk: 0 < k)
    calc
      n % k = n := by rw [mod_eq_if_neg h]
      _     < k := (lt_or_ge n k).elim id (not_and.mp h pk).elim
  · intro n k (h: 0 < k ∧ k ≤ n) (ih: 0 < k → (n - k) % k < k) (pk: 0 < k)
    calc
      n % k = (n - k) % k := by rw [mod_eq_if_pos h]
      _     < k           := ih pk

theorem mod_mod (n k: Nat): n % k % k = n % k :=
  match k with
  | Nat.zero => mod_zero _
  | Nat.succ k =>
    have: n % k.succ < k.succ := mod_lt n (zero_lt_succ k)
    mod_eq_of_lt this

-- Неочевидная теорема
theorem mul_mod_mul_left (m n k: Nat): m * n % (m * k) = m * (n % k) := by
  match m with
  | Nat.zero => simp only [zero_mul, mod_zero]
  | Nat.succ m =>
    refine divmod_ind
      (motive := λn k ↦ m.succ * n % (m.succ * k) = m.succ * (n % k)) ?_ ?_ n k
    · intro n k (h: ¬(0 < k ∧ k ≤ n))
      have: ¬(0 < m.succ * k ∧ m.succ * k ≤ m.succ * n) :=
        h ∘ (λ⟨msk, k_le_msn⟩ ↦
          ⟨pos_of_mul_pos_left msk,
          le_of_mul_le_mul_left (zero_lt_succ m) k_le_msn⟩)
      calc
        m.succ * n % (m.succ * k) = m.succ * n       := by rw [mod_eq_if_neg this]
        m.succ * n                = m.succ * (n % k) := by rw [mod_eq_if_neg h]
    · intro n k ⟨_, (yx: k ≤ n)⟩
      intro (h2: m.succ * (n - k) % (m.succ * k) = m.succ * ((n - k) % k))
      calc
        m.succ * n % (m.succ * k) = (m.succ * n - m.succ * k) % (m.succ * k) :=
          by rw [mod_eq_sub_mod (mul_le_mul_left _ yx)]
        _ = (m.succ * (n - k)) % (m.succ * k) :=
          by simp only [mul_sub_left_distrib]
        _ = m.succ * ((n - k) % k) := h2
        _ = m.succ * (n % k)       := by rw [←mod_eq_sub_mod yx]

theorem add_mod (m n k: Nat): (m + n) % k = (m % k + n % k) % k := by
  calc
    (m + n) % k = ((m % k + k * (m / k)) + (n % k + k * (n / k))) % k := by
      rw [mod_add_div m k, mod_add_div n k]
    _ = (m % k + n % k + (k * (m / k) + k * (n / k))) % k := by ac_rfl
    _ = (_+ k * (m / k + n / k)) % k := by
      rw [←mul_left_distr k (m/k) (n/k)]
    _ = (m % k + n % k) % k := by rw [add_mul_mod_self_left]

theorem mul_mod (m n k: Nat): (m * n) % k = ((m % k) * (n % k)) % k := by
  calc
    m * n % k = ( (m%k + k * (m/k)) * (n%k + k * (n/k)) ) % k := by
      rw [mod_add_div m k, mod_add_div n k]
    _ = ( (m%k) * (n%k + k * (n/k)) + (k * (m/k)) * (n%k + k * (n/k)) ) % k := by
      rw [mul_right_distr]
    _ = ( (m%k) * (n%k + k * (n/k)) + k * ((m/k) * (n%k + k * (n/k))) ) % k := by
      ac_rfl
    _ = ( (m%k) * (n%k + k * (n/k)) ) % k := by
      rw [add_mul_mod_self_left]
    _ = ( (m%k) * (n%k) + (m%k) * (k * (n/k)) ) % k := by
      rw [mul_left_distr]
    _ = ( (m%k) * (n%k) + k * ((m%k) * (n/k)) ) % k := by
      ac_rfl
    _ = ( (m%k) * (n%k) ) % k := by
      rw [add_mul_mod_self_left]

-- Тактика `omega`

example: 2*a + b = a + b + a := by omega

#check Lean.Parser.Tactic.exact?
#check Lean.Parser.Tactic.apply?

-- https://loogle.lean-lang.org/
