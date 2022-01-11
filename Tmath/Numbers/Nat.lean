#check Nat

#check Add

theorem add_zero  (n: Nat)   : n + 0 = n                 :=  rfl
theorem add_one   (n: Nat)   : n + 1 = n.succ            :=  rfl
theorem add_succ  (n k: Nat) : n + k.succ = (n + k).succ :=  rfl

theorem zero_add (n: Nat) : 0 + n = n :=
  n.rec
    (rfl : 0+0 = 0)
    (λn (h: 0+n = n) => (by rw[h] : (0+n).succ = n.succ))

theorem succ_add (n k: Nat) : n.succ + k = (n + k).succ := by
  refine k.rec rfl (λk ih => ?s)
  show (n.succ + k).succ = (n + k.succ).succ
  rw[ih]; rfl

theorem add_assoc (n k p: Nat) : (n + k) + p = n + (k + p) := by
  refine p.rec rfl (λp ih => ?s)
  calc
    (n + k) + p.succ = (n + k + p).succ   :=  rfl
                   _ = (n + (k + p)).succ :=  by rw[ih]

example (n k p: Nat) : (n + k) + p = n + (k + p) := by
  refine p.rec rfl (λp ih => ?s)
  simp[add_succ, ih]

theorem add_comm (n k: Nat) : n + k = k + n :=
  n.rec (by rw[zero_add]; rfl) (λn ih => by simp[add_succ, succ_add, ih])

theorem add_left_comm (n k p: Nat) : n + (k + p) = k + (n + p) :=
calc
  n + (k + p) = (n + k) + p :=  by rw[←add_assoc]
            _ = (k + n) + p :=  by rw[add_comm k]
            _ = k + (n + p) :=  by rw[add_assoc]

example (a b c d e: Nat) : (((a + b) + c) + d) + e = (c + ((b + e) + a)) + d :=
by simp[add_assoc, add_comm, add_left_comm]

/- simp lemmas -/

-- Умножение

-- Сравнение

-- Вычитание и деление

#check Nat.sub
#check Nat.div
#check Nat.mod

-- Конечные числа

#check Fin
#check Subtype

-- Делимость

#check Nat.gcd


-- Целые числа

#check Int
-- #