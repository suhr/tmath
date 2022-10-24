example: 1 + 1 = 2 := rfl

theorem add_zero  (n: Nat):   n + 0 = n                  := rfl
theorem add_one   (n: Nat):   n + 1 = n.succ             := rfl
theorem add_succ  (n k: Nat): n + k.succ = (n + k).succ  := rfl

theorem zero_add (n: Nat): 0 + n = n := by
  refine n.recOn rfl (λn (h: 0+n = n) => ?_)
  show (0+n).succ = n.succ;  rw[h]

theorem succ_add {n k: Nat}: n.succ + k = (n + k).succ := by
  refine k.recOn rfl (λk h => ?s)
  show (n.succ + k).succ = (n + k.succ).succ
  rw[h]; rfl

theorem add_assoc {n k p: Nat}: (n + k) + p = n + (k + p) := by
  refine p.recOn rfl (λp ih => ?s)
  calc
    (n + k) + p.succ = (n + k + p).succ   :=  rfl
                   _ = (n + (k + p)).succ :=  by rw[ih]

example {n k p: Nat}: (n + k) + p = n + (k + p) := by
  refine p.recOn rfl (λp ih => ?s)
  simp[add_succ, ih]

theorem add_comm {n k: Nat}: n + k = k + n :=
  n.recOn (by rw[zero_add]; rfl) (λn ih => by simp[add_succ, succ_add, ih])

theorem add_left_comm (n k p: Nat) : n + (k + p) = k + (n + p) :=
calc  n + (k + p)
    = (n + k) + p  := by rw[←add_assoc]
  _ = (k + n) + p  := by rw[@add_comm k]
  _ = k + (n + p)  := by rw[add_assoc]

example (a b c d e: Nat): (((a + b) + c) + d) + e = (c + ((b + e) + a)) + d :=
by simp[add_assoc, add_comm, add_left_comm]

-- Умножение

theorem mul_zero {n: Nat}:   n * 0 = 0               := rfl
theorem mul_succ {n k: Nat}: n * k.succ = n * k + n  := rfl
theorem mul_one {n: Nat}:    n * 1 = n :=
  by rw[mul_succ, add_comm]; rfl

theorem zero_mul {n:Nat}: 0 * n = 0 := by
  refine n.recOn rfl (λn h => ?_)
  calc  0 * n.succ
      = 0 * n + 0  := rfl
    _ = 0 + 0      := by simp[h]

theorem succ_mul {n k: Nat}: n.succ * k = n * k + k := by
  refine k.recOn rfl (λk h => ?_)
  calc  n.succ * k.succ
      = n.succ * k + n.succ  := by rw[mul_succ]
    _ = n * k + k + n.succ   := by simp [h]
    _ = n * k + n + k.succ   := by simp [add_assoc, add_comm, add_left_comm, add_succ]
    _ = n * k.succ + k.succ  := by simp [mul_succ]

theorem one_mul {n:Nat}: 1*n = n := by
  rw [succ_mul]
  show 0*n + n = n;  rw [zero_mul, zero_add]

theorem mul_left_distr {n k p: Nat}: n * (k + p) = n * k + n * p := by
  refine p.recOn rfl (λp h => ?_)
  show n * (k + p.succ) = n * k + n * p.succ
  simp [add_succ, mul_succ, h, add_assoc]

theorem mul_assoc {n k p: Nat}: (n * k) * p = n * (k * p) := by
  refine p.recOn rfl (λp h => ?_)
  show n * k * p.succ = n * (k * p.succ)
  simp [mul_succ, h, ←mul_left_distr]

theorem mul_comm {n k: Nat}: n * k = k * n := by
  refine k.recOn ?_ (λk h => ?_)
  show n * 0 = 0 * n;            rw [mul_zero, zero_mul]
  show n * k.succ = k.succ * n;  rw [mul_succ, h, ←succ_mul]

theorem mul_left_comm {n k p: Nat}: n * (k * p) = k * (n * p) :=
by rw [←mul_assoc, @mul_comm n, mul_assoc]

theorem mul_right_distr {n k p: Nat}: (n + k) * p = n * p + k * p :=
by simp [mul_comm, mul_left_distr]

-- Больше умножения и сложения

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
