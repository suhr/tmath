example: 1 + 1 = 2 := rfl

theorem add_zero  (n: Nat):   n + 0 = n                  := rfl
theorem add_one   (n: Nat):   n + 1 = n.succ             := rfl
theorem add_succ  (n k: Nat): n + k.succ = (n + k).succ  := rfl

theorem zero_add {n: Nat}: 0 + n = n := by
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

theorem add_left_comm (n k p: Nat): n + (k + p) = k + (n + p) :=
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

example {a b c d e: Nat}: (((a * b) * c) * d) * e = (c * ((b * e) * a)) * d :=
by simp [mul_assoc, mul_comm, mul_left_comm]

-- Больше умножения и сложения

example {n:Nat}: n.succ ≠ 0 := Nat.noConfusion
example {n:Nat}: 0 ≠ n.succ := Nat.noConfusion

#print Nat.pred

theorem succ_inj {n k: Nat}(e: n.succ = k.succ): n = k :=
  congrArg Nat.pred e

theorem succ_ne {n:Nat}: n.succ ≠ n :=
  n.recOn (Nat.noConfusion) (λn h => λ(e: n.succ.succ = n.succ) => h $ succ_inj e)

theorem add_right_cancel {n k p: Nat}: (n+p = k+p) → n = k :=
  p.recOn id (λ_ h => λe => h $ succ_inj e)

theorem add_left_cancel {n k p: Nat}: (p+n = p+k) → n = k :=
  add_comm ▸ (@add_comm p k) ▸ add_right_cancel

theorem add_eq_zero_left {n k: Nat}: (n + k = 0) → n = 0 :=
  k.recOn id (λk h => λ(e: n+k.succ = 0) => h $ congrArg Nat.pred e)

theorem add_eq_zero_right {n k: Nat}: (n + k = 0) → k = 0 :=
  add_comm ▸ add_eq_zero_left

theorem mul_eq_zero {n k: Nat}: (n * k = 0) → n = 0 ∨ k = 0 :=
  k.casesOn
    (λ_ => Or.inr rfl)
    (λk => λ(e: n*k + n = 0) => Or.inl $ add_eq_zero_right e)

theorem mul_left_cancel {n k p: Nat}(pn: n ≠ 0)(e: n * k = n * p): k = p := by
  refine (n.recOn ?_ ?_ : ∀p, _) p
  · sorry
  · sorry

-- Сравнение

#print Nat.le

theorem le_succ {n k: Nat}(q: n ≤ k): n ≤ k.succ := sorry
theorem zero_le {n: Nat}: 0 ≤ n :=
  sorry
theorem succ_le {n k: Nat}(le: n.succ ≤ k): n ≤ k :=
  sorry
theorem le_zero {n:Nat}(le: n ≤ 0): n = 0 :=
  sorry

theorem le_exists {n k: Nat}(le: n ≤ k): ∃p, n + p = k :=
  sorry
theorem exists_le {n k: Nat}(ex: ∃p, n + p = k): n ≤ k :=
  sorry

theorem succ_le_suc {n k: Nat}: n ≤ k ↔ n.succ ≤ k.succ :=
  sorry
theorem right_add_le_add {n k p: Nat}: n ≤ k ↔ n + p ≤ k + p :=
  sorry

theorem le_trans {n k p: Nat} (nk: n ≤ k) (kp: k ≤ p): n ≤ p :=
  sorry
theorem le_antisym {n k: Nat} (nk: n ≤ k) (kn: k ≤ n): n = k :=
  sorry
theorem le_total (n k: Nat): n ≤ k ∨ k ≤ n :=
  sorry

#check Nat.sub
#check Nat.div
#check Nat.mod
#check Fin
#check Subtype
#check Nat.gcd
#check Int

#check List
