example: 1 + 1 = 2 := rfl

theorem add_zero  {n: Nat}:   n + 0 = n                  := rfl
theorem add_one   {n: Nat}:   n + 1 = n.succ             := rfl
theorem add_succ  {n k: Nat}: n + k.succ = (n + k).succ  := rfl

theorem zero_add {n: Nat}: 0 + n = n := by
  refine n.recOn ?z ?s
  · show 0 + 0 = 0
    rfl
  · intro n (h: 0 + n = n)
    show (0 + n).succ = n.succ
    rw[h]

theorem zero_add_match : {n: Nat} → 0 + n = n
| 0 => rfl
| Nat.succ n => congrArg Nat.succ (zero_add_match : 0 + n = n)

example {n: Nat}: 0 + n = n := by
  refine n.recOn rfl (λn h => ?_)
  rw[add_succ, h]

example {n: Nat}: 0 + n = n :=
  n.recOn rfl (λ_ h => congrArg Nat.succ h)

theorem succ_add {n k: Nat}: n.succ + k = (n + k).succ := by
  refine k.recOn rfl (λk h => ?s)
  show (n.succ + k).succ = (n + k.succ).succ
  rw[h, add_succ]

theorem add_assoc {n k p: Nat}: (n + k) + p = n + (k + p) := by
  refine p.recOn rfl (λp h => ?s)
  calc
    (n + k) + p.succ = (n + k + p).succ   :=  by rfl
                   _ = (n + (k + p)).succ :=  by rw[h]

example {n k p: Nat}: (n + k) + p = n + (k + p) :=
  p.recOn rfl (λp h => by simp[add_succ, h])

theorem add_comm {n k: Nat}: n + k = k + n :=
  n.recOn (by rw[zero_add]; rfl) (λn h => by simp[add_succ, succ_add, h])

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

theorem succ_cancel {n k: Nat}(e: n.succ = k.succ): n = k :=
  congrArg Nat.pred e

theorem succ_ne {n:Nat}: n.succ ≠ n :=
  n.recOn (Nat.noConfusion) (λn h => λ(e: n.succ.succ = n.succ) => h $ succ_cancel e)

theorem add_right_cancel {n k p: Nat}: (n+p = k+p) → n = k :=
  p.recOn id (λ_ h => λe => h $ succ_cancel e)

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

theorem mul_left_cancel {n k p: Nat}(pn: n ≠ 0): (n * k = n * p) → k = p := by
  suffices h: ∀k, (n * k = n * p) → k = p from h k
  refine p.recOn ?_ ?_
  · intro k (nk: n * k = 0)
    exact (mul_eq_zero nk).elim (λz: n = 0 => (pn z).elim) id
  · intro p h
    show ∀k, (n * k = n * p.succ) → k = p.succ
    refine λk => k.casesOn ?_ ?_
    · intro (e: 0 = n * p + n)
      exact (pn $ add_eq_zero_right e.symm).elim
    · intro k (e: n * Nat.succ k = n * Nat.succ p)
      exact congrArg Nat.succ $ h k (add_right_cancel e)

-- Сравнение

#print Nat.le
#check Nat.le.step

theorem le_refl {n: Nat}: n ≤ n := Nat.le.refl
theorem le_succ {n k: Nat}: n ≤ k → n ≤ k.succ := Nat.le.step
theorem zero_le {n: Nat}: 0 ≤ n :=
  n.recOn le_refl (λ_ h => le_succ h)

theorem le_add {n k: Nat}: n ≤ n + k :=
  k.recOn le_refl (λ_ h => le_succ h)

theorem le_exists {n k: Nat}(le: n ≤ k): ∃p, n + p = k :=
  le.recOn ⟨0,rfl⟩ (λ_ ⟨p,h⟩ => ⟨p.succ, congrArg Nat.succ h⟩)

theorem exists_le {n k: Nat}(ex: ∃p, n + p = k): n ≤ k :=
  ex.elim λp => p.recOn
    (λ(e: n = k) => e ▸ le_refl)
    (λp _ => λ(e: n + p.succ = k) => e.symm ▸ (le_add : n ≤ n + p.succ))

theorem succ_le {n k: Nat}(le: n.succ ≤ k): n ≤ k :=
  let ⟨p, (e: n.succ + p = k)⟩ := le_exists le
  exists_le ⟨p.succ, e.symm ▸ succ_add ▸ rfl⟩

theorem le_zero {n:Nat}(le: n ≤ 0): n = 0 :=
  (le_exists le).elim (λp (e: n + p = 0) => add_eq_zero_left e)

theorem add_le_add_left {n k p: Nat}(l: n ≤ k): n + p ≤ k + p := by
  refine (le_exists l).elim (λq (e: n + q = k) => exists_le ⟨q, ?_⟩)
  calc  n + p + q = n + q + p  := by simp[add_assoc, add_comm, add_left_comm]
    _ = k + p                  := by rw[e]

theorem le_trans {n k p: Nat}(nk: n ≤ k)(kp: k ≤ p): n ≤ p :=
  let ⟨a, (ea: n + a = k)⟩ := le_exists nk
  let ⟨b, (eb: k + b = p)⟩ := le_exists kp
  let e: n + a + b = p := (congrArg (· + b) ea).trans eb;
  exists_le ⟨a+b, add_assoc ▸ e⟩

theorem le_antisym {n k: Nat}(nk: n ≤ k)(kn: k ≤ n): n = k :=
  let ⟨a, (ea: n + a = k)⟩ := le_exists nk
  let ⟨b, (eb: k + b = n)⟩ := le_exists kn
  let e : k + (b + a) = k + 0 := add_assoc ▸ eb.symm ▸ ea
  let ba: b + a = 0 := add_left_cancel e
  ((add_eq_zero_right ba) ▸ ea : n + 0 = k)

theorem le_total: {n k: Nat} → n ≤ k ∨ k ≤ n
| 0, _                   => Or.inl zero_le
| Nat.succ _, 0          => Or.inr zero_le
| Nat.succ n, Nat.succ k =>
  (@le_total n k).elim
    (λnk => Or.inl $ Nat.succ_le_succ nk)
    (λkn => Or.inr $ Nat.succ_le_succ kn)

#check Nat.sub
#check Nat.div
#check Nat.mod
#check Fin
#check Subtype
#check Nat.gcd
#check Int

#check List

-- #check [1,2] + [3]

#check List.zipWith
#check List.replicate

#check HAdd
instance [h: HAdd α β γ]: HAdd (List α) (List β) (List γ) where
  hAdd := List.zipWith h.hAdd

#reduce [1,2] + [4,5]

class Scalar (α: Type u) where
instance: Scalar (Nat) where

instance [Scalar α][h: HAdd α β γ]: HAdd α (List β) (List γ) where
  hAdd v xs:= List.zipWith h.hAdd (List.replicate xs.length v) xs

instance [Scalar α][h: HSub α β γ]: HAdd α (List β) (List γ) where
  hAdd v xs:= List.zipWith h.hSub (List.replicate xs.length v) xs

instance [Scalar α][h: HMul α β γ]: HAdd α (List β) (List γ) where
  hAdd v xs:= List.zipWith h.hMul (List.replicate xs.length v) xs

instance [Scalar α][h: HDiv α β γ]: HAdd α (List β) (List γ) where
  hAdd v xs:= List.zipWith h.hDiv (List.replicate xs.length v) xs

#reduce 2 + [1, 2, 3]
#reduce (2:Nat) + List.range 3
#check List.reverse
#check OfNat
