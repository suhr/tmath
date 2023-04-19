#eval 2+2
#check Sigma
#check Σ'x, x > 3
#check [1, 2, 3]
#check (_ ∘ _)
#check Function.comp

#check HasEquiv
#check Fin

-- Карта и территория

#check propext
#check funext

-- Натуральные числа

#check Add
#check Mul

#check congr
#check Eq.subst

#check {x // x > 3}
#check Subtype.eta

#check Exists
#check Fin

-- Фактор-типы и целые числа

-- Рациональные и вещественные числа

-- Множества и зависимые пары

-- Функции

namespace Function

def retraction   (f: α → ω)(g: ω → α): Prop :=  ∀x, g (f x) = x
def coretraction (f: ω → α)(g: α → ω): Prop :=  retraction g f

def inverse (f: α → ω)(g: ω → α) : Prop :=  retraction f g ∧ retraction g f

def injective  (f: α → ω) : Prop :=  ∀x y, f x = f y → x = y
def surjective (f: α → ω) : Prop :=  ∀y, ∃x, f x = y
def bijective  (f: α → ω) : Prop :=  injective f ∧ surjective f

theorem has_retr_injective (f: α → ω)(er: ∃g, retraction f g) : injective f :=
by
  let ⟨g, r⟩ := er;
  intro x y (e: f x = f y);  show x = y
  have e2: g (f x) = g (f y) := congrArg g e
  exact r x ▸ r y ▸ e2

theorem has_coretr_surjective (f: ω → α)(ec: ∃g, coretraction f g) : surjective f :=
  let ⟨g,c⟩ := ec;  λy:α => ⟨g y, (by rw[c y] : f (g y) = y)⟩

-- theorem inj_has_retraction (f: α → ω)(ij: injective f) : ∃g, retraction f g :=
-- by sorry

-- theorem surj_has_coretraction (f: α → ω)(sj: surjective f) : ∃g, coretraction f g :=
-- by sorry

theorem lwfix (f: α → α → ω)(sj: surjective f)(u: ω → ω): ∃x, u x = x := by
  let d := λx => u (f x x);  let ⟨c,fp⟩ := (sj d : ∃c, f c = d);
  refine ⟨d c, Eq.symm ?_⟩
  calc
    d c = u (f c c) := rfl
    _   = u (d c)   := by rw[fp] 

end Function

-- Отношения

---------------

#check WellFounded

#check Acc

example (n:Nat): Acc Nat.lt n := by
  apply Nat.rec
  · show Acc _ 0
    exact Acc.intro _ $ λk (h: k < 0) => absurd h (Nat.not_lt_zero k)
  · refine λn h => (?_: Acc _ n.succ)
    refine Acc.intro _ $ λk (lt: k < n.succ) => (?_: Acc _ k)
    apply (Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ lt)).elim
    · intro (l: k = n); exact l ▸ h
    · intro (r: k < n); exact Acc.inv h r

#check Eq.subst

-- example {C: α → Sort v}(F: ∀ x, (∀ y, r y x → C y) → C x)(x:α)(a: Acc r x): C x :=
--   a.rec (λx _ ih => F x ih)

#print Acc.rec

inductive WTree {α:Type}: α → Type where
| leaf (r:α): WTree r
| branch (x:α)(b: ∀y:α, WTree y): WTree x
