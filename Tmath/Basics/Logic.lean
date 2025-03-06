--- Пропрозиционная логика

example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  pq.elim (λp ↦ (np p).elim) id

example {P Q R: Prop}(pqr : P ∧ (Q ∨ R)): (P ∧ Q) ∨ (P ∧ R) :=
  let ⟨p,qr⟩ := pqr;  qr.elim (λq ↦ Or.inl ⟨p,q⟩) (λr ↦ Or.inr ⟨p,r⟩)

example {P Q: Prop}(pq: P → Q)(nq: ¬Q): ¬P :=
  λp ↦ nq (pq p : Q)

-- Простые

example {P Q: Prop}(pq: P ∧ Q): Q ∧ P :=
  let ⟨p,q⟩ := pq;  ⟨q,p⟩

example {P Q R: Prop}(pQr: P ∧ (Q ∧ R)): (P ∧ Q) ∧ R :=
  let ⟨p,⟨q,r⟩⟩ := pQr;  ⟨⟨p,q⟩,r⟩

example {P Q: Prop}(p: P): Q → P :=
  λ_ ↦ p

example {P Q R: Prop}(pqr: P → Q → R): P ∧ Q → R :=
  λpq ↦ pqr (pq.left : P) (pq.right : Q)

example {P Q R: Prop}(pqr: P → Q → R)(pq: P → Q): P → R :=
  λp ↦ pqr p (pq p : Q)

example {P Q R: Prop}(pq: P → Q)(qr: Q → R): P → R :=
  λp ↦ qr (pq p)

example {P Q: Prop}(npq: ¬(P ∨ Q)): ¬P ∧ ¬Q :=
  ⟨λp ↦ npq (Or.inl p), λq ↦ npq (Or.inr q)⟩

example {P Q: Prop}(npQ: ¬P ∨ Q): P → Q :=
  λp ↦ npQ.elim (λnp ↦ (np p).elim) (λq ↦ q)

example {P Q R: Prop}(pQr: P → Q ∧ R): (P → Q) ∧ (P → R) :=
  ⟨λp ↦ (pQr p).left, λp ↦ (pQr p).right⟩

example {P Q R: Prop}(pqR: P ∨ Q → R): (P → R) ∧ (Q → R) :=
  ⟨λp ↦ pqR (Or.inl p), λq ↦ pqR (Or.inr q)⟩

-- Сложнее

example {P Q R: Prop}(pqR: (P ∨ Q) ∨ R): P ∨ (Q ∨ R) :=
  pqR.elim
    (λpq ↦ pq.elim (λp ↦ Or.inl p) (λq ↦ Or.inr (Or.inl q : Q ∨ R)))
    (λr ↦ Or.inr (Or.inr r : Q ∨ R))

example {P Q R: Prop}(pqPr : (P ∧ Q) ∨ (P ∧ R)): P ∧ (Q ∨ R) :=
  ⟨ pqPr.elim And.left And.left,
    pqPr.elim (λpq ↦ Or.inl pq.right) (λpr ↦ Or.inr pr.right) ⟩

example {P Q R: Prop}(pQr: P ∨ (Q ∧ R)): (P ∨ Q) ∧ (P ∨ R) :=
  ⟨ pQr.elim (λp ↦ Or.inl p) (λqr ↦ Or.inr qr.left),
    pQr.elim (λp ↦ Or.inl p) (λqr ↦ Or.inr qr.right) ⟩

--- Предикаты и кванторы

example {P Q: α → Prop}(apq: ∀x, P x ∧ Q x): (∀x, P x) ∧ (∀x, Q x) :=
  ⟨λx ↦ (apq x).left,  λx ↦ (apq x).right⟩

example {P: α → β → Prop}(eap: ∃x, ∀y, P x y): ∀y, ∃x, P x y :=
  let ⟨x,ap⟩ := eap;  λy ↦ ⟨x, (ap y : P x y)⟩

-- Простые

example {P: α → β → Prop}(ap: ∀x, ∀y, P x y): ∀y, ∀x, P x y :=
  λy x ↦ ap x y

example {P: α → β → Prop}(ep: ∃x, ∃y, P x y): ∃y, ∃x, P x y :=
  let ⟨x,⟨y,p⟩⟩ := ep;  ⟨y,⟨x,p⟩⟩

example {P: α → Prop}(ne: ¬∃x, P x): ∀x, ¬(P x) :=
  λx p ↦ ne ⟨x,p⟩

example {P: α → Prop}{Q: Prop}(epQ: (∃x, P x) → Q): ∀x, P x → Q :=
  λx p ↦ epQ ⟨x,p⟩

example {P: α → Prop}{Q: Prop}(apq: ∀x, P x → Q): (∃x, P x) → Q :=
  λ⟨x,p⟩ ↦ apq x p

-- Сложнее

example {P Q: α → Prop}(aa: (∀x, P x) ∨ (∀x, Q x)): ∀x, P x ∨ Q x :=
  λx ↦ aa.elim (λap ↦ Or.inl (ap x : P x)) (λaq ↦ Or.inr (aq x : Q x))

example {P Q: α → Prop}(ee: (∃x, P x) ∨ (∃x, Q x)): ∃x, P x ∨ Q x :=
  ee.elim (λ⟨x,p⟩ ↦ ⟨x, Or.inl p⟩) (λ⟨x,q⟩ ↦ ⟨x, Or.inr q⟩)

-- Классическая логика

example {P: Prop}(nem: ¬(P ∨ ¬P)): False :=
  nem (Or.inr λp ↦ nem (Or.inl p))

section classical
open Classical

example {P: Prop}(nnp: ¬¬P): P :=
  (em P).elim id (λnp ↦ (nnp np).elim)

example {P: Prop}(nnp: ¬¬P): P := by
  refine (em P).elim ?_ ?_
  · intro (p: P)
    exact p
  · intro (np: ¬P)
    exact False.elim $ nnp np

example {P Q: Prop}(pq: P → Q): ¬P ∨ Q :=
  (em P).elim (λp ↦ Or.inr $ pq p) Or.inl

example {P Q: Prop}(npq : ¬(P ∧ Q)): ¬P ∨ ¬Q :=
  (em P).elim (λp ↦ Or.inr $ λq ↦ npq ⟨p,q⟩) Or.inl

example {P Q: Prop}(np_q: ¬P → Q): ¬Q → P :=
  λnq ↦ (em P).elim id (λnp ↦ (nq $ np_q np).elim)

example {P Q: Prop}(pq_p: (P → Q) → P): P :=
  (em P).elim id (λnp ↦ pq_p (λp ↦ (np p).elim))

-- Одновременно em и byContradiction
example {α: Type}{P: α → Prop}(na: ¬∀x, P x): ∃x, ¬P x := by
  refine (em (∃x, ¬P x)).elim id (λne: (¬∃x, ¬P x) ↦ ?_)
  let ap: ∀x, P x :=  λx ↦ byContradiction (λnp ↦ ne ⟨x, np⟩)
  exact (na ap).elim

end classical
