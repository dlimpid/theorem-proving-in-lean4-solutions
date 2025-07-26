/- # 3. Propositions and Proofs -/

/- ## 3.5. Classical Logic -/

open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

/-
As an exercise, you might try proving the converse, that is, showing that em can be proved from
dne.
-/

example (p : Prop) : p ∨ ¬p :=
  have contra : ¬(p ∨ ¬p) → ¬p :=
    fun (h : ¬(p ∨ ¬p)) (hp : p) => h (Or.inl hp)
  dne (fun h : ¬(p ∨ ¬p) => h (Or.inr (contra h)))

/- ## 3.7. Exercises -/

variable (p q r : Prop)

-- commutativity of ∧ and ∨

example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => ⟨h.right, h.left⟩)
    (fun h : q ∧ p => ⟨h.right, h.left⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q => Or.elim h Or.inr Or.inl)
    (fun h : q ∨ p => Or.elim h Or.inr Or.inl)

-- associativity of ∧ and ∨

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r => ⟨h.left.left, h.left.right, h.right⟩)
    (fun h : p ∧ q ∧ r => ⟨⟨h.left, h.right.left⟩, h.right.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun hpqr : (p ∨ q) ∨ r =>
      Or.elim hpqr
        (fun hpq : p ∨ q =>
          Or.elim hpq
            (fun hp : p => Or.inl hp)  -- Just `Or.inl` is sufficient.
            (fun hq : q => Or.inr (Or.inl hq)))
        (fun hr : r => Or.inr (Or.inr hr)))
    (fun hpqr : p ∨ (q ∨ r) =>
      Or.elim hpqr
        (fun hp : p => Or.inl (Or.inl hp))
        (fun hqr : q ∨ r =>
          Or.elim hqr
            (fun hq : q => Or.inl (Or.inr hq))
            (fun hr : r => Or.inr hr)))  -- `Or.inr`

-- distributivity

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun hpqr : p ∧ (q ∨ r) =>
      Or.elim hpqr.right
        (fun hq : q => Or.inl ⟨hpqr.left, hq⟩)
        (fun hr : r => Or.inr ⟨hpqr.left, hr⟩))
    (fun hpqpr : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim hpqpr
        (fun hpq : p ∧ q => ⟨hpq.left, Or.inl hpq.right⟩)
        (fun hpr : p ∧ r => ⟨hpr.left, Or.inr hpr.right⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun hpqr : p ∨ (q ∧ r) =>
      Or.elim hpqr
        (fun hp : p => ⟨Or.inl hp, Or.inl hp⟩)
        (fun hqr : q ∧ r => ⟨Or.inr hqr.left, Or.inr hqr.right⟩))
    (fun hpqpr : (p ∨ q) ∧ (p ∨ r) =>
      Or.elim hpqpr.left
        (fun hp : p => Or.inl hp)  -- `Or.inl`
        (fun hq : q =>
          Or.elim hpqpr.right
            (fun hp : p => Or.inl hp)  -- `Or.inl`
            (fun hr : r => Or.inr ⟨hq, hr⟩)))

-- other properties

example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun (hpqr : p → q → r) (hpq : p ∧ q) => hpqr hpq.left hpq.right)
    (fun (hpqr : p ∧ q → r) (hp : p) (hq : q) => hpqr ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun hpqr : (p ∨ q) → r => ⟨fun hp : p => hpqr (Or.inl hp), fun hq : q => hpqr (Or.inr hq)⟩)
    (fun (hprqr : (p → r) ∧ (q → r)) (hpq : p ∨ q) => Or.elim hpq hprqr.left hprqr.right)

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun hnpq : ¬(p ∨ q) => ⟨fun hp : p => hnpq (Or.inl hp), fun hq : q => hnpq (Or.inr hq)⟩)
    (fun (hnpnq : ¬p ∧ ¬q) (hpq : p ∨ q) => Or.elim hpq hnpnq.left hnpnq.right)

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun (hnpnq : ¬p ∨ ¬q) (hpq : p ∧ q) =>
    Or.elim hnpnq
      (fun hnp : ¬p => hnp hpq.left)
      (fun hnq : ¬q => hnq hpq.right)

example : ¬(p ∧ ¬p) :=
  fun h : p ∧ ¬p => h.right h.left

example : p ∧ ¬q → ¬(p → q) :=
  fun (hpnq : p ∧ ¬q) (hpq : p → q) => hpnq.right (hpq hpnq.left)

example : ¬p → (p → q) :=
  fun (hnp : ¬p) (hp : p) => absurd hp hnp

example : (¬p ∨ q) → (p → q) :=
  fun (hnpq : ¬p ∨ q) (hp : p) =>
    Or.elim hnpq
      (fun hnp : ¬p => absurd hp hnp)
      (fun hq : q => hq)

example : p ∨ False ↔ p :=
  Iff.intro
    (fun hpf : p ∨ False => Or.elim hpf (fun hp : p => hp) False.elim)
    Or.inl

example : p ∧ False ↔ False :=
  Iff.intro And.right False.elim

example : (p → q) → (¬q → ¬p) :=
  fun (hpq : p → q) (hnq : ¬q) (hp : p) => hnq (hpq hp)

/-
Prove the following identities, replacing the sorry placeholders with actual proofs.
These require classical reasoning.
-/

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun hpqr : p → q ∨ r =>
    byCases
      (fun hp : p =>
        Or.elim (hpqr hp)
          (fun hq : q => Or.inl (fun _ : p => hq))
          (fun hr : r => Or.inr (fun _ : p => hr)))
      (fun hnp : ¬p => Or.inl (fun hp : p => absurd hp hnp))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun hnpq : ¬(p ∧ q) =>
    byCases
      (fun hp : p =>
        byCases
          (fun hq : q => absurd ⟨hp, hq⟩ hnpq)
          Or.inr)
      Or.inl

example : ¬(p → q) → p ∧ ¬q :=
  fun hnpq : ¬(p → q) =>
    byCases
      (fun hq : q => absurd (fun _ : p => hq) hnpq)
      (fun hnq : ¬q =>
        byCases
          (fun hp : p => ⟨hp, hnq⟩)
          (fun hnp : ¬p => absurd (fun hp : p => absurd hp hnp) hnpq))

example : (p → q) → (¬p ∨ q) :=
  fun hpq : p → q =>
    byCases
      (fun hp : p => Or.inr (hpq hp))
      Or.inl

example : (¬q → ¬p) → (p → q) :=
  fun (hnqnp : ¬q → ¬p) (hp : p) => byContradiction (fun hnq : ¬q => hnqnp hnq hp)

example : p ∨ ¬p :=
  em p

example : (((p → q) → p) → p) :=
  fun hpqp : (p → q) → p =>
    byContradiction (fun hnp : ¬p => hnp (hpqp (fun hp : p => absurd hp hnp)))

/-
Prove `¬(p ↔ ¬p)` without using classical logic.
-/

example : ¬(p ↔ ¬p) :=
  fun h : p ↔ ¬p =>
    have hnp : ¬p := fun hp : p => h.mp hp hp
    hnp (h.mpr hnp)
