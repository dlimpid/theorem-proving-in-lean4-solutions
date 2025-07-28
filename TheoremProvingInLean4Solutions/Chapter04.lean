/- 4. Quantifiers and Equality -/

/- 4.4. The Existential Quantifier -/

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

set_option linter.unusedVariables false in
example : (∃ x : α, r) → r :=
  fun ⟨(_ : α), (hr : r)⟩ => hr

set_option linter.unusedVariables false in
example (a : α) : r → (∃ x : α, r) :=
  fun hr : r => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun ⟨(w : α), (hpw : p w), (hr : r)⟩ => ⟨⟨w, hpw⟩, hr⟩)
    (fun ⟨⟨(w : α), (hpw : p w)⟩, (hr : r)⟩ => ⟨w, hpw, hr⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨(w : α), (hpwqw : p w ∨ q w)⟩ =>
      Or.elim hpwqw
        (fun hpw : p w => Or.inl ⟨w, hpw⟩)
        (fun hqw : q w => Or.inr ⟨w, hqw⟩))
    (fun hpq : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim hpq
        (fun ⟨(w : α), (hp : p w)⟩ => ⟨w, Or.inl hp⟩)
        (fun ⟨(w : α), (hq : q w)⟩ => ⟨w, Or.inr hq⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun (h : ∀ x, p x) ⟨(w : α), (hnpw : ¬p w)⟩ => hnpw (h w))
    (fun (h : ¬∃ x, ¬p x) (x : α) =>
      byContradiction
        (fun hnpx : ¬p x => h ⟨x, hnpx⟩))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun ⟨(w : α), (hpw : p w)⟩ (h : ∀ x, ¬p x) => h w hpw)
    (fun h : ¬∀ x, ¬p x =>
      byContradiction
        (fun h2 : ¬∃ x, p x =>
          have h' : ∀ x, ¬p x := fun (x : α) (hpx : p x) => h2 ⟨x, hpx⟩
          h h'))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun (h : ¬∃ x, p x) (x : α) (hpx : p x) => h ⟨x, hpx⟩)
    (fun (h : ∀ x, ¬p x) ⟨(w : α), (hpw : p w)⟩ => h w hpw)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h : ¬∀ x, p x =>
      byContradiction
        (fun h2 : ¬∃ x, ¬p x =>
          have h' : ∀ x, p x := fun (x : α) => byContradiction (fun hnpx : ¬p x => h2 ⟨x, hnpx⟩)
          h h'))
    (fun ⟨(w : α), (hnpw : ¬p w)⟩ (h : ∀ x, p x) => hnpw (h w))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun (h : ∀ x, p x → r) ⟨(w : α), (hpw : p w)⟩ => h w hpw)
    (fun (h : (∃ x, p x) → r) (x : α) (hpx : p x) => h ⟨x, hpx⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨(w : α), (hpwr : p w → r)⟩ (h : ∀ x, p x) => hpwr (h w))
    (fun h : (∀ x, p x) → r =>
      byCases
        (fun hp : ∀ x, p x => ⟨a, fun _ : p a => h hp⟩)
        (fun hnp : ¬∀ x, p x =>
          -- Derive `¬∀ x, p x → ∃ x, ¬p x`, copied from the previous exercise
          have ⟨(w : α), (hnpw : ¬p w)⟩ : ∃ x, ¬p x :=
            byContradiction
              (fun h2 : ¬∃ x, ¬p x =>
                have hnp' : ∀ x, p x :=
                  fun (x : α) => byContradiction (fun hnpx : ¬p x => h2 ⟨x, hnpx⟩)
                hnp hnp')
          ⟨w, fun hpw : p w => absurd hpw hnpw⟩))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun ⟨(w : α), (hrpw : r → p w)⟩ (hr : r) => ⟨w, hrpw hr⟩)
    (fun h : r → ∃ x, p x =>
      byCases
        (fun hr : r =>
          have ⟨(w : α), (hpw : p w)⟩ : ∃ x, p x := h hr
          ⟨w, fun _ : r => hpw⟩)
        (fun hnr : ¬r =>
          ⟨a, fun hr : r => absurd hr hnr⟩))

/- 4.6. Exercises -/

-- 1.

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun hpq : ∀ x, p x ∧ q x =>
      ⟨fun (x : α) => (hpq x).left, fun (x : α) => (hpq x).right⟩)
    (fun ⟨(hp : ∀ x, p x), (hq : ∀ x, q x)⟩ =>
      fun (x : α) => ⟨hp x, hq x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun (hpq : ∀ x, p x → q x) (hp : ∀ x, p x) (x : α) => hpq x (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun (h : (∀ x, p x) ∨ (∀ x, q x)) (x : α) =>
    Or.elim h
      (fun hp : ∀ x, p x => Or.inl (hp x))
      (fun hq : ∀ x, q x => Or.inr (hq x))

-- 2.


variable (α : Type) (p q : α → Prop)
variable (r : Prop)

set_option linter.unusedVariables false in
example : α → ((∀ x : α, r) ↔ r) :=
  fun a : α =>
    Iff.intro
      (fun h : ∀ _, r => h a)
      (fun (hr : r) (_ : α) => hr)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h : ∀ x, p x ∨ r =>
      byCases
        (fun hr : r => Or.inr hr)
        (fun hnr : ¬r =>
          Or.inl (fun (x : α) =>
            Or.elim (h x)
              (fun hpx : p x => hpx)
              (fun hr : r => absurd hr hnr))))
    (fun (h : (∀ x, p x) ∨ r) (x : α) =>
      Or.elim h
        (fun hp : ∀ x, p x => Or.inl (hp x))
        (fun hr : r => Or.inr hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun (h : ∀ x, r → p x) (hr : r) (x : α) => h x hr)
    (fun (h : r → ∀ x, p x) (x : α) (hr : r) => h hr x)

-- 3.

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have hbarber : shaves barber barber ↔ ¬shaves barber barber := h barber
  byCases
    (fun hs : shaves barber barber => hbarber.mp hs hs)
    (fun hns : ¬shaves barber barber => hns (hbarber.mpr hns))

-- 4.

def divides (x y : Nat) : Prop :=
  ∃ k, k * x = y

def even (n : Nat) : Prop :=
  divides 2 n

def prime (n : Nat) : Prop :=
  ∀ m, 1 < m ∧ m < n → ¬divides m n

def infinitely_many_primes : Prop :=
  ∀ n, ∃ m > n, prime m

def Fermat_prime (n : Nat) : Prop :=
  prime n ∧ ∃ m, 2 ^ 2 ^ m + 1 = n

def infinitely_many_Fermat_primes : Prop :=
  ∀ n, ∃ m > n, Fermat_prime m

def goldbach_conjecture : Prop :=
  ∀ n > 2, even n → ∃ p q, prime p ∧ prime q ∧ p + q = n

def Goldbach's_weak_conjecture : Prop :=
  ∀ n > 5, ¬even n → ∃ p q r, prime p ∧ prime q ∧ prime r ∧ p + q + r = n

def Fermat's_last_theorem : Prop :=
  ∀ n > 2, ¬∃ (a b c : Nat), a > 0 ∧ b > 0 ∧ c > 0 ∧ a ^ n + b ^ n = c ^ n
