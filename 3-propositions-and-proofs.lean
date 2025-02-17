-- Exercises from https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html

namespace ExercisesBasic

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  ⟨ fun ⟨ hp, hq ⟩ ↦ ⟨ hq, hp ⟩,
    fun ⟨ hq, hp ⟩ ↦ ⟨ hp, hq ⟩ ⟩

example : p ∨ q ↔ q ∨ p :=
  ⟨ fun h ↦ h.elim Or.inr Or.inl,
    fun h ↦ h.elim Or.inr Or.inl ⟩

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨ fun ⟨ ⟨ hp, hq ⟩, hr ⟩ ↦ ⟨ hp, ⟨ hq, hr ⟩ ⟩,
    fun ⟨ hp, ⟨ hq, hr ⟩ ⟩ ↦ ⟨ ⟨ hp, hq ⟩, hr ⟩ ⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  ⟨ fun h : (p ∨ q) ∨ r ↦
      h.elim
        ( fun h : p ∨ q ↦
            h.elim
              (fun hp ↦ Or.inl hp)
              (fun hq ↦ Or.inr (Or.inl hq)) )
        ( fun hr : r ↦ Or.inr (Or.inr hr)),
    fun h : p ∨ (q ∨ r) ↦
      h.elim
        ( fun hp : p ↦ Or.inl (Or.inl hp))
        ( fun h : q ∨ r ↦
            h.elim
              ( fun hq ↦ Or.inl (Or.inr hq) )
              ( fun hr ↦ Or.inr hr ))⟩

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  ⟨ show p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) from
    fun ⟨ hp, hor ⟩ ↦ hor.elim
      (fun hq ↦ Or.inl ⟨ hp, hq ⟩)
      (fun hr ↦ Or.inr ⟨ hp, hr ⟩),
    show (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) from
    fun hor ↦ hor.elim
      (fun ⟨ hp, hq ⟩ ↦ ⟨ hp, Or.inl hq ⟩)
      (fun ⟨ hp, hr ⟩ ↦ ⟨ hp, Or.inr hr ⟩) ⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  ⟨ fun h : p ∨ (q ∧ r) ↦ show (p ∨ q) ∧ (p ∨ r) from
      h.elim
      (fun hp ↦ ⟨ Or.inl hp, Or.inl hp ⟩)
      (fun ⟨ hq, hr ⟩ ↦ ⟨ Or.inr hq, Or.inr hr ⟩),
    fun (⟨ h1, h2 ⟩ : (p ∨ q) ∧ (p ∨ r)) ↦ show p ∨ (q ∧ r) from
      h1.elim
      (fun hp ↦ Or.inl hp)
      (fun hq ↦
        h2.elim
        (fun hp ↦ Or.inl hp)
        (fun hr ↦ Or.inr ⟨ hq, hr ⟩))⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  ⟨ fun h : p → (q → r) ↦ show p ∧ q → r from
      fun ⟨ hp, hq ⟩ ↦ h hp hq,
    fun h : p ∧ q → r ↦ show p → (q → r) from
      fun hp hq ↦ h ⟨ hp, hq ⟩ ⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨ fun h : (p ∨ q) → r ↦
      ⟨ fun hp ↦ show r from h (Or.inl hp),
        fun hq ↦ show r from h (Or.inr hq) ⟩,
    fun (⟨ h1, h2 ⟩ : (p → r) ∧ (q → r)) ↦
      fun hor : p ∨ q ↦ show r from
        hor.elim
        (fun hp ↦ h1 hp)
        (fun hq ↦ h2 hq)⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨ fun h : ¬(p ∨ q) ↦ show ¬p ∧ ¬q from
    ⟨ fun hp ↦ h (Or.inl hp),
      fun hq ↦ h (Or.inr hq) ⟩,
    fun (⟨ hnp, hnq ⟩ : ¬p ∧ ¬q) ↦ show ¬(p ∨ q) from
      fun hor ↦ hor.elim
        (fun hp ↦ hnp hp)
        (fun hq ↦ hnq hq) ⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h : ¬p ∨ ¬q ↦ show ¬(p ∧ q) from
    fun ⟨ hp, hq ⟩ ↦
      h.elim (fun hnp ↦ hnp hp) (fun hnq ↦ hnq hq)

example : ¬(p ∧ ¬p) :=
  fun ⟨ hp, hnp ⟩ ↦ hnp hp

example : p ∧ ¬q → ¬(p → q) :=
  fun ⟨ hp, hnq ⟩ ↦ show ¬(p → q) from
    fun h : p → q ↦
      have hq : q := h hp
      hnq hq

example : ¬p → (p → q) :=
  fun hnp hp ↦ absurd hp hnp

example : (¬p ∨ q) → (p → q) :=
  fun (h : ¬p ∨ q) hp ↦ h.elim
    (fun hnp ↦ absurd hp hnp)
    (fun hq ↦ hq)

example : p ∨ False ↔ p :=
  ⟨ fun h : p ∨ False ↦ h.elim
      (fun hp ↦ hp)
      (False.elim),
    fun hp ↦ Or.inl hp ⟩

example : p ∧ False ↔ False :=
  ⟨ fun h : p ∧ False ↦ h.right,
    fun hFalse ↦ ⟨ (False.elim hFalse), hFalse ⟩ ⟩

example : (p → q) → (¬q → ¬p) :=
  fun (h : p → q) hnq ↦ show ¬p from
    fun hp ↦
      have hq : q := h hp
      hnq hq

end ExercisesBasic

namespace ExercisesClassical

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h : p → q ∨ r ↦
    byCases
      (fun hp ↦
        have hor : q ∨ r := h hp
        hor.elim
          (fun hq ↦ Or.inl (fun _ ↦ hq))
          (fun hr ↦ Or.inr (fun _ ↦ hr)))
      (fun hnp ↦
        Or.inl (show p → q from
                fun hp ↦ absurd hp hnp))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h : ¬(p ∧ q) ↦
    byCases
      (fun hp ↦
        Or.inr (show ¬q from fun hq ↦ h ⟨ hp, hq ⟩))
      (fun hnp ↦
        Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q :=
  fun h : ¬(p → q) ↦
    ⟨ show p from byContradiction
        (fun hnp ↦
          have hpq : p → q := fun hp ↦ absurd hp hnp
          h hpq),
      show ¬q from (fun hq ↦
        have hpq : p → q := fun _ ↦ hq
        absurd hpq h) ⟩

example : (p → q) → (¬p ∨ q) :=
  fun h : p → q ↦
    byCases
      (fun hp ↦ Or.inr (show q from h hp))
      (fun hnp ↦ Or.inl hnp)

example : (¬q → ¬p) → (p → q) :=
  fun (h : ¬q → ¬p) hp ↦
    show q from byCases
      (fun hq ↦ hq)
      (fun hnq ↦
        have hnp := h hnq
        absurd hp hnp)

example : p ∨ ¬p :=
  byCases Or.inl Or.inr

example : (((p → q) → p) → p) :=
  fun h : (p → q) → p ↦ show p from
    byContradiction (fun hnp ↦
      have hpq : p → q := fun hp ↦ absurd hp hnp
      have hp := h hpq
      hnp hp
    )

end ExercisesClassical
