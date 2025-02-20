-- https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html
-- 2025-02-18

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  Nat.add_assoc (x * x + y * x) (x * y) (y * y) ▸ h2

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y)   * x + (x + y) * y := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y := by rw [←Nat.add_assoc]

namespace MaybeClassical

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _x : α, r) → r :=
  fun ⟨_, hr⟩ ↦ hr

example (a : α) : r → (∃ _x : α, r) :=
  fun hr ↦ ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  ⟨ fun ⟨x, hpx, hr⟩ ↦ ⟨⟨x, hpx⟩, hr⟩,
    fun ⟨⟨x, hpx⟩, hr⟩ ↦ ⟨x, hpx, hr⟩ ⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  ⟨ fun ⟨x, h⟩ ↦ match h with
      | Or.inl hpx => Or.inl ⟨x, hpx⟩
      | Or.inr hqx => Or.inr ⟨x, hqx⟩,
    fun h ↦ match h with
      | Or.inl ⟨x, hpx⟩ => ⟨x, Or.inl hpx⟩
      | Or.inr ⟨x, hqx⟩ => ⟨x, Or.inr hqx⟩ ⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  ⟨ fun h ⟨x, hnpx⟩ ↦
      have hpx := h x
      hnpx hpx,
    fun h x ↦ byContradiction
      (fun hnpx ↦ h ⟨x, hnpx⟩)⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  ⟨ fun ⟨x, hpx⟩ (h : ∀ x, ¬ p x) ↦ h x hpx,
    fun (h : ¬ (∀ x, ¬ p x)) ↦ byContradiction
      (fun h1 : ¬ (∃ x, p x) ↦
        have h2 : ∀ x, ¬ p x := fun x hpx ↦ h1 ⟨x, hpx⟩
        h h2)⟩

-- 2025-02-19

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  ⟨ λ (h : ¬∃x, p x) x hpx ↦ h ⟨x, hpx⟩,
    λ (h : ∀x, ¬p x) ⟨x, px⟩ ↦ h x px ⟩

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  ⟨ λ (hna : ¬∀x, p x) ↦ byContradiction 
      (λ (he : ¬∃x, ¬p x) ↦
        have ha : ∀x, p x := λx ↦ byContradiction (λhnpx ↦ he ⟨x, hnpx⟩)
        hna ha),
    λ ⟨x, hnpx⟩ hna ↦ hnpx (hna x) ⟩

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
  ⟨ λh ⟨x, hpx⟩ ↦ h x hpx,
    λh x hpx ↦ h ⟨x, hpx⟩ ⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  ⟨ λ ⟨x, h1⟩ (h2 : ∀x, p x) ↦ h1 (h2 x),
    λ (h1 : (∀ x, p x) → r) ↦ byCases
      (λ ⟨x, hnpx⟩ ↦ ⟨x, λhpx ↦ absurd hpx hnpx⟩)
      (λ (h2 : ¬∃x, ¬p x) ↦
        have h3 : ∀x, p x := λx ↦ byContradiction (λhnpx ↦ h2 ⟨x, hnpx⟩)
        ⟨a, λ_ ↦ h1 h3⟩) ⟩

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  ⟨ λ⟨x, hrpx⟩ hr ↦ ⟨x, hrpx hr⟩,
    λh ↦ byCases
      (λ hr ↦
        have ⟨x, hpx⟩ := h hr
        ⟨x, λ_↦ hpx⟩)
      (λ hnr ↦ ⟨a, λhr ↦ absurd hr hnr⟩) ⟩

end MaybeClassical

-- 2025-02-20

namespace Exercices1

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  ⟨ λ h : ∀x, p x ∧ q x ↦
      ⟨ λ a ↦ (h a).left, λ a ↦ (h a).right ⟩,
    λ (⟨ h1, h2 ⟩ : (∀x, p x) ∧ (∀x, q x)) a ↦ ⟨ h1 a, h2 a ⟩ ⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  λ h1 h2 a ↦ (h1 a) (h2 a)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  λ h a ↦ match h with
    | Or.inl hp => Or.inl (hp a)
    | Or.inr hq => Or.inr (hq a)

end Exercices1

namespace Exercises2

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  λ a ↦
    ⟨ λ h ↦ h a,
      λ hr _ ↦ hr ⟩

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  ⟨ λ h ↦ Classical.byCases
      (λ hr ↦ Or.inr hr)
      (λ hnr ↦
        suffices ∀ x, p x from Or.inl this
        λ a ↦ match h a with
          | Or.inl hpa => hpa
          | Or.inr hr => absurd hr hnr),
    λ h a ↦ match h with
      | Or.inl hp => Or.inl (hp a)
      | Or.inr hr => Or.inr hr ⟩

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  ⟨ λ h hr a ↦ h a hr,
    λ h a hr ↦ h hr a ⟩

end Exercises2
