-- https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html

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

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

end MaybeClassical
