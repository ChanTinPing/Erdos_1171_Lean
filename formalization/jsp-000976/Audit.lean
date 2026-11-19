module

import Jsp000976.Theorem

open Cardinal Ordinal Jsp000976

universe u

-- The Formal Conjectures representation, fully expanded without local aliases.
example : ∀ k : ℕ, ∀ c : Sym2 (ω₁ ^ 2 : Ordinal.{u}).ToType → Fin (k + 1),
    (∃ S : Set (ω₁ ^ 2 : Ordinal.{u}).ToType,
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → c s(x, y) = 0) ∧ typeLT S = ω₁ * ω) ∨
      ∃ i : Fin k, ∃ S : Set (ω₁ ^ 2 : Ordinal.{u}).ToType,
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → c s(x, y) = i.succ) ∧ #S = 3 :=
  erdos_1171

-- The equivalent Jig representation, using symmetric functions and order type three.
example : ∀ k : ℕ,
    ∀ c : (ω₁ ^ 2 : Ordinal.{u}).ToType → (ω₁ ^ 2 : Ordinal.{u}).ToType → Fin (k + 1),
      (∀ x y, c x y = c y x) →
        (∃ S : Set (ω₁ ^ 2 : Ordinal.{u}).ToType,
          typeLT S = ω₁ * ω ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c x y = 0) ∨
          ∃ i : Fin k, ∃ S : Set (ω₁ ^ 2 : Ordinal.{u}).ToType,
            typeLT S = 3 ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c x y = i.succ := by
  intro k c hsym
  rcases (ordinalFiniteColorPartition_iff_symmetric _ _ k).mp (erdos_1171 k) c hsym with
      ⟨S, hS, htype⟩ | ⟨i, S, hS, hcard⟩
  · exact Or.inl ⟨S, htype, hS⟩
  · exact Or.inr ⟨i, S, cardinal_three_iff_typeLT_three.mp hcard, hS⟩

#print axioms Jsp000976.erdos_1171
