module

public import Mathlib.Data.Sym.Sym2
public import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Data.Set.Card

/-!
# The statement of JSP-000976

The target is Erdős Problem 1171 and Theorem 1.1 of Howe–Huffman–Kohlmeyer–Kruer.
The color-zero witness has inherited order type `ω₁ * ω` and a positive-color
witness is a set of exactly three vertices. The diagonal of `Sym2` is irrelevant.
-/

@[expose] public section

namespace Jsp000976

open Cardinal Ordinal

universe u v

/-- The source ordinal of the partition relation. -/
noncomputable abbrev SourceOrdinal : Ordinal.{u} := ω₁ ^ 2

/-- The order type of the homogeneous set in color zero. -/
noncomputable abbrev TargetOrdinal : Ordinal.{u} := ω₁ * ω

/-- Edge colors are indexed by `0, 1, …, k`. -/
abbrev EdgeColoring (α : Type u) (k : ℕ) := Sym2 α → Fin (k + 1)

/-- A set is monochromatic when all pairs of distinct members have the indicated color. -/
def Homogeneous {α : Type u} {C : Type v} (c : Sym2 α → C) (i : C) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → c s(x, y) = i

/-- The ordinal arrow with `k` positive colors, each seeking a triangle. -/
def OrdinalFiniteColorPartition (α β : Ordinal.{u}) (k : ℕ) : Prop :=
  ∀ c : EdgeColoring α.ToType k,
    (∃ s : Set α.ToType, Homogeneous c 0 s ∧ typeLT s = β) ∨
      ∃ i : Fin k, ∃ s : Set α.ToType, Homogeneous c i.succ s ∧ #s = 3

/-- The unconditional statement, with the quantifier over every finite palette. -/
def Statement : Prop :=
  ∀ k : ℕ, OrdinalFiniteColorPartition SourceOrdinal.{u} TargetOrdinal.{u} k

/-- Any coloring on the two-element subsets can be assigned arbitrary diagonal colors. -/
noncomputable def extendDistinctPairColoring {α : Type u} {k : ℕ}
    (c : {e : Sym2 α // ¬ e.IsDiag} → Fin (k + 1)) : EdgeColoring α k := by
  classical
  exact fun e => if h : ¬ e.IsDiag then c ⟨e, h⟩ else 0

@[simp] theorem extendDistinctPairColoring_apply {α : Type u} {k : ℕ}
    (c : {e : Sym2 α // ¬ e.IsDiag} → Fin (k + 1)) (e : Sym2 α) (h : ¬ e.IsDiag) :
    extendDistinctPairColoring c e = c ⟨e, h⟩ := by
  classical
  simp [extendDistinctPairColoring, h]

/-- The same statement for a symmetric function of two ordered vertices. -/
theorem ordinalFiniteColorPartition_iff_symmetric (α β : Ordinal.{u}) (k : ℕ) :
    OrdinalFiniteColorPartition α β k ↔
      ∀ c : α.ToType → α.ToType → Fin (k + 1), (∀ x y, c x y = c y x) →
        (∃ s : Set α.ToType, (∀ x ∈ s, ∀ y ∈ s, x ≠ y → c x y = 0) ∧ typeLT s = β) ∨
          ∃ i : Fin k, ∃ s : Set α.ToType,
            (∀ x ∈ s, ∀ y ∈ s, x ≠ y → c x y = i.succ) ∧ #s = 3 := by
  constructor
  · intro h c hsymm
    exact h (Sym2.lift ⟨c, hsymm⟩)
  · intro h c
    exact h (fun x y => c s(x, y)) (fun _ _ => congrArg c Sym2.eq_swap)

/-- A witness of cardinality three is precisely a set of three distinct vertices. -/
theorem cardinal_three_iff {α : Type u} {s : Set α} :
    #s = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  simpa only [← Set.toENat_cardinalMk, Cardinal.toENat_eq_ofNat] using
    (Set.encard_eq_three (s := s))

/-- For three vertices, the cardinal and inherited ordinal targets agree. -/
theorem cardinal_three_iff_typeLT_three {α : Ordinal.{u}} {s : Set α.ToType} :
    #s = 3 ↔ typeLT s = 3 := by
  rw [← Ordinal.card_type (α := s) (· < ·)]
  exact Ordinal.card_eq_nat

/-- The case with no positive color holds when the target is smaller than the source. -/
theorem ordinalFiniteColorPartition_zero {α β : Ordinal.{u}} (h : β < α) :
    OrdinalFiniteColorPartition α β 0 := by
  intro c
  have ht : typeLT β.ToType < typeLT α.ToType := by simpa using h
  obtain ⟨f⟩ := type_lt_iff.mp ht
  refine Or.inl ⟨Set.Iio f.top, ?_, ?_⟩
  · intro x _ y _ _
    exact Fin.eq_zero _
  · exact f.subrelIso.ordinalType_congr.trans (type_toType β)

/-- The original relation for `k = 0`. -/
theorem zeroPalette : OrdinalFiniteColorPartition SourceOrdinal.{u} TargetOrdinal.{u} 0 := by
  apply ordinalFiniteColorPartition_zero
  rw [SourceOrdinal, TargetOrdinal, pow_two]
  exact mul_lt_mul_of_pos_left omega0_lt_omega_one
    (omega0_pos.trans omega0_lt_omega_one)

end Jsp000976
