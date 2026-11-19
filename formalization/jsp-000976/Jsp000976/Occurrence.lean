module

public import Jsp000976.ChainIdeal
public import Jsp000976.DenseCone
public import Mathlib.Data.Set.Countable

/-!
# Occurrence labels in a dense cone

A label records the chosen child as well as its tagged parent. If one label
is earlier than another, the earlier label's chosen child is a prefix of the
later parent. This is the relation used for thinning and the row ideal.
-/

@[expose] public section

namespace Jsp000976.DenseCone

universe u v w

variable {Tag : Type u}

/-- A tagged node in the chosen cone together with its selected child. -/
structure Occurrence (kind : List Nat → Tag) (t : Tag) (base : List Nat) : Type v where
  parent : List Nat
  child : Nat
  in_cone : base <+: parent
  tagged : kind parent = t

namespace Occurrence

variable {kind : List Nat → Tag} {t : Tag} {base : List Nat}

instance : Countable (Occurrence.{u, v} kind t base) := Function.Injective.countable
  (f := fun p : Occurrence.{u, v} kind t base => (p.parent, p.child)) (by
    rintro ⟨s, a, hs, ht⟩ ⟨q, b, hq, hu⟩ h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl)

/-- Path including the selected child. -/
def path (p : Occurrence.{u, v} kind t base) : List Nat := p.parent ++ [p.child]

/-- Earlier occurrence along a branch. -/
def Earlier (p q : Occurrence.{u, v} kind t base) : Prop := StrictPrefix p.path q.path

theorem earlier_irrefl (p : Occurrence.{u, v} kind t base) : ¬ Earlier p p :=
  fun h => Nat.lt_irrefl _ h.2

theorem Earlier.child_prefix_parent {p q : Occurrence.{u, v} kind t base} (h : Earlier p q) :
    p.path <+: q.parent := by
  refine List.prefix_of_prefix_length_le h.1 (List.prefix_append _ _) ?_
  exact Nat.le_of_lt_succ (by simpa [path] using h.2)

/-- A local child choice satisfying a fixed test at every tagged node yields
an infinite chain of occurrences satisfying that test. -/
theorem exists_chain (hdense : TypeDenseAbove kind t base)
    (good : Occurrence.{u, v} kind t base → Prop)
    (hgood : ∀ s (hs : base <+: s) (ht : kind s = t), ∃ a, good ⟨s, a, hs, ht⟩) :
    ContainsChain Earlier {p | good p} := by
  classical
  let G (s : List Nat) (a : Nat) :=
    ∃ (hs : base <+: s) (ht : kind s = t), good ⟨s, a, hs, ht⟩
  obtain ⟨f, hgood_f, hchain⟩ := exists_test_prefix_chain kind t base hdense G
    (fun s hs ht => by obtain ⟨a, ha⟩ := hgood s hs ht; exact ⟨a, hs, ht, ha⟩)
  have labels (n : Nat) : ∃ p : Occurrence.{u, v} kind t base, good p ∧ p.path = f n := by
    obtain ⟨s, a, _, _, ⟨hs, ht, hG⟩, hp⟩ := hgood_f n
    exact ⟨⟨s, a, hs, ht⟩, hG, hp.symm⟩
  choose F hF hpath using labels
  refine ⟨F, hF, fun i j hij => ?_⟩
  change StrictPrefix (F i).path (F j).path
  rw [hpath i, hpath j]
  exact hchain i j hij

/-- The local conditions for finite tests provide the clean chains required
to generate a proper ideal containing all the marks. -/
theorem clean_chains {Test : Type w} (hdense : TypeDenseAbove kind t base)
    (marks : Test → Set (Occurrence.{u, v} kind t base))
    (hlocal : ∀ (F : Finset Test) s (hs : base <+: s) (ht : kind s = t),
      ∃ a, ∀ i ∈ F, ⟨s, a, hs, ht⟩ ∉ marks i) :
    ∀ F : Finset Test, ContainsChain Earlier (RowIdeal.coveredByMarks marks F)ᶜ := by
  intro F
  apply exists_chain hdense
  intro s hs ht
  obtain ⟨a, ha⟩ := hlocal F s hs ht
  exact ⟨a, fun ⟨i, hi, him⟩ => ha i hi him⟩

end Occurrence

end Jsp000976.DenseCone
