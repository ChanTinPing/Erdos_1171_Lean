module

public import Jsp000976.Thinning

@[expose] public section

namespace Jsp000976

open Set Cardinal

universe u

abbrev Point := Stage.{u} × Stage.{u}

/-- A stock consists of countably many increasing rows with an uncountable
slice in every row. -/
structure Stock where
  row : Nat → Stage.{u}
  increasing : StrictMono row
  slice : Nat → Set Stage.{u}
  thick : ∀ n, ¬ (slice n).Countable

def Stock.carrier (A : Stock.{u}) : Set Point.{u} :=
  {x | ∃ n, x.1 = A.row n ∧ x.2 ∈ A.slice n}

theorem Stock.mem_carrier (A : Stock.{u}) (n : Nat) {x : Stage.{u}}
    (hx : x ∈ A.slice n) : (A.row n, x) ∈ A.carrier :=
  ⟨n, rfl, hx⟩

/-- Restrict to an increasing sequence of rows and an uncountable subset
of the slice in each retained row. -/
def Stock.restrict (A : Stock.{u}) (f : Nat → Nat) (hf : StrictMono f)
    (S : Nat → Set Stage.{u}) (hS : ∀ n, ¬ (S n).Countable) : Stock.{u} where
  row := A.row ∘ f
  increasing := A.increasing.comp hf
  slice := S
  thick := hS

theorem Stock.restrict_subset (A : Stock.{u}) (f : Nat → Nat) (hf : StrictMono f)
    (S : Nat → Set Stage.{u}) (hS : ∀ n, ¬ (S n).Countable)
    (hsub : ∀ n, S n ⊆ A.slice (f n)) : (A.restrict f hf S hS).carrier ⊆ A.carrier := by
  rintro x ⟨n, hn, hx⟩
  exact ⟨f n, hn, hsub n hx⟩

theorem exists_uncountable_fiber {α β : Type*} [Countable β] {S : Set α}
    (hS : ¬ S.Countable) (f : S → β) :
    ∃ b, ¬ {x : S | f x = b}.Countable := by
  classical
  by_contra! h
  exact hS (Countable.of_preimage_singleton (fun b => h b))

theorem exists_uncountable_independent_of_countable_neighbors
    {α : Type u} (S : Set α) (hS : ¬ S.Countable)
    (G : α → α → Prop) (hSymm : Std.Symm G)
    (hdegree : ∀ x ∈ S, {y ∈ S | G x y}.Countable) :
    ∃ T ⊆ S, ¬ T.Countable ∧ T.Pairwise (fun x y => ¬ G x y) := by
  classical
  let conflict (a b : Σ _ : Stage.{u}, α) := a.2 = b.2 ∨ G a.2 b.2
  have hsym : Std.Symm conflict :=
    ⟨fun a b h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr (hSymm.symm _ _ h))⟩
  have hcount (a b : Stage.{u}) (_ : a ≠ b) (x : α) (hx : x ∈ S) :
      {y ∈ S | conflict ⟨a, x⟩ ⟨b, y⟩}.Countable :=
    ((countable_singleton x).union (hdegree x hx)).mono <| by
      rintro y ⟨hy, he | hg⟩
      · exact Or.inl he.symm
      · exact Or.inr ⟨hy, hg⟩
  obtain ⟨T, hT, hfree⟩ :=
    exists_uncountable_thinning (ι := Stage.{u}) (by simp [Stage])
      (fun _ => S) (fun _ => hS) conflict hsym hcount
  have hne (i : Stage.{u}) : (T i).Nonempty := by
    by_contra! h
    exact (hT i).2 (by simp [h])
  choose f hf using hne
  have hf_inj : Function.Injective f := by
    intro i j h
    by_contra hij
    exact hfree i j hij _ (hf i) _ (hf j) (Or.inl h)
  refine ⟨range f, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact (hT i).1 (hf i)
  · intro h
    have := h.to_subtype
    exact (not_countable (α := Stage.{u})) <| Function.Injective.countable
      (f := fun i => (⟨f i, mem_range_self i⟩ : range f))
      (fun i j hij => hf_inj (congrArg (fun x : range f => x.1) hij))
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij hG
    exact hfree i j (fun h => hij (congrArg f h)) _ (hf i) _ (hf j) (Or.inr hG)

end Jsp000976
