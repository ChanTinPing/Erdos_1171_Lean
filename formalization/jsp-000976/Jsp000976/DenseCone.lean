module

public import Init

/-!
# Recurrent types and finite tests on a tree

In a finitely colored tree, one type has an occurrence extending each node
of some cone. For any fixed local test, the successful child occurrences of
that type contain an infinite chain. The chain can depend on the test.
-/

@[expose] public section

namespace Jsp000976

universe u

/-- Proper extension order on tree paths. -/
def StrictPrefix (s t : List Nat) : Prop :=
  s <+: t ∧ s.length < t.length

theorem StrictPrefix.trans {s t u : List Nat} (hst : StrictPrefix s t)
    (htu : StrictPrefix t u) : StrictPrefix s u :=
  ⟨hst.1.trans htu.1, Nat.lt_trans hst.2 htu.2⟩

/-- A relation that holds from each child to its parent also holds from
each descendant to its prefix, when the relation is reflexive and transitive. -/
theorem descendant_of_prefix {State : Type u} (node : List Nat → State)
    (rel : State → State → Prop) (refl : ∀ x, rel x x)
    (trans : ∀ {x y z}, rel x y → rel y z → rel x z)
    (step : ∀ s a, rel (node (s ++ [a])) (node s))
    {s t : List Nat} (hst : s <+: t) : rel (node t) (node s) := by
  obtain ⟨suffix, rfl⟩ := hst
  induction suffix generalizing s with
  | nil => simpa using refl (node s)
  | cons a tail ih =>
    have h := trans (ih (s := s ++ [a])) (step s a)
    simpa [List.append_assoc] using h

/-- Every extension of `base` has a further extension of the chosen type. -/
def TypeDenseAbove {TypeTag : Type u} (kind : List Nat → TypeTag)
    (t : TypeTag) (base : List Nat) : Prop :=
  ∀ s, base <+: s → ∃ q, s <+: q ∧ kind q = t

private theorem exists_dense_type_subcone {TypeTag : Type u} (kind : List Nat → TypeTag)
    (types : List TypeTag) (base : List Nat)
    (hcover : ∀ p, base <+: p → kind p ∈ types) :
    ∃ b, base <+: b ∧ ∃ t ∈ types, TypeDenseAbove kind t b := by
  classical
  induction types generalizing base with
  | nil =>
    exact (List.not_mem_nil (hcover base List.prefix_rfl)).elim
  | cons t types ih =>
    by_cases ht : TypeDenseAbove kind t base
    · exact ⟨base, List.prefix_rfl, t, List.mem_cons_self, ht⟩
    · unfold TypeDenseAbove at ht
      obtain ⟨b, hb⟩ := Classical.not_forall.mp ht
      have hb' : base <+: b := Classical.byContradiction (fun h => hb (fun h' => (h h').elim))
      have no_t (p) (hp : b <+: p) : kind p ≠ t := fun h =>
        hb (fun _ => ⟨p, hp, h⟩)
      have next (p) (hp : b <+: p) : kind p ∈ types :=
        (List.mem_cons.mp (hcover p (hb'.trans hp))).resolve_left (no_t p hp)
      obtain ⟨c, hc, t', ht', hd⟩ := ih b next
      exact ⟨c, hb'.trans hc, t', List.mem_cons_of_mem _ ht', hd⟩

/-- Finitely many types cover the tree, so one type is dense in some cone. -/
theorem exists_dense_type_cone {TypeTag : Type u} (kind : List Nat → TypeTag)
    (types : List TypeTag) (hcover : ∀ p, kind p ∈ types) :
    ∃ b t, t ∈ types ∧ TypeDenseAbove kind t b := by
  obtain ⟨b, _, t, ht, hd⟩ :=
    exists_dense_type_subcone kind types [] (fun p _ => hcover p)
  exact ⟨b, t, ht, hd⟩

private theorem exists_prefix_chain (A : List Nat → Prop) (base : List Nat)
    (next : ∀ p, base <+: p → ∃ q, StrictPrefix p q ∧ A q) :
    ∃ f : Nat → List Nat, (∀ n, A (f n)) ∧
      ∀ n m, n < m → StrictPrefix (f n) (f m) := by
  classical
  let Cone := {p : List Nat // base <+: p}
  have next' (p : Cone) : ∃ q : Cone, StrictPrefix p.val q.val ∧ A q.val := by
    obtain ⟨q, hq, hA⟩ := next p.val p.property
    exact ⟨⟨q, p.property.trans hq.1⟩, hq, hA⟩
  let f : Nat → Cone :=
    Nat.rec ⟨base, List.prefix_rfl⟩ (fun _ p => (next' p).choose)
  have hf (n : Nat) : StrictPrefix (f n).val (f (n + 1)).val ∧ A (f (n + 1)).val :=
    (next' (f n)).choose_spec
  refine ⟨fun n => (f (n + 1)).val, fun n => (hf n).2, ?_⟩
  intro n m
  induction m with
  | zero =>
    exact fun hn => (Nat.not_lt_zero n hn).elim
  | succ m ih =>
    intro hnm
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hnm) with h | h
    · exact (ih h).trans (hf (m + 1)).1
    · exact h.symm ▸ (hf (m + 1)).1

/-- In the chosen type's cone, every fixed local test admits an infinite
chain of successful child occurrences. A label records the path up to and
including the selected child. -/
theorem exists_test_prefix_chain {TypeTag : Type u} (kind : List Nat → TypeTag)
    (t : TypeTag) (base : List Nat) (hdense : TypeDenseAbove kind t base)
    (good : List Nat → Nat → Prop)
    (hgood : ∀ s, base <+: s → kind s = t → ∃ a, good s a) :
    ∃ f : Nat → List Nat,
      (∀ n, ∃ s a, base <+: s ∧ kind s = t ∧ good s a ∧ f n = s ++ [a]) ∧
      ∀ n m, n < m → StrictPrefix (f n) (f m) := by
  apply exists_prefix_chain
    (fun q => ∃ s a, base <+: s ∧ kind s = t ∧ good s a ∧ q = s ++ [a]) base
  intro p hp
  obtain ⟨s, hps, ht⟩ := hdense p hp
  obtain ⟨a, ha⟩ := hgood s (hp.trans hps) ht
  refine ⟨s ++ [a], ⟨hps.trans (List.prefix_append _ _), ?_⟩,
    s, a, hp.trans hps, ht, ha, rfl⟩
  simpa using Nat.lt_succ_of_le hps.length_le

end Jsp000976
