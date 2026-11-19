module

public import Jsp000976.MarkFamily
public import Jsp000976.Incidence
public import Jsp000976.StageBounds

/-!
# A tree of full reservoirs in the ground model

Every node has a full child that meets any specified finite set of tests.
The child is selected by a single point outside all nonfull child reservoirs.
-/

@[expose] public section

namespace Jsp000976

open Set

universe u

variable {k : Nat} {c : Point.{u} → Point.{u} → Fin (k + 1)}
  {X : Set Point.{u}} {r : Nat}

structure FamilyNode (c : Point.{u} → Point.{u} → Fin (k + 1))
    (X : Set Point.{u}) (r : Nat) where
  carrier : Set Point.{u}
  full : Full carrier
  subsetX : carrier ⊆ X
  family : MarkFamily c X
  subfamily : family.carrier ⊆ carrier
  rank : r ≤ family.marked.card

def FamilyNode.childSet (N : FamilyNode c X r) (i : N.family.labels) : Set Point.{u} :=
  {y ∈ N.carrier | N.family.cutoff < y.1 ∧ i ∈ N.family.openLabels y}

/-- Every finite family of tests can be met while retaining a full child. -/
theorem FamilyNode.has_full_child_meeting (N : FamilyNode c X r)
    (F : Finset Point.{u}) (hF : ∀ y ∈ F, y ∈ X ∧ N.family.cutoff < y.1) :
    ∃ i : N.family.labels, Full (N.childSet i) ∧
      ∀ y ∈ F, ∀ p ∈ N.family.marked, i ∉ N.family.markSet y p := by
  classical
  let := N.family.countable
  let bad (i : N.family.labels) : Set Point.{u} :=
    if Full (N.childSet i) then ∅ else N.childSet i
  have hbad (i : N.family.labels) : ¬ Full (bad i) := by
    by_cases h : Full (N.childSet i)
    · change ¬ Full (if Full (N.childSet i) then ∅ else N.childSet i)
      simp only [h, ↓reduceIte]
      simp [Full, thickRows, rowSlice]
    · simp [bad, h]
  obtain ⟨y, hy, hyCut, hyAvoid⟩ :=
    N.full.exists_above_avoiding N.family.cutoff bad hbad
  let F' := insert y F
  have hF' (z : Point.{u}) (hz : z ∈ F') : z ∈ X ∧ N.family.cutoff < z.1 := by
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨N.subsetX hy, hyCut⟩
    · exact hF z hz
  obtain ⟨i, _, htest⟩ := N.family.exists_avoiding_finite_tests Set.univ
    N.family.ideal.univ_not_small F' hF'
  have hi : i ∈ N.family.openLabels y :=
    (N.family.mem_openLabels y i).mpr (htest y (Finset.mem_insert_self _ _))
  have hchild : Full (N.childSet i) := by
    by_contra h
    have hy' : y ∈ N.childSet i := ⟨hy, hyCut, hi⟩
    exact hyAvoid i (by simpa [bad, h] using hy')
  exact ⟨i, hchild, fun z hz => htest z (Finset.mem_insert_of_mem hz)⟩

theorem FamilyNode.exists_full_child (N : FamilyNode c X r) :
    ∃ i : N.family.labels, Full (N.childSet i) := by
  obtain ⟨i, hi, _⟩ := N.has_full_child_meeting ∅ (by simp)
  exact ⟨i, hi⟩

/-- A tree retaining all full children, with finite tests locally satisfiable. -/
structure PrunedFamilies (c : Point.{u} → Point.{u} → Fin (k + 1))
    (X : Set Point.{u}) (r : Nat) (Y : Set Point.{u}) where
  family : List Nat → MarkFamily c X
  reservoir : List Nat → Set Point.{u}
  family_sub : ∀ s, (family s).carrier ⊆ reservoir s
  rank : ∀ s, r ≤ (family s).marked.card
  cutoff : Stage.{u}
  cutoffs : ∀ s, (family s).cutoff < cutoff
  root : reservoir [] = Y
  choose : (s : List Nat) → Nat → (family s).labels
  transition : ∀ s n, reservoir (s ++ [n]) =
    {y ∈ reservoir s | (family s).cutoff < y.1 ∧ choose s n ∈ (family s).openLabels y}
  tests : ∀ (s : List Nat) (F : Finset Point.{u}), ∃ n,
    ∀ y ∈ F, y ∈ X → cutoff < y.1 → ∀ p ∈ (family s).marked,
      choose s n ∉ (family s).markSet y p

theorem exists_pruned_families
    (Y : Set Point.{u}) (hY : Full Y) (hYX : Y ⊆ X)
    (seed : ∀ Z : Set Point.{u}, Full Z → Z ⊆ X →
      ∃ M : MarkFamily c X, M.carrier ⊆ Z ∧ r ≤ M.marked.card) :
    Nonempty (PrunedFamilies c X r Y) := by
  classical
  choose family hsub hrank using seed
  let mkNode (Z : Set Point.{u}) (hZ : Full Z) (hZX : Z ⊆ X) : FamilyNode c X r :=
    ⟨Z, hZ, hZX, family Z hZ hZX, hsub Z hZ hZX, hrank Z hZ hZX⟩
  let root := mkNode Y hY hYX
  have hEnum (N : FamilyNode c X r) :
      ∃ f : Nat → {i // Full (N.childSet i)}, Function.Surjective f := by
    let := N.family.countable
    obtain ⟨i, hi⟩ := N.exists_full_child
    let : Nonempty {i // Full (N.childSet i)} := ⟨⟨i, hi⟩⟩
    exact exists_surjective_nat _
  let enumerate (N : FamilyNode c X r) := (hEnum N).choose
  let step (N : FamilyNode c X r) (n : Nat) :=
    mkNode (N.childSet (enumerate N n).1) (enumerate N n).2 (fun _ hy => N.subsetX hy.1)
  let node (s : List Nat) := s.foldl step root
  obtain ⟨cutoff, hcutoff⟩ := countable_bounded_stage (fun s => (node s).family.cutoff)
  refine ⟨{
    family := fun s => (node s).family
    reservoir := fun s => (node s).carrier
    family_sub := fun s => (node s).subfamily
    rank := fun s => (node s).rank
    cutoff := cutoff
    cutoffs := hcutoff
    root := rfl
    choose := fun s n => (enumerate (node s) n).1
    transition := ?_
    tests := ?_ }⟩
  · intro s n
    have hnext : node (s ++ [n]) = step (node s) n := by simp [node, List.foldl_append]
    rw [hnext]
    rfl
  · intro s F
    let F' := F.filter fun y => y ∈ X ∧ cutoff < y.1
    have hF' (y : Point.{u}) (hy : y ∈ F') : y ∈ X ∧ (node s).family.cutoff < y.1 := by
      obtain ⟨_, hyX, hyCut⟩ := Finset.mem_filter.mp hy
      exact ⟨hyX, (hcutoff s).trans hyCut⟩
    obtain ⟨i, hi, htest⟩ := (node s).has_full_child_meeting F' hF'
    obtain ⟨n, hn⟩ := (hEnum (node s)).choose_spec ⟨i, hi⟩
    refine ⟨n, fun y hy hyX hycut p hp => ?_⟩
    have heq : (enumerate (node s) n).1 = i := congrArg Subtype.val hn
    rw [heq]
    exact htest y (Finset.mem_filter.mpr ⟨hy, hyX, hycut⟩) p hp

theorem PrunedFamilies.child_subset {Y : Set Point.{u}} (T : PrunedFamilies c X r Y)
    (s : List Nat) (n : Nat) : T.reservoir (s ++ [n]) ⊆ T.reservoir s := by
  rw [T.transition]
  exact fun _ h => h.1

theorem PrunedFamilies.reservoir_antitone {Y : Set Point.{u}} (T : PrunedFamilies c X r Y)
    {s t : List Nat} (h : s <+: t) : T.reservoir t ⊆ T.reservoir s := by
  obtain ⟨l, rfl⟩ := List.prefix_iff_exists_eq_append.mp h
  clear h
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    have hs : s ++ a :: l = (s ++ [a]) ++ l := by simp
    intro x hx
    rw [hs] at hx
    exact T.child_subset s a (ih hx)

theorem PrunedFamilies.later_point {Y : Set Point.{u}} (T : PrunedFamilies c X r Y)
    {s t : List Nat} {n : Nat} (h : s ++ [n] <+: t)
    {y : Point.{u}} (hy : y ∈ (T.family t).carrier) :
    (T.family s).cutoff < y.1 ∧ T.choose s n ∈ (T.family s).openLabels y := by
  have hm := T.reservoir_antitone h (T.family_sub t hy)
  rw [T.transition] at hm
  exact hm.2

/-- On a family in the rich-incidence region, some positive color stays
unmarked, so the marking rank is strictly less than the number of colors. -/
theorem MarkFamily.marked_card_lt (M : MarkFamily c X) (hX : Full X)
    (hsub : M.carrier ⊆ X)
    (hinc : IncidenceProperty (fun x y => c x y ≠ 0) X)
    (hSym : Std.Symm fun x y => c x y ≠ 0)
    (hforward : ∀ (x : Point.{u}) (b : Stage.{u}), x.1 < b →
      {d | c x (b, d) ≠ 0}.Countable) :
    M.marked.card < k := by
  classical
  let := M.countable
  let E (i : M.labels) := incidenceExceptions (fun x y => c x y ≠ 0) X (M.row i) (M.slice i)
  have hE (i : M.labels) : ¬ Full (E i) := by
    apply hinc.not_full_exceptional hSym hforward (M.thick i)
    intro x hx
    exact hsub (M.mem_carrier i hx)
  obtain ⟨y, hy, hcut, hAvoid⟩ := hX.exists_above_avoiding M.cutoff E hE
  have hrich (i : M.labels) :
      ¬ {x ∈ M.slice i | c (M.row i, x) y ≠ 0}.Countable := by
    intro hCount
    exact hAvoid i ⟨⟨hy, (M.row_le_cutoff i).trans_lt hcut⟩, hCount⟩
  obtain ⟨p, hp0, hp, _⟩ := M.exists_unmarked_color y hy hcut hrich
  let positive : Finset (Fin (k + 1)) := Finset.univ.erase 0
  have hsmall : M.marked ⊂ positive := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨fun q hq => Finset.mem_erase.mpr ⟨M.marked_positive q hq, Finset.mem_univ _⟩, ?_⟩
    intro h
    exact hp (h.symm ▸ Finset.mem_erase.mpr ⟨hp0, Finset.mem_univ _⟩)
  have hcard : positive.card = k := by
    dsimp [positive]
    rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (k + 1)))]
    simp
  simpa only [hcard] using Finset.card_lt_card hsmall

end Jsp000976
