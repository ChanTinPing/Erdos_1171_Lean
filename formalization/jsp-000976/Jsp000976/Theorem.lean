module

public import Jsp000976.Finish
public import Jsp000976.GroundStep
public import Jsp000976.NestedIncidence
public import Jsp000976.Occurrence
public import Jsp000976.PrunedFamilies
import Mathlib.Data.Fintype.Powerset

/-!
# Erdős Problem 1171

The proof uses the ideal of label sets containing no infinite prefix chain.
The resulting marking induction uses finite tests in the ground model.
-/

@[expose] public section

namespace Jsp000976

open Set DenseCone

universe u

private theorem PrunedFamilies.exists_groundCandidates {k r : Nat}
    {c : GridColoring.{u} k} {X Y : Set Point.{u}}
    (T : PrunedFamilies c X r Y) : Nonempty (GroundCandidates c X Y r) := by
  classical
  let kind (s : List Nat) := (T.family s).marked
  obtain ⟨base, L, _, dense⟩ := exists_dense_type_cone kind
    (Finset.univ.toList : List (Finset (Fin (k + 1)))) (fun s => by simp [kind])
  let Label : Type := Occurrence kind L base
  let chooseSlice (a : Label) := T.choose a.parent a.child
  let row (a : Label) := (T.family a.parent).row (chooseSlice a)
  let slice (a : Label) := (T.family a.parent).slice (chooseSlice a)
  have thick (a : Label) : ¬ (slice a).Countable := (T.family a.parent).thick (chooseSlice a)
  have inFamily (a : Label) (x : Stage.{u}) (hx : x ∈ slice a) :
      (row a, x) ∈ (T.family a.parent).carrier :=
    (T.family a.parent).mem_carrier (chooseSlice a) hx
  have belowParent (a : Label) : row a ≤ (T.family a.parent).cutoff :=
    (T.family a.parent).row_le_cutoff (chooseSlice a)
  have later (a b : Label) (h : Occurrence.Earlier a b) (y : Stage.{u}) (hy : y ∈ slice b) :
      (T.family a.parent).cutoff < row b ∧
        chooseSlice a ∈ (T.family a.parent).openLabels (row b, y) :=
    T.later_point h.child_prefix_parent (inFamily b y hy)
  have ordered (a b : Label) (h : Occurrence.Earlier a b) : row a < row b := by
    obtain ⟨y, hy⟩ : (slice b).Nonempty := by
      by_contra! hn
      exact thick b (by simp [hn])
    exact (belowParent a).trans_lt (later a b h y hy).1
  obtain ⟨s, _, hkind⟩ := dense base List.prefix_rfl
  change (T.family s).marked = L at hkind
  have hL (p : Fin (k + 1)) (hp : p ∈ L) : p ≠ 0 :=
    (T.family s).marked_positive p (hkind.symm ▸ hp)
  have hRank : r ≤ L.card := hkind ▸ T.rank s
  refine ⟨{
    labels := Label
    countable := inferInstance
    earlier := Occurrence.Earlier
    row := row
    ordered := ordered
    slice := slice
    thick := thick
    contained := ?_
    cutoff := T.cutoff
    below := fun a => (belowParent a).trans (T.cutoffs a.parent).le
    marked := L
    marked_positive := hL
    rank := hRank
    backward := ?_
    clean := ?_ }⟩
  · intro a x hx
    have hSub := T.reservoir_antitone (s := []) (List.nil_prefix (l := a.parent))
      (T.family_sub a.parent (inFamily a x hx))
    simpa only [T.root] using hSub
  · intro a b hab y hy
    let F (p : L) := {x ∈ slice a | c (row a, x) (row b, y) = p.1}
    have hF (p : L) : (F p).Countable := by
      have hmem : p.1 ∈ (T.family a.parent).marked := by
        rw [show (T.family a.parent).marked = L from a.tagged]
        exact p.2
      have havoid := ((T.family a.parent).mem_openLabels (row b, y) (chooseSlice a)).mp
        (later a b hab y hy).2 p.1 hmem
      exact Classical.byContradiction havoid
    apply (countable_iUnion hF).mono
    intro x hx
    exact mem_iUnion.mpr ⟨⟨c (row a, x) (row b, y), hx.2⟩, hx.1, rfl⟩
  · intro F
    apply Occurrence.exists_chain dense
    intro t ht htag
    change (T.family t).marked = L at htag
    obtain ⟨n, hn⟩ := T.tests t F
    refine ⟨n, ?_⟩
    intro y hy hyX hyCut p hp
    exact Classical.byContradiction (hn y hy hyX hyCut p (htag.symm ▸ hp))

private theorem exists_zero_stock_of_nested {k : Nat} (c : GridColoring.{u} k)
    (symm : ∀ x y, c x y = c y x) (nested : IsNested c)
    (triangles : ∀ i : Fin k, TriangleFree (gridColorGraph c i.succ)) :
    ∃ A : Stock.{u}, A.carrier.Pairwise (fun x y => c x y = 0) := by
  classical
  by_contra! hNo
  obtain ⟨X, hFull, hInc, _⟩ := exists_full_nested_incidence nested symm hNo
  have hSym : Std.Symm (fun x y => c x y ≠ 0) :=
    ⟨fun x y h hz => h ((symm x y).trans hz)⟩
  have hTriangle (p : Fin (k + 1)) (hp : p ≠ 0) : TriangleFree (gridColorGraph c p) := by
    obtain ⟨i, hi⟩ := (Fin.eq_zero_or_eq_succ p).resolve_left hp
    rw [hi]
    exact triangles i
  have ranked (r : Nat) : ∀ Y : Set Point.{u}, Full Y → Y ⊆ X →
      ∃ M : MarkFamily c X, M.carrier ⊆ Y ∧ r ≤ M.marked.card := by
    induction r with
    | zero =>
      intro Y hY _
      obtain ⟨A, hA⟩ := hY.exists_stock
      obtain ⟨cutoff, hcut⟩ := A.exists_cutoff
      let M := MarkFamily.ofStock A c X cutoff (fun n => (hcut n).le)
      exact ⟨M, hA, Nat.zero_le _⟩
    | succ r ih =>
      intro Y hY hYX
      obtain ⟨T⟩ := exists_pruned_families Y hY hYX ih
      obtain ⟨D⟩ := T.exists_groundCandidates
      exact D.exists_rank_succ symm nested hTriangle hNo
  obtain ⟨M, hM, hRank⟩ := ranked k X hFull Subset.rfl
  exact (Nat.not_lt_of_ge hRank) (M.marked_card_lt hFull hM hInc hSym nested.countable_forward)

/-- For every finite palette, the ordinal square of `ω₁` forces a color-zero
copy of `ω₁ * ω` or a triangle in one of the positive colors. -/
theorem erdos_1171 : Statement.{u} :=
  statement_of_nested_zero (fun _ => exists_zero_stock_of_nested)

end Jsp000976
