module

public import Jsp000976.Rows
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# One-sided independent stocks and the nested reduction

This is the remainder of §2 of Howe–Huffman–Kohlmeyer–Kruer.
-/

@[expose] public section

namespace Jsp000976

open Set

universe u

def TriangleFree {α : Type*} (G : α → α → Prop) : Prop :=
  ∀ ⦃x y z⦄, G x y → G x z → G y z → False

theorem TriangleFree.pairwise_neighbors {α : Type*} {G : α → α → Prop}
    (hG : TriangleFree G) (x : α) : {y | G x y}.Pairwise (fun y z => ¬ G y z) :=
  fun _ hy _ hz _ h => hG hy hz h

private theorem exists_strictMono_mem {S : Set Nat} (hS : S.Infinite) :
    ∃ f : Nat → Nat, StrictMono f ∧ ∀ n, f n ∈ S := by
  apply Nat.exists_strictMono_subsequence
  intro m
  by_contra! h
  exact hS.not_bddAbove ⟨m, fun i hi => Nat.le_of_not_gt (fun hgt => h i hgt hi)⟩

private theorem exists_strictMono_avoiding (forbid : Nat → Set Nat)
    (hfinite : ∀ i, (forbid i).Finite) :
    ∃ f : Nat → Nat, StrictMono f ∧ ∀ i j, i < j → f j ∉ forbid (f i) := by
  classical
  have hnext (n : Nat) : ∃ m, n < m ∧ ∀ i ≤ n, m ∉ forbid i := by
    have hfin : (⋃ i ∈ Iic n, forbid i).Finite :=
      (finite_Iic n).biUnion fun i _ => hfinite i
    obtain ⟨b, hb⟩ := hfin.bddAbove
    refine ⟨max n b + 1, Nat.lt_succ_of_le (Nat.le_max_left _ _), ?_⟩
    intro i hi h
    have hm := hb (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hi, h⟩⟩)
    exact (Nat.not_succ_le_self (max n b)) (hm.trans (Nat.le_max_right _ _))
  choose next hnext using hnext
  let f : Nat → Nat := Nat.rec 0 (fun _ m => next m)
  have hmono : StrictMono f := strictMono_nat_of_lt_succ fun n => (hnext (f n)).1
  refine ⟨f, hmono, ?_⟩
  intro i j hij
  cases j with
  | zero => exact False.elim (Nat.not_lt_zero _ hij)
  | succ j => exact (hnext (f j)).2 (f i) (hmono.monotone (Nat.le_of_lt_succ hij))

private theorem exists_thick_independent {S : Set Stage.{u}} (hS : ¬ S.Countable)
    (G : Stage.{u} → Stage.{u} → Prop) (hsym : Std.Symm G) (htriangle : TriangleFree G) :
    ∃ T ⊆ S, ¬ T.Countable ∧ T.Pairwise (fun x y => ¬ G x y) := by
  by_cases h : ∃ x ∈ S, ¬ {y ∈ S | G x y}.Countable
  · obtain ⟨x, _, hx⟩ := h
    exact ⟨_, fun _ hy => hy.1, hx,
      (htriangle.pairwise_neighbors x).mono fun _ hy => hy.2⟩
  · push Not at h
    exact exists_uncountable_independent_of_countable_neighbors S hS G hsym h

/-- Backward countable degrees in a triangle-free graph suffice to find
an independent substock. -/
theorem exists_independent_stock_of_backward_countable (A : Stock.{u})
    (G : Point.{u} → Point.{u} → Prop) (hsym : Std.Symm G) (htriangle : TriangleFree G)
    (hback : ∀ i j, i < j → ∀ y ∈ A.slice j,
      {x ∈ A.slice i | G (A.row j, y) (A.row i, x)}.Countable) :
    ∃ B : Stock.{u}, B.carrier ⊆ A.carrier ∧ B.carrier.Pairwise (fun x y => ¬ G x y) := by
  classical
  by_contra! hno
  let N (x : Point.{u}) (i : Nat) := {y ∈ A.slice i | G x (A.row i, y)}
  let thickRows (x : Point.{u}) : Set Nat := {i | ¬ (N x i).Countable}
  have hfinite (x : Point.{u}) : (thickRows x).Finite := by
    by_contra! h
    obtain ⟨f, hf, hmem⟩ := exists_strictMono_mem h
    let B := A.restrict f hf (fun n => N x (f n)) hmem
    exact hno B (A.restrict_subset f hf _ hmem (fun _ _ hy => hy.1))
      ((htriangle.pairwise_neighbors x).mono <| by
        rintro y ⟨i, hi, hy⟩
        change G x y
        have hG : G x (B.row i, y.2) := hy.2
        simpa only [← hi, Prod.eta] using hG)
  let marks (x : Point.{u}) : Finset Nat := (hfinite x).toFinset
  have hmarks (i : Nat) :
      ∃ M : Finset Nat, ¬ {x ∈ A.slice i | marks (A.row i, x) = M}.Countable := by
    obtain ⟨M, hM⟩ := exists_uncountable_fiber (A.thick i)
      (fun x : A.slice i => marks (A.row i, x.1))
    refine ⟨M, fun h => hM ?_⟩
    apply (h.preimage (f := Subtype.val) Subtype.val_injective).mono
    intro x hx
    change x.1 ∈ {x ∈ A.slice i | marks (A.row i, x) = M}
    exact ⟨x.2, hx⟩
  choose mark hmark using hmarks
  obtain ⟨f, hf, havoid⟩ :=
    exists_strictMono_avoiding (fun i => (mark i : Set Nat)) (fun i => (mark i).finite_toSet)
  let S (n : Nat) := {x ∈ A.slice (f n) | marks (A.row (f n), x) = mark (f n)}
  have hS (n : Nat) : ¬ (S n).Countable := hmark (f n)
  have hthin (n : Nat) : ∃ T ⊆ S n, ¬ T.Countable ∧
      T.Pairwise (fun x y => ¬ G (A.row (f n), x) (A.row (f n), y)) :=
    exists_thick_independent (hS n) _ ⟨fun x y => hsym.symm _ _⟩
      (fun ⦃_ _ _⦄ hxy hxz hyz => htriangle hxy hxz hyz)
  choose T hTsub hTthick hTfree using hthin
  let conflict (x y : Σ _ : Nat, Stage.{u}) :=
    G (A.row (f x.1), x.2) (A.row (f y.1), y.2)
  have hconf (i j : Nat) (hij : i ≠ j) (x : Stage.{u}) (hx : x ∈ T i) :
      {y ∈ T j | conflict ⟨i, x⟩ ⟨j, y⟩}.Countable := by
    have hx' := hTsub i hx
    rcases lt_or_gt_of_ne hij with h | h
    · have hm : f j ∉ thickRows (A.row (f i), x) := by
        intro hthick
        apply havoid i j h
        have : f j ∈ marks (A.row (f i), x) := (Set.Finite.mem_toFinset _).2 hthick
        simpa [hx'.2] using this
      have hn : (N (A.row (f i), x) (f j)).Countable := by
        simpa [thickRows] using hm
      apply hn.mono
      intro y hy
      change y ∈ A.slice (f j) ∧ G (A.row (f i), x) (A.row (f j), y)
      exact ⟨(hTsub j hy.1).1, hy.2⟩
    · apply (hback (f j) (f i) (hf h) x hx'.1).mono
      intro y hy
      change y ∈ A.slice (f j) ∧ G (A.row (f i), x) (A.row (f j), y)
      exact ⟨(hTsub j hy.1).1, hy.2⟩
  obtain ⟨U, hU, hUfree⟩ := exists_uncountable_thinning_countable (α := fun _ : Nat => Stage.{u})
    T hTthick conflict ⟨fun x y => hsym.symm _ _⟩ hconf
  let B := A.restrict f hf U (fun i => (hU i).2)
  have hsub (i : Nat) : U i ⊆ A.slice (f i) :=
    fun _ hi => (hTsub i ((hU i).1 hi)).1
  refine hno B (A.restrict_subset f hf U (fun i => (hU i).2) hsub) ?_
  rintro x ⟨i, hxi, hx⟩ y ⟨j, hyj, hy⟩ hxy hG
  change x.1 = A.row (f i) at hxi
  change y.1 = A.row (f j) at hyj
  by_cases he : i = j
  · subst j
    apply hTfree i ((hU i).1 hx) ((hU i).1 hy) _ _
    · exact fun h => hxy (Prod.ext (hxi.trans hyj.symm) h)
    · have hex : (A.row (f i), x.2) = x := Prod.ext hxi.symm rfl
      have hey : (A.row (f i), y.2) = y := Prod.ext hyj.symm rfl
      rw [hex, hey]
      exact hG
  · apply hUfree i j he _ hx _ hy
    simpa only [conflict, ← hxi, ← hyj, Prod.eta] using hG

abbrev GridColoring (k : Nat) := Point.{u} → Point.{u} → Fin (k + 1)

def gridColorGraph {k : Nat} (c : GridColoring.{u} k) (i : Fin (k + 1)) :
    Point.{u} → Point.{u} → Prop :=
  fun x y => x ≠ y ∧ c x y = i

def NestedEdge (x y : Point.{u}) : Prop :=
  x.1 < y.1 ∧ y.1 < y.2 ∧ y.2 < x.2

def IsNested {k : Nat} (c : GridColoring.{u} k) : Prop :=
  ∀ x y, x.1 ≤ y.1 → c x y ≠ 0 → NestedEdge x y

noncomputable def nestColoring {k : Nat} (c : GridColoring.{u} k) : GridColoring.{u} k := by
  classical
  exact fun x y => if NestedEdge x y ∨ NestedEdge y x then c x y else 0

theorem nestColoring_nested {k : Nat} (c : GridColoring.{u} k) : IsNested (nestColoring c) := by
  classical
  intro x y hrow hpos
  by_contra hx
  have hy : ¬ NestedEdge y x := fun hy => (not_lt_of_ge hrow) hy.1
  exact hpos (by simp [nestColoring, hx, hy])

theorem nestColoring_symmetric {k : Nat} {c : GridColoring.{u} k}
    (hsym : ∀ x y, c x y = c y x) : ∀ x y, nestColoring c x y = nestColoring c y x := by
  classical
  intro x y
  by_cases hxy : NestedEdge x y
  · simp [nestColoring, hxy, hsym x y]
  · by_cases hyx : NestedEdge y x <;> simp [nestColoring, hxy, hyx, hsym x y]

theorem nestColoring_preserves_triangleFree {k : Nat} {c : GridColoring.{u} k}
    (h : ∀ i : Fin k, TriangleFree (gridColorGraph c i.succ)) :
    ∀ i : Fin k, TriangleFree (gridColorGraph (nestColoring c) i.succ) := by
  classical
  have hsub (i : Fin k) (x y : Point.{u}) :
      gridColorGraph (nestColoring c) i.succ x y → gridColorGraph c i.succ x y := by
    rintro ⟨hne, hxy⟩
    refine ⟨hne, ?_⟩
    change (if NestedEdge x y ∨ NestedEdge y x then c x y else 0) = i.succ at hxy
    split at hxy
    · exact hxy
    · exact False.elim (i.succ_ne_zero hxy.symm)
  intro i x y z hxy hxz hyz
  exact h i (hsub i x y hxy) (hsub i x z hxz) (hsub i y z hyz)

private theorem exists_stock_avoiding_palette {k : Nat} (A : Stock.{u}) (c : GridColoring.{u} k)
    (hsym : ∀ x y, c x y = c y x)
    (htriangle : ∀ i : Fin k, TriangleFree (gridColorGraph c i.succ))
    (hback : ∀ x ∈ A.carrier, ∀ y ∈ A.carrier, x.1 < y.1 → c y x ≠ 0 → x.2 ≤ y.2)
    (colors : Finset (Fin k)) :
    ∃ B : Stock.{u}, B.carrier ⊆ A.carrier ∧
      B.carrier.Pairwise (fun x y => ∀ i ∈ colors, c x y ≠ i.succ) := by
  classical
  induction colors using Finset.induction_on with
  | empty => exact ⟨A, Subset.rfl, fun _ _ _ _ _ _ hi => False.elim (Finset.notMem_empty _ hi)⟩
  | @insert i colors hi ih =>
    obtain ⟨B, hBA, hB⟩ := ih
    let G := gridColorGraph c i.succ
    have hG : Std.Symm G := ⟨fun x y h => ⟨h.1.symm, (hsym y x).trans h.2⟩⟩
    have hthin (m n : Nat) (hmn : m < n) (y : Stage.{u}) (hy : y ∈ B.slice n) :
        {x ∈ B.slice m | G (B.row n, y) (B.row m, x)}.Countable :=
      (countable_Iic_stage y).mono <| by
        intro x hx
        exact hback _ (hBA (B.mem_carrier m hx.1)) _ (hBA (B.mem_carrier n hy))
          (B.increasing hmn) (hx.2.2 ▸ i.succ_ne_zero)
    obtain ⟨D, hDB, hD⟩ := exists_independent_stock_of_backward_countable B G hG (htriangle i) hthin
    refine ⟨D, hDB.trans hBA, ?_⟩
    intro x hx y hy hne j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact fun h => hD hx hy hne ⟨hne, h⟩
    · exact hB (hDB hx) (hDB hy) hne j hj

/-- A zero stock for the nested recoloring yields a zero stock for the original
coloring if the positive colors are triangle-free. -/
theorem exists_zero_stock_of_nested_zero_stock {k : Nat} {c : GridColoring.{u} k}
    (hsym : ∀ x y, c x y = c y x)
    (htriangle : ∀ i : Fin k, TriangleFree (gridColorGraph c i.succ))
    (A : Stock.{u}) (hA : A.carrier.Pairwise (fun x y => nestColoring c x y = 0)) :
    ∃ B : Stock.{u}, B.carrier ⊆ A.carrier ∧
      B.carrier.Pairwise (fun x y => c x y = 0) := by
  classical
  let S (n : Nat) := A.slice n ∩ Ioi (A.row n)
  have hS (n : Nat) : ¬ (S n).Countable := by
    intro h
    apply A.thick n
    apply (h.union (countable_Iic_stage (A.row n))).mono
    intro x hx
    rcases le_or_gt x (A.row n) with hl | hg
    · exact Or.inr hl
    · exact Or.inl ⟨hx, hg⟩
  let D := A.restrict id strictMono_id S hS
  have hDA : D.carrier ⊆ A.carrier :=
    A.restrict_subset id strictMono_id S hS (fun _ _ hx => hx.1)
  have hback (x : Point.{u}) (hx : x ∈ D.carrier) (y : Point.{u}) (hy : y ∈ D.carrier)
      (hrow : x.1 < y.1) (hpos : c y x ≠ 0) : x.2 ≤ y.2 := by
    by_contra! hcol
    have hyy : y.1 < y.2 := by
      obtain ⟨n, hrow, hy⟩ := hy
      exact hrow ▸ hy.2
    have hnest : NestedEdge x y := ⟨hrow, hyy, hcol⟩
    have hne : y ≠ x := fun h => (ne_of_gt hrow) (congrArg Prod.fst h)
    apply hpos
    have hz := hA (hDA hy) (hDA hx) hne
    simpa [nestColoring, hnest] using hz
  obtain ⟨B, hBD, hB⟩ := exists_stock_avoiding_palette D c hsym htriangle hback Finset.univ
  refine ⟨B, hBD.trans hDA, ?_⟩
  intro x hx y hy hne
  rcases Fin.eq_zero_or_eq_succ (c x y) with h | ⟨i, hi⟩
  · exact h
  · exact False.elim (hB hx hy hne i (Finset.mem_univ i) hi)

end Jsp000976
