module

public import Jsp000976.PaletteMarks
public import Jsp000976.Rows
import Mathlib.Data.Finset.Prod

/-!
# Marked families of thick slices

A family has countably many labels. Labels can select the same physical row,
while a later compatible occurrence will use a strictly later row.
-/

@[expose] public section

namespace Jsp000976

open Set

universe u

/-- A countably indexed family of thick slices with small marked-color fibers. -/
structure MarkFamily {k : Nat} (c : Point.{u} → Point.{u} → Fin (k + 1))
    (X : Set Point.{u}) where
  labels : Type
  countable : Countable labels
  row : labels → Stage.{u}
  slice : labels → Set Stage.{u}
  thick : ∀ i, ¬ (slice i).Countable
  ideal : RowIdeal labels
  marked : Finset (Fin (k + 1))
  marked_positive : ∀ p ∈ marked, p ≠ 0
  cutoff : Stage.{u}
  row_le_cutoff : ∀ i, row i ≤ cutoff
  marks_small : ∀ y ∈ X, cutoff < y.1 → ∀ p ∈ marked,
    ideal.small {i | ¬ {x ∈ slice i | c (row i, x) y = p}.Countable}

namespace MarkFamily

variable {k : Nat} {c : Point.{u} → Point.{u} → Fin (k + 1)} {X : Set Point.{u}}

def carrier (M : MarkFamily c X) : Set Point.{u} :=
  {x | ∃ i, x.1 = M.row i ∧ x.2 ∈ M.slice i}

theorem mem_carrier (M : MarkFamily c X) (i : M.labels) {x : Stage.{u}}
    (hx : x ∈ M.slice i) : (M.row i, x) ∈ M.carrier :=
  ⟨i, rfl, hx⟩

/-- The stock consisting of an increasing sequence of rows supplies the
initial marked family with no marked colors. -/
def ofStock (A : Stock.{u})
    (c : Point.{u} → Point.{u} → Fin (k + 1)) (X : Set Point.{u})
    (cutoff : Stage.{u}) (hcutoff : ∀ n, A.row n ≤ cutoff) : MarkFamily c X where
  labels := Nat
  countable := inferInstance
  row := A.row
  slice := A.slice
  thick := A.thick
  ideal := RowIdeal.finite
  marked := ∅
  marked_positive _ hp := (Finset.notMem_empty _ hp).elim
  cutoff := cutoff
  row_le_cutoff := hcutoff
  marks_small _ _ _ _ hp := (Finset.notMem_empty _ hp).elim

theorem carrier_ofStock (A : Stock.{u})
    (c : Point.{u} → Point.{u} → Fin (k + 1)) (X : Set Point.{u})
    (cutoff : Stage.{u}) (hcutoff : ∀ n, A.row n ≤ cutoff) :
    (ofStock A c X cutoff hcutoff).carrier = A.carrier := rfl

def markSet (M : MarkFamily c X) (y : Point.{u}) (p : Fin (k + 1)) : Set M.labels :=
  {i | ¬ {x ∈ M.slice i | c (M.row i, x) y = p}.Countable}

def openLabels (M : MarkFamily c X) (y : Point.{u}) : Set M.labels :=
  (RowIdeal.coveredByMarks (M.markSet y) M.marked)ᶜ

theorem openLabels_positive (M : MarkFamily c X) (y : Point.{u})
    (hy : y ∈ X) (hcut : M.cutoff < y.1) : ¬ M.ideal.small (M.openLabels y) := by
  have h := M.ideal.diff_not_small M.ideal.univ_not_small <|
    M.ideal.coveredByMarks_small (M.markSet y) M.marked (M.marks_small y hy hcut)
  simpa [openLabels, Set.compl_eq_univ_sdiff] using h

theorem mem_openLabels (M : MarkFamily c X) (y : Point.{u}) (i : M.labels) :
    i ∈ M.openLabels y ↔ ∀ p ∈ M.marked, i ∉ M.markSet y p := by
  classical
  simp [openLabels, RowIdeal.coveredByMarks]

theorem exists_thick_positive_color (M : MarkFamily c X) (y : Point.{u}) (i : M.labels)
    (h : ¬ {x ∈ M.slice i | c (M.row i, x) y ≠ 0}.Countable) :
    ∃ p : Fin (k + 1), p ≠ 0 ∧ i ∈ M.markSet y p := by
  classical
  by_contra he
  have hEach (p : {p : Fin (k + 1) // p ≠ 0}) :
      {x ∈ M.slice i | c (M.row i, x) y = p.1}.Countable := by
    by_contra hCount
    exact he ⟨p.1, p.2, hCount⟩
  apply h
  refine (Set.countable_iUnion hEach).mono ?_
  intro x hx
  exact Set.mem_iUnion.mpr ⟨⟨c (M.row i, x) y, hx.2⟩, hx.1, rfl⟩

theorem exists_unmarked_color (M : MarkFamily c X)
    (y : Point.{u}) (hy : y ∈ X) (hcut : M.cutoff < y.1)
    (hRich : ∀ i, ¬ {x ∈ M.slice i | c (M.row i, x) y ≠ 0}.Countable) :
    ∃ p : Fin (k + 1), p ≠ 0 ∧ p ∉ M.marked ∧
      ¬ M.ideal.small (M.openLabels y ∩ M.markSet y p) := by
  classical
  let available := Finset.univ.filter fun p : Fin (k + 1) => p ≠ 0 ∧ p ∉ M.marked
  let markedFiber (p : Fin (k + 1)) := M.openLabels y ∩ M.markSet y p
  have cover : M.openLabels y ⊆ RowIdeal.coveredByMarks markedFiber available := by
    intro i hi
    obtain ⟨p, hp0, hpi⟩ := M.exists_thick_positive_color y i (hRich i)
    have hpMark : p ∉ M.marked := fun hp => (M.mem_openLabels y i).mp hi p hp hpi
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp0, hpMark⟩, hi, hpi⟩
  obtain ⟨p, hp, hFiber⟩ :=
    M.ideal.exists_positive_mark markedFiber available (M.openLabels_positive y hy hcut) cover
  have hp' := (Finset.mem_filter.mp hp).2
  exact ⟨p, hp'.1, hp'.2, hFiber⟩

theorem exists_avoiding_finite_tests (M : MarkFamily c X)
    (D : Set M.labels) (hD : ¬ M.ideal.small D)
    (F : Finset Point.{u}) (hF : ∀ y ∈ F, y ∈ X ∧ M.cutoff < y.1) :
    ∃ i ∈ D, ∀ y ∈ F, ∀ p ∈ M.marked, i ∉ M.markSet y p := by
  classical
  let marks (pair : Point.{u} × Fin (k + 1)) := M.markSet pair.1 pair.2
  let cover := RowIdeal.coveredByMarks marks (F.product M.marked)
  have hcover : M.ideal.small cover := by
    apply M.ideal.coveredByMarks_small
    intro pair hpair
    have hp := Finset.mem_product.mp hpair
    exact M.marks_small pair.1 (hF _ hp.1).1 (hF _ hp.1).2 pair.2 hp.2
  have hD' := M.ideal.diff_not_small hD hcover
  obtain ⟨i, hi⟩ : (D \ cover).Nonempty := by
    by_contra! h
    exact hD' (M.ideal.finite_small (by simp [h]))
  refine ⟨i, hi.1, fun y hy p hp hap => hi.2 ?_⟩
  exact ⟨(y, p), Finset.mem_product.mpr ⟨hy, hp⟩, hap⟩

end MarkFamily

end Jsp000976
