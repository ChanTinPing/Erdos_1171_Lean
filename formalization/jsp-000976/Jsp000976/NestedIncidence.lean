module

public import Jsp000976.Incidence
public import Jsp000976.Nested

/-! Apply the full-set incidence lemma to the positive edges of a nested coloring. -/

@[expose] public section

namespace Jsp000976

open Set

universe u

/-- Edges within a single row have color zero in a nested coloring. -/
theorem IsNested.same_row_zero {k : Nat} {c : GridColoring.{u} k} (hNested : IsNested c)
    {x y : Point.{u}} (hrow : x.1 = y.1) : c x y = 0 := by
  by_contra hpos
  exact (hNested x y hrow.le hpos).1.ne hrow

/-- In a later row all positive neighbors of a point lie below its column. -/
theorem IsNested.countable_forward {k : Nat} {c : GridColoring.{u} k} (hNested : IsNested c)
    (x : Point.{u}) (b : Stage.{u}) (hrow : x.1 < b) : {d | c x (b, d) ≠ 0}.Countable :=
  (countable_Iio_stage x.2).mono fun d hd => (hNested x (b, d) hrow.le hd).2.2

/-- A nested symmetric coloring with no zero stock has a full set on which
all thick slices have rich backward incidence outside nonfull exceptions. -/
theorem exists_full_nested_incidence {k : Nat} {c : GridColoring.{u} k}
    (hNested : IsNested c) (hSym : ∀ x y, c x y = c y x)
    (hNo : ∀ A : Stock.{u}, ¬ A.carrier.Pairwise (fun x y => c x y = 0)) :
    ∃ X : Set Point.{u}, Full X ∧ IncidenceProperty (fun x y => c x y ≠ 0) X ∧
      ∀ (a : Stage.{u}) (S : Set Stage.{u}),
        ¬ S.Countable → S ⊆ rowSlice X a →
          ¬ Full (incidenceExceptions (fun x y => c x y ≠ 0) X a S) := by
  have hSym' : Std.Symm (fun x y => c x y ≠ 0) :=
    ⟨fun x y h hz => h ((hSym x y).trans hz)⟩
  obtain ⟨X, hFull, hInc⟩ := exists_full_incidence (fun x y => c x y ≠ 0) hSym'
    (fun x y hrow hpos => hpos (hNested.same_row_zero hrow))
    (by
      intro A hA
      apply hNo A
      intro x hx y hy hne
      exact not_not.mp (hA hx hy hne))
  exact ⟨X, hFull, hInc, fun _ _ hS hsub =>
    hInc.not_full_exceptional hSym' hNested.countable_forward hS hsub⟩

end Jsp000976
