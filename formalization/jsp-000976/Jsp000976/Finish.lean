module

public import Jsp000976.Geometry
public import Jsp000976.Nested

/-!
# Reduction from the original ordinal partition relation to nested colorings
-/

@[expose] public section

namespace Jsp000976

universe u

/-- The all-palette grid statement follows from the zero-stock claim for
nested colorings with no positive monochromatic triangle. -/
theorem statement_of_nested_zero
    (h : ∀ (k : Nat) (c : GridColoring.{u} k), (∀ x y, c x y = c y x) →
      IsNested c → (∀ i : Fin k, TriangleFree (gridColorGraph c i.succ)) →
      ∃ A : Stock.{u}, A.carrier.Pairwise (fun x y => c x y = 0)) :
    Statement.{u} := by
  apply statement_of_grid
  intro k
  apply gridPartition_of_symmetric
  intro c hsym
  by_cases ht : ∃ i : Fin k, ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      c x y = i.succ ∧ c x z = i.succ ∧ c y z = i.succ
  · exact Or.inr ht
  · have htri (i : Fin k) : TriangleFree (gridColorGraph c i.succ) := by
      intro x y z hxy hxz hyz
      exact ht ⟨i, x, y, z, hxy.1, hxz.1, hyz.1, hxy.2, hxz.2, hyz.2⟩
    obtain ⟨A, hA⟩ := h k (nestColoring c) (nestColoring_symmetric hsym)
      (nestColoring_nested c) (nestColoring_preserves_triangleFree htri)
    obtain ⟨B, _, hB⟩ := exists_zero_stock_of_nested_zero_stock hsym htri A hA
    exact Or.inl ⟨B, hB⟩

end Jsp000976
