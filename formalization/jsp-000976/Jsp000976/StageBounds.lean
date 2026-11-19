module

public import Jsp000976.Rows
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

namespace Jsp000976

open Set Cardinal

universe u

/-- Every countable set of countable ordinals has a strict upper bound among the countable ordinals. -/
theorem exists_stage_above_countable {S : Set Stage.{u}} (hS : S.Countable) :
    ∃ γ : Stage.{u}, ∀ x ∈ S, x < γ := by
  apply not_isCofinal_iff.mp
  intro hcofinal
  have hcof : Order.cof Stage.{u} = ℵ₁ := by
    change Order.cof (ℵ₁ : Cardinal.{u}).ord.ToType = ℵ₁
    rw [Ordinal.cof_toType, isRegular_aleph_one.cof_ord]
  have h := (Order.cof_le hcofinal).trans (le_aleph0_iff_set_countable.mpr hS)
  exact (not_le_of_gt aleph0_lt_aleph_one) (hcof ▸ h)

/-- A single cutoff strictly bounds all stages in a countably indexed family. -/
theorem countable_bounded_stage {ι : Type*} [Countable ι] (f : ι → Stage.{u}) :
    ∃ γ : Stage.{u}, ∀ i, f i < γ := by
  obtain ⟨γ, hγ⟩ := exists_stage_above_countable (countable_range f)
  exact ⟨γ, fun i => hγ _ (mem_range_self _)⟩

/-- The rows of any stock lie below a fixed countable ordinal. -/
theorem Stock.exists_cutoff (A : Stock.{u}) : ∃ γ : Stage.{u}, ∀ n, A.row n < γ :=
  countable_bounded_stage A.row

/-- The grid of countable ordinals has cardinality `ℵ₁`. -/
theorem cardinal_point : #(Point.{u}) = ℵ₁ := by
  change #(Stage.{u} × Stage.{u}) = ℵ₁
  simp only [mk_prod, lift_id]
  change #((ℵ₁ : Cardinal.{u}).ord.ToType) * #((ℵ₁ : Cardinal.{u}).ord.ToType) = ℵ₁
  rw [mk_ord_toType, mul_eq_self aleph0_lt_aleph_one.le]

private noncomputable def finiteSubsetEquiv (α : Type u) :
    {s : Set α // s.Finite} ≃ Finset α where
  toFun s := s.2.toFinset
  invFun t := ⟨t, t.finite_toSet⟩
  left_inv s := Subtype.ext s.2.coe_toFinset
  right_inv t := Finset.coe_injective (Set.Finite.coe_toFinset t.finite_toSet)

/-- There are `ℵ₁` finite sets of grid points. -/
theorem cardinal_finite_point_subsets : #({s : Set Point.{u} // s.Finite}) = ℵ₁ := by
  let : Infinite Point.{u} := aleph0_le_mk_iff.mp (cardinal_point ▸ aleph0_lt_aleph_one.le)
  rw [mk_congr (finiteSubsetEquiv _), mk_finset_of_infinite, cardinal_point]

/-- Finite subsets of a countable type form a countable type. -/
theorem countable_finite_subsets {α : Type u} [Countable α] : Countable {s : Set α // s.Finite} :=
  (finiteSubsetEquiv α).injective.countable

end Jsp000976
