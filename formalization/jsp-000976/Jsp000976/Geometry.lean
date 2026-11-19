module

public import Jsp000976.Rows
public import Jsp000976.Statement

/-!
# From rows to ordinal witnesses

A stock with increasing rows and uncountable slices has inherited order type
`ω₁ * ω` in the lexicographic grid of order type `ω₁ ^ 2`.
-/

@[expose] public section

namespace Jsp000976

open Set Cardinal Ordinal

universe u

/-- The grid order compares rows first and columns second. -/
abbrev pointLex : Point.{u} → Point.{u} → Prop := Prod.Lex (· < ·) (· < ·)

private theorem stage_type : typeLT Stage.{u} = ω₁ := by
  change typeLT (ℵ₁ : Cardinal.{u}).ord.ToType = ω₁
  rw [type_toType, Cardinal.ord_aleph]

/-- An uncountable set of countable ordinals has the same inherited order type
as the entire first uncountable ordinal. -/
theorem thickSlice_type {S : Set Stage.{u}} (hS : ¬ S.Countable) : typeLT S = ω₁ := by
  apply le_antisymm ((type_set_le S).trans_eq stage_type)
  rw [← Cardinal.ord_aleph, Cardinal.ord_le, Ordinal.card_type]
  exact le_of_not_gt fun h => hS (le_aleph0_iff_set_countable.mp (lt_aleph_one_iff.mp h))

private noncomputable def sliceIso (A : Stock.{u}) (n : ℕ) :
    ((· < ·) : Stage.{u} → Stage.{u} → Prop) ≃r ((· < ·) : A.slice n → A.slice n → Prop) :=
  Classical.choice (Ordinal.type_eq.mp (stage_type.trans (thickSlice_type (A.thick n)).symm))

/-- The order type of the lexicographic grid is `ω₁ ^ 2`. -/
theorem pointLex_type : Ordinal.type pointLex.{u} = SourceOrdinal.{u} := by
  change Ordinal.type (Prod.Lex ((· < ·) : Stage.{u} → Stage.{u} → Prop) (· < ·)) = ω₁ ^ 2
  rw [Ordinal.type_prod_lex, stage_type, pow_two]

/-- The row-first, column-second lexicographic grid represents the ordinal square. -/
noncomputable def pointOrdinalIso :
    pointLex.{u} ≃r ((· < ·) : SourceOrdinal.{u}.ToType → SourceOrdinal.{u}.ToType → Prop) :=
  Classical.choice (Ordinal.type_eq.mp (pointLex_type.trans (type_toType _).symm))

private noncomputable def stockMap (A : Stock.{u}) (p : ULift.{u} ℕ × Stage.{u}) : A.carrier :=
  ⟨(A.row p.1.down, (sliceIso A p.1.down p.2).1), A.mem_carrier _ (sliceIso A p.1.down p.2).2⟩

private theorem stockMap_bijective (A : Stock.{u}) : Function.Bijective (stockMap A) := by
  constructor
  · rintro ⟨⟨n⟩, x⟩ ⟨⟨m⟩, y⟩ h
    have hrow : A.row n = A.row m := congrArg (fun p : A.carrier => p.1.1) h
    have hnm : n = m := A.increasing.injective hrow
    subst m
    have hcol : (sliceIso A n x).1 = (sliceIso A n y).1 :=
      congrArg (fun p : A.carrier => p.1.2) h
    have hxy : x = y := (sliceIso A n).injective (Subtype.ext hcol)
    subst y
    rfl
  · rintro ⟨⟨row, col⟩, n, hn, hcol⟩
    change row = A.row n at hn
    subst row
    refine ⟨(ULift.up n, (sliceIso A n).symm ⟨col, hcol⟩), ?_⟩
    apply Subtype.ext
    change (A.row n, ((sliceIso A n) ((sliceIso A n).symm ⟨col, hcol⟩)).1) = (A.row n, col)
    rw [RelIso.apply_symm_apply]

private noncomputable def stockLexIso (A : Stock.{u}) :
    Prod.Lex ((· < ·) : ULift.{u} ℕ → ULift.{u} ℕ → Prop)
      ((· < ·) : Stage.{u} → Stage.{u} → Prop) ≃r Subrel pointLex (· ∈ A.carrier) where
  toEquiv := Equiv.ofBijective (stockMap A) (stockMap_bijective A)
  map_rel_iff' := by
    rintro ⟨⟨n⟩, x⟩ ⟨⟨m⟩, y⟩
    change Prod.Lex (· < ·) (· < ·)
        (A.row n, (sliceIso A n x).1) (A.row m, (sliceIso A m y).1) ↔
      Prod.Lex (· < ·) (· < ·) (ULift.up n, x) (ULift.up m, y)
    rw [Prod.lex_def, Prod.lex_def]
    simp only [ULift.up_lt, ULift.up_inj]
    rw [A.increasing.lt_iff_lt, A.increasing.injective.eq_iff]
    apply or_congr_right
    by_cases h : n = m
    · subst m
      simpa using (sliceIso A n).map_rel_iff (a := x) (b := y)
    · simp only [h, false_and]

/-- The image of a stock in the ordinal square has inherited order type `ω₁ * ω`. -/
theorem stock_image_type (A : Stock.{u}) :
    typeLT (pointOrdinalIso '' A.carrier) = TargetOrdinal.{u} := by
  let e : Subrel pointLex (· ∈ A.carrier) ≃r
      ((· < ·) : (pointOrdinalIso '' A.carrier) → (pointOrdinalIso '' A.carrier) → Prop) :=
    ⟨pointOrdinalIso.toEquiv.image A.carrier, fun {x y} =>
      (pointOrdinalIso.map_rel_iff (a := x.1) (b := y.1))⟩
  rw [← (stockLexIso A |>.trans e).ordinalType_congr, Ordinal.type_prod_lex,
    stage_type, Ordinal.type_lt_ulift, Ordinal.type_nat_lt, Ordinal.lift_omega0, TargetOrdinal]

/-- The conclusion in row coordinates uses a stock as the witness for color zero. -/
def GridPartition (k : ℕ) : Prop :=
  ∀ c : EdgeColoring Point.{u} k,
    (∃ A : Stock.{u}, Homogeneous c 0 A.carrier) ∨
      ∃ i : Fin k, ∃ s : Set Point.{u}, Homogeneous c i.succ s ∧ #s = 3

/-- A monochromatic three-element set is equivalent to three distinct vertices
with all three edges of the specified color. -/
theorem homogeneous_three_iff {α : Type u} {C : Type*} {c : Sym2 α → C} {i : C} :
    (∃ s : Set α, Homogeneous c i s ∧ #s = 3) ↔
      ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        c s(x, y) = i ∧ c s(x, z) = i ∧ c s(y, z) = i := by
  constructor
  · rintro ⟨S, hS, hcard⟩
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := cardinal_three_iff.mp hcard
    exact ⟨x, y, z, hxy, hxz, hyz,
      hS x (by simp) y (by simp) hxy, hS x (by simp) z (by simp) hxz,
      hS y (by simp) z (by simp) hyz⟩
  · rintro ⟨x, y, z, hxy, hxz, hyz, h1, h2, h3⟩
    refine ⟨{x, y, z}, ?_, cardinal_three_iff.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩⟩
    intro a ha b hb hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first | exact (hne rfl).elim | assumption | rwa [Sym2.eq_swap]

/-- Transfer a proof on symmetric maps of ordered grid points to unordered
edges. The positive branch can be given as three explicit vertices. -/
theorem gridPartition_of_symmetric {k : ℕ}
    (h : ∀ c : Point.{u} → Point.{u} → Fin (k + 1), (∀ x y, c x y = c y x) →
      (∃ A : Stock.{u}, ∀ x ∈ A.carrier, ∀ y ∈ A.carrier, x ≠ y → c x y = 0) ∨
        ∃ i : Fin k, ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
          c x y = i.succ ∧ c x z = i.succ ∧ c y z = i.succ) : GridPartition.{u} k := by
  intro c
  rcases h (fun x y => c s(x, y)) (fun _ _ => congrArg c Sym2.eq_swap) with h0 | ⟨i, hpos⟩
  · exact Or.inl h0
  · exact Or.inr ⟨i, homogeneous_three_iff.mpr hpos⟩

private theorem homogeneous_image {k : ℕ} (c : EdgeColoring SourceOrdinal.{u}.ToType k)
    (i : Fin (k + 1)) (s : Set Point.{u})
    (h : Homogeneous (c ∘ Sym2.map pointOrdinalIso) i s) :
    Homogeneous c i (pointOrdinalIso '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  exact h x hx y hy (fun he => hxy (congrArg pointOrdinalIso he))

/-- Proving the row-coordinate conclusion for every finite palette proves the original statement. -/
theorem statement_of_grid (h : ∀ k : ℕ, GridPartition.{u} k) : Statement.{u} := by
  intro k c
  rcases h k (c ∘ Sym2.map pointOrdinalIso) with ⟨A, hA⟩ | ⟨i, s, hs, hcard⟩
  · exact Or.inl ⟨pointOrdinalIso '' A.carrier, homogeneous_image c 0 A.carrier hA, stock_image_type A⟩
  · refine Or.inr ⟨i, pointOrdinalIso '' s, homogeneous_image c i.succ s hs, ?_⟩
    rwa [Cardinal.mk_image_eq pointOrdinalIso.injective]

end Jsp000976
