module

public import Jsp000976.Nested
public import Jsp000976.PaletteMarks

/-!
# Compatible slices and their palette

Only pairs of labels on a common path contribute to the palette. A positive
label set contains such a path, which turns an empty palette into a zero stock.
-/

@[expose] public section

namespace Jsp000976

open Set

universe u

variable {ι : Type}

def Compatible (before : ι → ι → Prop) (i j : ι) : Prop :=
  before i j ∨ before j i

/-- Countable-conflict thinning across all tree occurrences, with conflicts
only between labels that can occur on the same path. -/
theorem exists_compatible_thinning [Countable ι] {k : Nat}
    (c : GridColoring.{u} k) (symm : ∀ x y, c x y = c y x) (nested : IsNested c)
    (before : ι → ι → Prop) (row : ι → Stage.{u}) (hrow : ∀ i j, before i j → row i < row j)
    (S : ι → Set Stage.{u}) (thick : ∀ i, ¬ (S i).Countable)
    (L : Finset (Fin (k + 1))) (hL : ∀ p ∈ L, p ≠ 0)
    (back : ∀ i j, before i j → ∀ y ∈ S j,
       {x ∈ S i | c (row i, x) (row j, y) ∈ L}.Countable) :
    ∃ T : ι → Set Stage.{u}, (∀ i, T i ⊆ S i ∧ ¬ (T i).Countable) ∧
      ∀ i j, Compatible before i j → ∀ x ∈ T i, ∀ y ∈ T j, c (row i, x) (row j, y) ∉ L := by
  let R (x y : Σ _ : ι, Stage.{u}) :=
    Compatible before x.1 y.1 ∧ c (row x.1, x.2) (row y.1, y.2) ∈ L
  have hSymm : Std.Symm R := ⟨fun x y h => ⟨h.1.symm,
    (symm (row x.1, x.2) (row y.1, y.2)) ▸ h.2⟩⟩
  have hdegree (i j : ι) (_ : i ≠ j) (x : Stage.{u}) (hx : x ∈ S i) :
      {y ∈ S j | R ⟨i, x⟩ ⟨j, y⟩}.Countable := by
    by_cases h : before i j
    · exact (countable_Iio_stage x).mono <| by
        intro y hy
        exact (nested (row i, x) (row j, y) (hrow i j h).le (hL _ hy.2.2)).2.2
    · by_cases h' : before j i
      · apply (back j i h' x hx).mono
        intro y hy
        exact ⟨hy.1, (symm (row i, x) (row j, y)) ▸ hy.2.2⟩
      · exact countable_empty.mono fun y hy => (hy.2.1.elim h h').elim
  obtain ⟨T, hT, hfree⟩ := exists_uncountable_thinning_countable
    (α := fun _ : ι => Stage.{u}) S thick R hSymm hdegree
  refine ⟨T, hT, ?_⟩
  intro i j hij x hx y hy hc
  have hne : i ≠ j := by
    rintro rfl
    rcases hij with h | h <;> exact (lt_irrefl _) (hrow i i h)
  exact hfree i j hne x hx y hy ⟨hij, hc⟩

/-- Uncountable slices on a specified set of labels. -/
structure IndexedSlices (ι : Type) where
  active : Set ι
  cols : ι → Set Stage.{u}
  thick : ∀ i ∈ active, ¬ (cols i).Countable

namespace IndexedSlices

variable {k : Nat} (row : ι → Stage.{u}) (c : GridColoring.{u} k)
variable (before : ι → ι → Prop)

def Refines (B A : IndexedSlices.{u} ι) : Prop :=
  B.active ⊆ A.active ∧ ∀ i ∈ B.active, B.cols i ⊆ A.cols i

theorem Refines.refl (A : IndexedSlices.{u} ι) : Refines A A :=
  ⟨Subset.rfl, fun _ _ => Subset.rfl⟩

theorem Refines.trans {A B C : IndexedSlices.{u} ι}
    (hAB : Refines A B) (hBC : Refines B C) : Refines A C :=
  ⟨hAB.1.trans hBC.1, fun i hi => (hAB.2 i hi).trans (hBC.2 i (hAB.1 hi))⟩

def mark (A : IndexedSlices.{u} ι) (y : Point.{u}) (p : Fin (k + 1)) : Set ι :=
  {i ∈ A.active | ¬ {x ∈ A.cols i | c (row i, x) y = p}.Countable}

theorem mark_mono {B A : IndexedSlices.{u} ι} (hBA : Refines B A)
    (y : Point.{u}) (p : Fin (k + 1)) : B.mark row c y p ⊆ A.mark row c y p := by
  intro i hi
  refine ⟨hBA.1 hi.1, fun h => hi.2 (h.mono ?_)⟩
  intro x hx
  exact ⟨hBA.2 i hi.1 hx.1, hx.2⟩

noncomputable def palette (A : IndexedSlices.{u} ι) : Finset (Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun p =>
    p ≠ 0 ∧ ∃ i ∈ A.active, ∃ j ∈ A.active, Compatible before i j ∧
      ∃ x ∈ A.cols i, ∃ y ∈ A.cols j, c (row i, x) (row j, y) = p

theorem mem_palette (A : IndexedSlices.{u} ι) (p : Fin (k + 1)) :
    p ∈ A.palette row c before ↔
    p ≠ 0 ∧ ∃ i ∈ A.active, ∃ j ∈ A.active, Compatible before i j ∧
      ∃ x ∈ A.cols i, ∃ y ∈ A.cols j, c (row i, x) (row j, y) = p := by
  classical
  simp [palette]

theorem palette_mono {B A : IndexedSlices.{u} ι} (hBA : Refines B A) :
    B.palette row c before ⊆ A.palette row c before := by
  intro p hp
  obtain ⟨hp0, i, hi, j, hj, hr, x, hx, y, hy, hxy⟩ := (B.mem_palette row c before p).mp hp
  exact (A.mem_palette row c before p).mpr
    ⟨hp0, i, hBA.1 hi, j, hBA.1 hj, hr, x, hBA.2 i hi hx, y, hBA.2 j hj hy, hxy⟩

theorem exists_zero_stock_of_palette_empty (A : IndexedSlices.{u} ι)
    (hrow : ∀ i j, before i j → row i < row j) (nested : IsNested c)
    (f : Nat → ι) (hf : ∀ n, f n ∈ A.active)
    (hchain : ∀ n m, n < m → before (f n) (f m))
    (hp : ¬ (A.palette row c before).Nonempty) :
    ∃ B : Stock.{u}, B.carrier.Pairwise (fun x y => c x y = 0) := by
  let B : Stock.{u} :=
    ⟨row ∘ f, fun n m h => hrow _ _ (hchain n m h), A.cols ∘ f, fun n => A.thick _ (hf n)⟩
  refine ⟨B, ?_⟩
  rintro x ⟨n, hxn, hx⟩ y ⟨m, hym, hy⟩ _
  by_contra hc
  have hxn' : x.1 = row (f n) := hxn
  have hym' : y.1 = row (f m) := hym
  rcases lt_trichotomy n m with hn | he | hm
  · have hxy : c (row (f n), x.2) (row (f m), y.2) = c x y := by
      rw [← hxn', ← hym', Prod.eta, Prod.eta]
    exact hp ⟨c x y, (A.mem_palette row c before (c x y)).mpr
      ⟨hc, f n, hf n, f m, hf m, Or.inl (hchain n m hn), x.2, hx, y.2, hy, hxy⟩⟩
  · subst m
    have hr : x.1 = y.1 := hxn'.trans hym'.symm
    exact (lt_irrefl _) (hr ▸ (nested x y hr.le hc).1)
  · have hxy : c (row (f n), x.2) (row (f m), y.2) = c x y := by
      rw [← hxn', ← hym', Prod.eta, Prod.eta]
    exact hp ⟨c x y, (A.mem_palette row c before (c x y)).mpr
      ⟨hc, f n, hf n, f m, hf m, Or.inr (hchain m n hm), x.2, hx, y.2, hy, hxy⟩⟩

/-- A positive refinement of the compatible family increases the set of
marked colors. Data on the chosen active label set are returned explicitly. -/
theorem exists_larger_marked_palette (A : IndexedSlices.{u} ι) (J : RowIdeal ι)
    (hA : ¬ J.small A.active) (L : Finset (Fin (k + 1))) (hL : ∀ p ∈ L, p ≠ 0)
    (Y : Set Point.{u}) (hrow : ∀ i j, before i j → row i < row j)
    (hAbove : ∀ i ∈ A.active, ∀ y ∈ Y, row i < y.1)
    (nested : IsNested c)
    (htri : ∀ p : Fin (k + 1), p ≠ 0 → TriangleFree (gridColorGraph c p))
    (hNoZero : ∀ B : Stock.{u}, ¬ B.carrier.Pairwise (fun x y => c x y = 0))
    (hchain : ∀ S, ¬ J.small S → ∃ f : Nat → ι, (∀ n, f n ∈ S) ∧
      ∀ n m, n < m → before (f n) (f m))
    (hold : ∀ y ∈ Y, ∀ p ∈ L, J.small (A.mark row c y p))
    (havoid : ∀ p ∈ A.palette row c before, p ∉ L) :
    ∃ B : IndexedSlices.{u} ι, ∃ M : Finset (Fin (k + 1)),
      Refines B A ∧ ¬ J.small B.active ∧ L.card < M.card ∧
      (∀ p ∈ M, p ≠ 0) ∧ ∀ y ∈ Y, ∀ p ∈ M, J.small (B.mark row c y p) := by
  classical
  let fiber (B : IndexedSlices.{u} ι) (y : Y) (p : Fin (k + 1)) := B.mark row c y.1 p
  have hweight (B : IndexedSlices.{u} ι) (hBA : Refines B A) (y : Y) (p : Fin (k + 1))
      (_ : ¬ J.small (fiber B y p)) :
      ∃ D, Refines D B ∧ D.active = fiber B y p ∧ p ∉ D.palette row c before := by
    let D : IndexedSlices.{u} ι :=
      ⟨fiber B y p, fun i => {x ∈ B.cols i | c (row i, x) y.1 = p}, fun _ hi => hi.2⟩
    refine ⟨D, ⟨fun i hi => hi.1, fun i _ x hx => hx.1⟩, rfl, ?_⟩
    intro hp
    obtain ⟨hp0, i, hi, j, hj, hij, x, hx, z, hz, hColor⟩ := (D.mem_palette row c before p).mp hp
    have hne : (row i, x) ≠ (row j, z) := by
      intro h
      have hrows := congrArg Prod.fst h
      exact hij.elim (fun h => (hrow i j h).ne hrows) (fun h => (hrow j i h).ne hrows.symm)
    have hiy := (hAbove i (hBA.1 hi.1) y.1 y.2).ne
    have hjy := (hAbove j (hBA.1 hj.1) y.1 y.2).ne
    exact htri p hp0 ⟨hne, hColor⟩ ⟨fun h => hiy (congrArg Prod.fst h), hx.2⟩
      ⟨fun h => hjy (congrArg Prod.fst h), hz.2⟩
  have hused (B : IndexedSlices.{u} ι) (_ : Refines B A) (hB : ¬ J.small B.active) :
      (B.palette row c before).Nonempty := by
    by_contra hp
    obtain ⟨f, hf, hpath⟩ := hchain B.active hB
    obtain ⟨D, hD⟩ := B.exists_zero_stock_of_palette_empty row c before hrow nested f hf hpath hp
    exact hNoZero D hD
  obtain ⟨B, M, hBA, hB, _, hcard, hM, hmarked⟩ :=
    exists_enlarged_marked_palette J Refines Refines.refl (fun _ _ _ => Refines.trans)
      IndexedSlices.active (fun B => B.palette row c before) (palette_mono row c before)
      fiber (fun h y p => mark_mono row c h y.1 p) A hA L hweight
      (fun y p hp => hold y.1 y.2 p hp) havoid hused
  refine ⟨B, M, hBA, hB, hcard, ?_, fun y hy => hmarked ⟨y, hy⟩⟩
  intro p hp
  exact (hM p hp).elim (hL p) (fun hp => ((B.mem_palette row c before p).mp hp).1)

end IndexedSlices

end Jsp000976
