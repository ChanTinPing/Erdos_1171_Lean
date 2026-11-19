module

public import Jsp000976.CompatiblePalette
public import Jsp000976.MarkFamily
public import Jsp000976.ChainIdeal

/-!
# Raising the number of marked colors in the ground model
-/

@[expose] public section

namespace Jsp000976

open Set

universe u

/-- The data extracted from one dense cone of the reservoir tree. Each
finite test has its own compatible chain of successful occurrences. -/
structure GroundCandidates {k : Nat} (c : GridColoring.{u} k)
    (X Y : Set Point.{u}) (r : Nat) where
  labels : Type
  countable : Countable labels
  earlier : labels → labels → Prop
  row : labels → Stage.{u}
  ordered : ∀ i j, earlier i j → row i < row j
  slice : labels → Set Stage.{u}
  thick : ∀ i, ¬ (slice i).Countable
  contained : ∀ i x, x ∈ slice i → (row i, x) ∈ Y
  cutoff : Stage.{u}
  below : ∀ i, row i ≤ cutoff
  marked : Finset (Fin (k + 1))
  marked_positive : ∀ p ∈ marked, p ≠ 0
  rank : r ≤ marked.card
  backward : ∀ i j, earlier i j → ∀ y ∈ slice j,
    {x ∈ slice i | c (row i, x) (row j, y) ∈ marked}.Countable
  clean : ∀ F : Finset Point.{u}, ContainsChain earlier
    {i | ∀ y ∈ F, y ∈ X → cutoff < y.1 → ∀ p ∈ marked,
      {x ∈ slice i | c (row i, x) y = p}.Countable}

/-- The compatible families obtained by thinning and minimizing give
marking data with more marked colors in the original full reservoir. -/
theorem GroundCandidates.exists_rank_succ {k r : Nat} {c : GridColoring.{u} k}
    {X Y : Set Point.{u}} (D : GroundCandidates c X Y r)
    (symm : ∀ x y, c x y = c y x) (nested : IsNested c)
    (htri : ∀ p : Fin (k + 1), p ≠ 0 → TriangleFree (gridColorGraph c p))
    (hNoZero : ∀ A : Stock.{u}, ¬ A.carrier.Pairwise (fun x y => c x y = 0)) :
    ∃ M : MarkFamily c X, M.carrier ⊆ Y ∧ r + 1 ≤ M.marked.card := by
  classical
  let := D.countable
  obtain ⟨T, hT, hfree⟩ := exists_compatible_thinning c symm nested D.earlier D.row D.ordered
    D.slice D.thick D.marked D.marked_positive D.backward
  let A : IndexedSlices.{u} D.labels := ⟨univ, T, fun i _ => (hT i).2⟩
  let Later := {y : Point.{u} // y ∈ X ∧ D.cutoff < y.1}
  let Test := Later × {p : Fin (k + 1) // p ∈ D.marked}
  let marks (s : Test) : Set D.labels := A.mark D.row c s.1.1 s.2.1
  have hirr (i : D.labels) : ¬ D.earlier i i := fun h => (lt_irrefl _) (D.ordered i i h)
  have hclean (M : Finset Test) : ContainsChain D.earlier (RowIdeal.coveredByMarks marks M)ᶜ := by
    obtain ⟨f, hf, hchain⟩ := D.clean (M.image fun s => s.1.1)
    refine ⟨f, ?_, hchain⟩
    intro n h
    obtain ⟨s, hs, hBad⟩ := h
    have hCount := hf n s.1.1 (Finset.mem_image_of_mem _ hs) s.1.2.1 s.1.2.2 s.2.1 s.2.2
    have hsub :
        {x ∈ T (f n) | c (D.row (f n), x) s.1.1 = s.2.1} ⊆
          {x ∈ D.slice (f n) | c (D.row (f n), x) s.1.1 = s.2.1} := by
      intro x hx
      exact ⟨(hT _).1 hx.1, hx.2⟩
    exact hBad.2 (hCount.mono hsub)
  let J := RowIdeal.chainMarks D.earlier hirr marks hclean
  have hMark (y : Point.{u}) (hy : y ∈ {y | y ∈ X ∧ D.cutoff < y.1}) (p : Fin (k + 1))
      (hp : p ∈ D.marked) : J.small (A.mark D.row c y p) :=
    RowIdeal.chainMarks_generator_small D.earlier hirr marks hclean (⟨y, hy⟩, ⟨p, hp⟩)
  have hAvoid (p : Fin (k + 1)) (hp : p ∈ A.palette D.row c D.earlier) : p ∉ D.marked := by
    obtain ⟨_, i, _, j, _, hij, x, hx, y, hy, hxy⟩ :=
      (A.mem_palette D.row c D.earlier p).mp hp
    rw [← hxy]
    exact hfree i j hij x hx y hy
  obtain ⟨B, M, hBA, hB, hRank, hPos, hMarks⟩ := A.exists_larger_marked_palette
    D.row c D.earlier J J.univ_not_small D.marked D.marked_positive
    {y | y ∈ X ∧ D.cutoff < y.1} D.ordered
    (fun i _ _ hy => (D.below i).trans_lt hy.2)
    nested htri hNoZero
    (fun S hS => RowIdeal.containsChain_of_chainMarks_positive D.earlier hirr marks hclean hS)
    hMark hAvoid
  let N : MarkFamily c X :=
    { labels := B.active
      countable := inferInstance
      row := fun i => D.row i.1
      slice := fun i => B.cols i.1
      thick := fun i => B.thick i.1 i.2
      ideal := J.restrict B.active hB
      marked := M
      marked_positive := hPos
      cutoff := D.cutoff
      row_le_cutoff := fun i => D.below i.1
      marks_small := by
        intro y hy hcy p hp
        apply J.small_of_subset _ (hMarks y ⟨hy, hcy⟩ p hp)
        rintro _ ⟨i, hi, rfl⟩
        exact ⟨i.2, hi⟩ }
  refine ⟨N, ?_, Nat.succ_le_of_lt (D.rank.trans_lt hRank)⟩
  rintro x ⟨i, hi, hx⟩
  have hi' : x.1 = D.row i.1 := hi
  have hxy : (D.row i.1, x.2) ∈ Y :=
    D.contained _ _ ((hT i.1).1 (hBA.2 i.1 i.2 hx))
  simpa only [← hi', Prod.eta] using hxy

end Jsp000976
