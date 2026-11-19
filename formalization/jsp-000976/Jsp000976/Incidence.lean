module

public import Jsp000976.StageBounds
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Full sets and positive incidence

This is the incidence argument of §3 of Howe–Huffman–Kohlmeyer–Kruer.
A set is full when uncountably many rows have uncountable slices.
-/

@[expose] public section

namespace Jsp000976

open Set Cardinal

universe u v

/-- The columns of `X` in the row `a`. -/
def rowSlice (X : Set Point.{u}) (a : Stage.{u}) : Set Stage.{u} := {b | (a, b) ∈ X}

/-- The rows of `X` with uncountable slices. -/
def thickRows (X : Set Point.{u}) : Set Stage.{u} := {a | ¬ (rowSlice X a).Countable}

/-- A set is full if it has uncountably many thick rows. -/
def Full (X : Set Point.{u}) : Prop := ¬ (thickRows X).Countable

/-- The part of `X` strictly above the row `a`. -/
def tail (X : Set Point.{u}) (a : Stage.{u}) : Set Point.{u} := {x ∈ X | a < x.1}

theorem thickRows_mono : Monotone (thickRows : Set Point.{u} → Set Stage.{u}) := by
  intro X Y hXY a ha hc
  exact ha (hc.mono fun _ hb => hXY hb)

theorem Full.mono {X Y : Set Point.{u}} (hX : Full X) (hXY : X ⊆ Y) : Full Y :=
  fun hY => hX (hY.mono (thickRows_mono hXY))

theorem Full.univ : Full (univ : Set Point.{u}) := by
  have hrow : thickRows (Set.univ : Set Point.{u}) = Set.univ := by
    ext a
    simp [thickRows, rowSlice, not_countable_univ]
  exact fun h => not_countable_univ (hrow ▸ h)

/-- A countable union of nonfull sets is nonfull. -/
theorem not_full_iUnion {ι : Type v} [Countable ι] (X : ι → Set Point.{u})
    (hX : ∀ i, ¬ Full (X i)) : ¬ Full (⋃ i, X i) := by
  have hrows (i : ι) : (thickRows (X i)).Countable := not_not.mp (hX i)
  apply not_not.mpr
  apply (countable_iUnion hrows).mono
  intro a ha
  by_contra hab
  apply ha
  have hi (i : ι) : (rowSlice (X i) a).Countable :=
    not_not.mp (fun h => hab (mem_iUnion.mpr ⟨i, h⟩))
  apply (countable_iUnion hi).mono
  intro b hb
  obtain ⟨i, hi⟩ := mem_iUnion.mp hb
  exact mem_iUnion.mpr ⟨i, hi⟩

theorem not_full_union {X Y : Set Point.{u}} (hX : ¬ Full X) (hY : ¬ Full Y) :
    ¬ Full (X ∪ Y) := by
  apply not_not.mpr
  apply ((not_not.mp hX).union (not_not.mp hY)).mono
  intro a ha
  by_contra h
  have hXrow : (rowSlice X a).Countable := not_not.mp (fun hx => h (Or.inl hx))
  have hYrow : (rowSlice Y a).Countable := not_not.mp (fun hy => h (Or.inr hy))
  exact ha (hXrow.union hYrow)

/-- Deleting a nonfull set from a full set leaves a full set. -/
theorem Full.diff_nonfull {X Y : Set Point.{u}} (hX : Full X) (hY : ¬ Full Y) :
    Full (X \ Y) := by
  intro hdiff
  apply not_full_union (not_not.mpr hdiff) hY
  apply hX.mono
  intro x hx
  by_cases h : x ∈ Y
  · exact Or.inr h
  · exact Or.inl ⟨hx, h⟩

/-- Every tail of a full set remains full. -/
theorem Full.tail {X : Set Point.{u}} (hX : Full X) (a : Stage.{u}) : Full (tail X a) := by
  intro htail
  apply hX
  apply (htail.union (countable_Iic_stage a)).mono
  intro b hb
  rcases le_or_gt b a with hba | hab
  · exact Or.inr hba
  · refine Or.inl fun h => hb (h.mono ?_)
    intro x hx
    change (b, x) ∈ Jsp000976.tail X a
    exact ⟨hx, hab⟩

/-- Every full set contains a stock. -/
theorem Full.exists_stock {X : Set Point.{u}} (hX : Full X) :
    ∃ A : Stock.{u}, A.carrier ⊆ X := by
  classical
  have hnext (a : Stage.{u}) : ∃ b ∈ thickRows X, a < b := by
    have h : ¬ thickRows X ⊆ Iic a := fun hs => hX ((countable_Iic_stage a).mono hs)
    obtain ⟨b, hb, hab⟩ := not_subset.mp h
    exact ⟨b, hb, lt_of_not_ge hab⟩
  obtain ⟨b0, hb0⟩ : (thickRows X).Nonempty := by
    by_contra! h
    exact hX (by simp [h])
  choose next hnmem hnlt using hnext
  let row : Nat → Stage.{u} := Nat.rec b0 (fun _ a => next a)
  have hrows (n : Nat) : row n ∈ thickRows X := by
    cases n with
    | zero => exact hb0
    | succ n => exact hnmem (row n)
  let A : Stock.{u} := ⟨row, strictMono_nat_of_lt_succ (fun n => hnlt (row n)),
    fun n => rowSlice X (row n), hrows⟩
  refine ⟨A, ?_⟩
  rintro ⟨a, b⟩ ⟨n, ha, hb⟩
  change a = row n at ha
  subst a
  exact hb

/-- A full set has a point above the cutoff outside every set in a countable
family of nonfull exceptions. -/
theorem Full.exists_above_avoiding {ι : Type v} [Countable ι] {X : Set Point.{u}}
    (hX : Full X) (γ : Stage.{u}) (E : ι → Set Point.{u}) (hE : ∀ i, ¬ Full (E i)) :
    ∃ y ∈ X, γ < y.1 ∧ ∀ i, y ∉ E i := by
  have hfull := (hX.tail γ).diff_nonfull (not_full_iUnion E hE)
  obtain ⟨A, hA⟩ := hfull.exists_stock
  obtain ⟨b, hb⟩ : (A.slice 0).Nonempty := by
    by_contra! h
    exact A.thick 0 (by simp [h])
  have hy := hA (A.mem_carrier 0 hb)
  exact ⟨(A.row 0, b), hy.1.1, hy.1.2, fun i hi => hy.2 (mem_iUnion.mpr ⟨i, hi⟩)⟩

/-- Every thick slice of `X` has an edge to every full subset of `X`
strictly above its row. -/
def IncidenceProperty (G : Point.{u} → Point.{u} → Prop) (X : Set Point.{u}) : Prop :=
  ∀ (a : Stage.{u}) (S : Set Stage.{u}) (Z : Set Point.{u}),
    ¬ S.Countable → S ⊆ rowSlice X a → Full Z → Z ⊆ tail X a →
      ∃ b ∈ S, ∃ y ∈ Z, G (a, b) y

private structure AvoidanceStep (G : Point.{u} → Point.{u} → Prop) (Y : Set Point.{u}) where
  row : Stage.{u}
  slice : Set Stage.{u}
  thick : ¬ slice.Countable
  within : slice ⊆ rowSlice Y row
  next : Set Point.{u}
  nextFull : Full next
  nextWithin : next ⊆ tail Y row
  separated : ∀ b ∈ slice, ∀ y ∈ next, ¬ G (row, b) y

/-- If every stock has an edge and there are no edges within rows, some full
set has the incidence property. -/
theorem exists_full_incidence (G : Point.{u} → Point.{u} → Prop) (hSym : Std.Symm G)
    (hrow : ∀ x y, x.1 = y.1 → ¬ G x y)
    (hno : ∀ A : Stock.{u}, ¬ A.carrier.Pairwise (fun x y => ¬ G x y)) :
    ∃ X : Set Point.{u}, Full X ∧ IncidenceProperty G X := by
  classical
  by_contra! hbad
  let FullSet := {X : Set Point.{u} // Full X}
  have hstep (Y : FullSet) : Nonempty (AvoidanceStep G Y.1) := by
    have h := hbad Y.1 Y.2
    unfold IncidenceProperty at h
    push Not at h
    obtain ⟨a, S, Z, hS, hsub, hZ, htail, hsep⟩ := h
    exact ⟨⟨a, S, hS, hsub, Z, hZ, htail, hsep⟩⟩
  let step (Y : FullSet) := (hstep Y).some
  let Y : Nat → FullSet := Nat.rec ⟨univ, Full.univ⟩
    (fun _ W => ⟨(step W).next, (step W).nextFull⟩)
  have hnext (n : Nat) : (Y (n + 1)).1 ⊆ tail (Y n).1 (step (Y n)).row :=
    (step (Y n)).nextWithin
  have hdesc : Antitone (fun n => (Y n).1) :=
    antitone_nat_of_succ_le fun n _ hx => (hnext n hx).1
  let row (n : Nat) := (step (Y n)).row
  let S (n : Nat) := (step (Y n)).slice
  have hrows (n : Nat) : row n < row (n + 1) := by
    obtain ⟨b, hb⟩ : (S (n + 1)).Nonempty := by
      by_contra! h
      exact (step (Y (n + 1))).thick (by simp [S, h])
    have hm : (row (n + 1), b) ∈ (Y (n + 1)).1 := (step (Y (n + 1))).within hb
    exact (hnext n hm).2
  let A : Stock.{u} := ⟨row, strictMono_nat_of_lt_succ hrows, S, fun n => (step (Y n)).thick⟩
  have hcross (m n : Nat) (hmn : m < n) (b : Stage.{u}) (hb : b ∈ S m)
      (d : Stage.{u}) (hd : d ∈ S n) : ¬ G (row m, b) (row n, d) := by
    have hdY : (row n, d) ∈ (Y n).1 := (step (Y n)).within hd
    exact (step (Y m)).separated b hb _ (hdesc (Nat.succ_le_of_lt hmn) hdY)
  apply hno A
  rintro ⟨a, b⟩ ⟨m, ha, hb⟩ ⟨c, d⟩ ⟨n, hc, hd⟩ _
  change a = row m at ha
  change c = row n at hc
  subst a
  subst c
  rcases lt_trichotomy m n with h | h | h
  · exact hcross m n h b hb d hd
  · exact hrow _ _ (congrArg row h)
  · exact fun hedge => hcross n m h d hd b hb (hSym.symm _ _ hedge)

/-- Later points with only countably many neighbors in the specified slice. -/
def incidenceExceptions (G : Point.{u} → Point.{u} → Prop) (X : Set Point.{u})
    (a : Stage.{u}) (S : Set Stage.{u}) : Set Point.{u} :=
  {y ∈ tail X a | {b ∈ S | G (a, b) y}.Countable}

/-- Under the incidence property and countable forward degrees, the later
points with countable backward degree into a thick slice form a nonfull set. -/
theorem IncidenceProperty.not_full_exceptional {G : Point.{u} → Point.{u} → Prop}
    {X : Set Point.{u}} (hinc : IncidenceProperty G X) (hSym : Std.Symm G)
    (hforward : ∀ (x : Point.{u}) (b : Stage.{u}), x.1 < b → {d | G x (b, d)}.Countable)
    {a : Stage.{u}} {S : Set Stage.{u}} (hS : ¬ S.Countable) (hsub : S ⊆ rowSlice X a) :
    ¬ Full (incidenceExceptions G X a S) := by
  classical
  intro hfull
  let E := incidenceExceptions G X a S
  have above (b : Stage.{u}) (hb : b ∈ thickRows E) : a < b := by
    obtain ⟨d, hd⟩ : (rowSlice E b).Nonempty := by
      by_contra! h
      exact hb (by simp [h])
    change (b, d) ∈ E at hd
    exact hd.1.2
  let D : Set Stage.{u} := insert a (thickRows E)
  let center : D := ⟨a, mem_insert _ _⟩
  let U (i : D) : Set Stage.{u} := if i.1 = a then S else rowSlice E i.1
  have ht (i : D) : ¬ (U i).Countable := by
    by_cases h : i.1 = a
    · simpa [U, h] using hS
    · have hi : ¬ (rowSlice E i.1).Countable := (mem_insert_iff.mp i.2).resolve_left h
      simpa [U, h] using hi
  let conflict (x y : Σ _ : D, Stage.{u}) : Prop :=
    (x.1.1 = a ∨ y.1.1 = a) ∧ G (x.1.1, x.2) (y.1.1, y.2)
  have hsym : Std.Symm conflict :=
    ⟨fun x y h => ⟨h.1.symm, hSym.symm _ _ h.2⟩⟩
  have hdegree (i j : D) (hij : i ≠ j) (x : Stage.{u}) (hx : x ∈ U i) :
      {y ∈ U j | conflict ⟨i, x⟩ ⟨j, y⟩}.Countable := by
    by_cases hi : i.1 = a
    · have hj : j.1 ≠ a := fun h => hij (Subtype.ext (hi.trans h.symm))
      have hjE := (mem_insert_iff.mp j.2).resolve_left hj
      have hn := hforward (i.1, x) j.1 (by rw [hi]; exact above _ hjE)
      exact hn.mono fun _ hy => hy.2.2
    · have hxE : (i.1, x) ∈ E := by simpa [U, hi, rowSlice] using hx
      apply hxE.2.mono
      intro y hy
      have hj : j.1 = a := hy.2.1.resolve_left hi
      exact ⟨by simpa [U, hj] using hy.1, by simpa [hj] using hSym.symm _ _ hy.2.2⟩
  have hD : #D ≤ ℵ₁ := (mk_set_le D).trans_eq (mk_ord_toType _)
  obtain ⟨T, hT, hTfree⟩ := exists_uncountable_thinning hD U ht conflict hsym hdegree
  let Z : Set Point.{u} := {y | ∃ h : y.1 ∈ thickRows E,
    y.2 ∈ T ⟨y.1, mem_insert_of_mem a h⟩}
  have hZ : Full Z := by
    intro h
    apply hfull
    apply h.mono
    intro b hb
    refine fun hc => (hT ⟨b, mem_insert_of_mem a hb⟩).2 (hc.mono ?_)
    intro d hd
    change (b, d) ∈ Z
    exact ⟨hb, hd⟩
  have hZsub : Z ⊆ tail X a := by
    rintro ⟨b, d⟩ ⟨hb, hd⟩
    have hbne : b ≠ a := (above b hb).ne'
    have hdE : (b, d) ∈ E := by
      have this := (hT ⟨b, mem_insert_of_mem a hb⟩).1 hd
      simpa [U, hbne, rowSlice] using this
    exact hdE.1
  have hTc : T center ⊆ rowSlice X a := by
    intro b hb
    apply hsub
    have this := (hT center).1 hb
    simpa [U, center] using this
  obtain ⟨b, hb, y, ⟨hy, hymi⟩, hedge⟩ := hinc a (T center) Z (hT center).2 hTc hZ hZsub
  have hne : center ≠ (⟨y.1, mem_insert_of_mem a hy⟩ : D) :=
    fun h => (above _ hy).ne (congrArg Subtype.val h)
  apply hTfree center ⟨y.1, mem_insert_of_mem a hy⟩ hne b hb y.2 hymi
  exact ⟨Or.inl rfl, by simpa [center] using hedge⟩

end Jsp000976
