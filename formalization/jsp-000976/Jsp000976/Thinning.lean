module

public import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Thinning uncountable slices

Choose in each indexed uncountable slice while avoiding all countable
conflicts created by earlier choices. This proves the thinning lemma
of §2 of Howe–Huffman–Kohlmeyer–Kruer.
-/

@[expose] public section

namespace Jsp000976

open Set Cardinal

universe u

/-- A scheduling type with one point for each countable ordinal. -/
abbrev Stage := (ℵ₁ : Cardinal.{u}).ord.ToType

private theorem mk_stage : #(Stage.{u}) = ℵ₁ := mk_ord_toType _

instance : Uncountable Stage.{u} :=
  aleph0_lt_mk_iff.mp (by rw [mk_stage]; exact aleph0_lt_aleph_one)

theorem countable_Iio_stage (s : Stage.{u}) : (Iio s).Countable :=
  le_aleph0_iff_set_countable.mp <| lt_aleph_one_iff.mp <| by
    simpa using (mk_Iio_lt s)

theorem countable_Iic_stage (s : Stage.{u}) : (Iic s).Countable :=
  ((countable_Iio_stage s).union (countable_singleton s)).mono <| by
    intro a ha
    rcases lt_or_eq_of_le (show a ≤ s from ha) with h | h
    · exact Or.inl h
    · exact Or.inr h

private theorem schedule {ι : Type u} (hι : #ι ≤ ℵ₁) :
    Nonempty ((ι × Stage.{u}) ↪ Stage.{u}) := by
  apply (Cardinal.le_def _ _).mp
  rw [mk_prod, mk_stage, lift_id, lift_id]
  exact (mul_le_mul' hι le_rfl).trans (le_of_eq (mul_eq_self aleph0_lt_aleph_one.le))

variable {ι : Type u} {α : ι → Type u}

/-- Uncountable slices with countable conflict sets admit uncountable
subsets with no conflict between different slices. -/
theorem exists_uncountable_thinning
    (hι : #ι ≤ ℵ₁)
    (s : ∀ i, Set (α i))
    (hs : ∀ i, ¬ (s i).Countable)
    (conflict : (Σ i, α i) → (Σ i, α i) → Prop)
    (hsym : Std.Symm conflict)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ s i, {y ∈ s j | conflict ⟨i, x⟩ ⟨j, y⟩}.Countable) :
    ∃ t : ∀ i, Set (α i),
      (∀ i, t i ⊆ s i ∧ ¬ (t i).Countable) ∧
      ∀ i j, i ≠ j → ∀ x ∈ t i, ∀ y ∈ t j, ¬ conflict ⟨i, x⟩ ⟨j, y⟩ := by
  classical
  obtain ⟨e⟩ := schedule hι
  let earlier : (ι × Stage) → (ι × Stage) → Prop := fun b a => e b < e a
  have wf : WellFounded earlier := InvImage.wf e (hasWellFounded_toType (ℵ₁ : Cardinal.{u}).ord).wf
  have hprev (a : ι × Stage) : Countable {b // earlier b a} := by
    have : Countable (Iio (e a)) := (countable_Iio_stage (e a)).to_subtype
    apply Function.Injective.countable (f := fun b : {b // earlier b a} => (⟨e b.1, b.2⟩ : Iio (e a)))
    intro b c h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  let avoid (a b : ι × Stage) (x : s b.1) : Set (α a.1) :=
    if h : b.1 = a.1 then {h ▸ x.1}
    else {y ∈ s a.1 | conflict ⟨b.1, x.1⟩ ⟨a.1, y⟩}
  have havoid (a b : ι × Stage) (x : s b.1) : (avoid a b x).Countable := by
    by_cases h : b.1 = a.1
    · simp [avoid, h]
    · simpa [avoid, h] using hc b.1 a.1 h x.1 x.2
  have fresh (a : ι × Stage) (p : ∀ b, earlier b a → s b.1) :
      ∃ x : s a.1, ∀ b (hb : earlier b a), x.1 ∉ avoid a b (p b hb) := by
    have := hprev a
    have hu : (⋃ b : {b // earlier b a}, avoid a b.1 (p b.1 b.2)).Countable :=
      countable_iUnion fun b => havoid a b.1 (p b.1 b.2)
    have hn : ¬ s a.1 ⊆ ⋃ b : {b // earlier b a}, avoid a b.1 (p b.1 b.2) :=
      fun h => hs a.1 (hu.mono h)
    obtain ⟨x, hxs, hx⟩ := not_subset.mp hn
    exact ⟨⟨x, hxs⟩, fun b hb hm => hx (mem_iUnion.mpr ⟨⟨b, hb⟩, hm⟩)⟩
  let choose : ∀ a : ι × Stage, s a.1 := wf.fix fun a p => (fresh a p).choose
  have hchoose (a b : ι × Stage) (hb : earlier b a) :
      (choose a).1 ∉ avoid a b (choose b) := by
    have h := (fresh a (fun b _ => choose b)).choose_spec b hb
    have heq (a : ι × Stage) :
        choose a = (fresh a (fun b _ => choose b)).choose := wf.fix_eq _ _
    rw [heq a]
    exact h
  let f (i : ι) (n : Stage.{u}) : α i := (choose (i, n)).1
  have hfinj (i : ι) : Function.Injective (f i) := by
    intro n m hnm
    by_contra hne
    have hab : e (i, n) ≠ e (i, m) := fun h => hne (congrArg Prod.snd (e.injective h))
    rcases lt_or_gt_of_ne hab with h | h
    · exact hchoose (i, m) (i, n) h (by simpa [avoid, f] using hnm.symm)
    · exact hchoose (i, n) (i, m) h (by simpa [avoid, f] using hnm)
  refine ⟨fun i => range (f i), ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · rintro x ⟨n, rfl⟩
      exact (choose (i, n)).2
    · intro h
      have := h.to_subtype
      exact (not_countable (α := Stage.{u})) (Function.Injective.countable
        (f := fun n => (⟨f i n, mem_range_self n⟩ : range (f i)))
        (fun n m h => hfinj i (congrArg (fun x : range (f i) => x.1) h)))
  · rintro i j hij x ⟨n, rfl⟩ y ⟨m, rfl⟩ hxy
    have hne : e (i, n) ≠ e (j, m) := fun h => hij (congrArg Prod.fst (e.injective h))
    rcases lt_or_gt_of_ne hne with h | h
    · apply hchoose (j, m) (i, n) h
      simpa [avoid, hij, f] using And.intro (choose (j, m)).2 hxy
    · apply hchoose (i, n) (j, m) h
      simpa [avoid, hij.symm, f] using And.intro (choose (i, n)).2 (hsym.symm _ _ hxy)


/-- Countably many slices may be indexed in the smallest universe. -/
theorem exists_uncountable_thinning_countable {ι : Type} [Countable ι] {α : ι → Type u}
    (s : ∀ i, Set (α i))
    (hs : ∀ i, ¬ (s i).Countable)
    (conflict : (Σ i, α i) → (Σ i, α i) → Prop)
    (hsym : Std.Symm conflict)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ s i, {y ∈ s j | conflict ⟨i, x⟩ ⟨j, y⟩}.Countable) :
    ∃ t : ∀ i, Set (α i),
      (∀ i, t i ⊆ s i ∧ ¬ (t i).Countable) ∧
      ∀ i j, i ≠ j → ∀ x ∈ t i, ∀ y ∈ t j, ¬ conflict ⟨i, x⟩ ⟨j, y⟩ := by
  let e (x : Σ i : ULift.{u} ι, α i.down) : Σ i, α i := ⟨x.1.down, x.2⟩
  let R (x y : Σ i : ULift.{u} ι, α i.down) := conflict (e x) (e y)
  have hcount : #(ULift.{u} ι) ≤ ℵ₁ := (mk_le_aleph0 (α := ULift.{u} ι)).trans aleph0_lt_aleph_one.le
  have hR (i j : ULift.{u} ι) (hij : i ≠ j) (x : α i.down) (hx : x ∈ s i.down) :
      {y ∈ s j.down | R ⟨i, x⟩ ⟨j, y⟩}.Countable :=
    hc i.down j.down (fun h => hij (congrArg ULift.up h)) x hx
  obtain ⟨t, ht, hfree⟩ := exists_uncountable_thinning hcount (fun i => s i.down)
    (fun i => hs i.down) R ⟨fun x y => hsym.symm (e x) (e y)⟩ hR
  exact ⟨fun i => t (ULift.up i), fun i => ht (ULift.up i),
    fun i j hij => hfree (ULift.up i) (ULift.up j) (fun h => hij (congrArg ULift.down h))⟩

end Jsp000976
