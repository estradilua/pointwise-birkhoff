import Mathlib

lemma map_partialSups
    [SemilatticeSup α] [SemilatticeSup β] [FunLike F α β] [SupHomClass F α β]
    (f : ℕ → α) (g : F) : partialSups (g ∘ f) = g ∘ partialSups f := by
  funext n; induction n <;> simp [*]

open OrderIso in
lemma add_partialSups
    [Lattice α] [AddGroup α] [CovariantClass α α ((· + ·)) (· ≤ ·)]
    (f : ℕ → α) (c : α) : partialSups (c + f ·) n = c + partialSups f n := by
  change (partialSups (addLeft c ∘ _)) n = _
  rw [map_partialSups f (addLeft c)]; rfl

/-- This is the old version. -/
example [SemilatticeSup α] (f : ℕ → α) (n : ℕ) :
    partialSups f n.succ = f 0 ⊔ partialSups (f ∘ .succ) n := by
  induction' n with n hn; rfl
  have : (partialSups (f ∘ Nat.succ)) (Nat.succ n) =
      ((partialSups (f ∘ Nat.succ)) n ⊔ (f ∘ Nat.succ) (n + 1)) := by simp
  simp [this, ← sup_assoc, ← hn]

-- It seems this result doesn't yet exist in Mathlib and is convenient for the following proof.
open Finset in
lemma Order.Icc_image_succ {ι : Type u_2} [LinearOrder ι] [SuccOrder ι]
    [LocallyFiniteOrder ι] [OrderBot ι] (i : ι) :
    Icc (Order.succ ⊥) (Order.succ i) = image Order.succ (Icc ⊥ i) := by
  ext x
  constructor
  · intro hx
    simp_rw [Icc_bot, mem_image, mem_Iic]
    rw [mem_Icc] at hx
    obtain hc | hc := eq_or_ne x ⊥
    · use ⊥
      simp_all [hx.1]
    · -- Since `x ≠ ⊥` there exists `y` such that `x = Order.succ y`.
      -- Isn't there a lemma for this?
      sorry
  · intro hx
    simp only [Icc_bot, mem_image, mem_Iic] at hx
    obtain ⟨y, hy⟩ := hx
    rw [mem_Icc]
    exact ⟨by simp [← hy.2], by simp [← hy.2, hy.1]⟩

-- It seems this result doesn't yet exist in Mathlib and is convenient for the following proof.
open Finset in
lemma bot_union_Icc {ι : Type u_2} [LinearOrder ι] [SuccOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    (i : ι) : {⊥} ∪ Icc (Order.succ ⊥) i = Iic i := by
  ext x
  constructor
  · intro hx
    simp only [mem_union, mem_singleton, mem_Icc] at hx
    obtain hc | hc := hx
    · simp [hc]
    · simp [hc.2]
  · intro hx
    obtain hc | hc := eq_bot_or_bot_lt x
    · simp [hc]
    · rw [mem_union, mem_Icc]
      rw [mem_Iic] at hx
      exact Or.inr ⟨Order.succ_le_of_lt hc, hx⟩

-- This a generalised version of the previous `partialSups_succ'`.
-- To be added to `Mathlib/Order/PartialSups`
open Finset in
lemma partialSups_succ'' {α : Type u_1} {ι : Type u_2} [SemilatticeSup α] [LinearOrder ι]
    [LocallyFiniteOrder ι] [SuccOrder ι] [OrderBot ι] (f : ι → α) (i : ι) :
    (partialSups f) (Order.succ i) = f ⊥ ⊔ (partialSups (f ∘ Order.succ)) i := by
  suffices partialSups (f ∘ Order.succ) i = (Icc (Order.succ ⊥) (Order.succ i)).sup'
      (nonempty_Icc.mpr <| Order.succ_le_succ <| bot_le) f  by
    have ne'' : ({⊥} : Finset ι).Nonempty := singleton_nonempty ⊥
    rw [this, partialSups_apply]
    have : f ⊥ = ({⊥} : Finset ι).sup' ne'' f := by simp
    rw [this]
    have ne' : (Icc (Order.succ ⊥) (Order.succ i)).Nonempty :=
        nonempty_Icc.mpr <| Order.succ_le_succ <| bot_le
    rw [← sup'_union ne'' ne' f]
    exact sup'_congr nonempty_Iic (bot_union_Icc <| Order.succ i).symm fun _ ↦ congrFun rfl
  have h (f : ι → α) (i : ι) : partialSups f i = (Icc ⊥ i).sup'
      (nonempty_Icc.mpr <| OrderBot.bot_le i) f := by rfl
  simp_rw [h (f ∘ Order.succ) i, sup'_comp_eq_image, ← Order.Icc_image_succ i]

-- This lemma matches `partialSups_add_one` which is already in Mathlib,
-- in `Mathlib/Algebra/Order/PartialSups`
lemma partialSups_add_one' [SemilatticeSup α] (f : ℕ → α) (n : ℕ) :
    partialSups f (n + 1) = f 0 ⊔ partialSups (f ∘ (fun k ↦ k + 1)) n := by
  exact Order.succ_eq_add_one n ▸ partialSups_succ'' f n
