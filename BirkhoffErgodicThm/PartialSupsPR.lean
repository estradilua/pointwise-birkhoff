import Mathlib.Tactic

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

-- For `Mathlib/Order/PartialSups`
-- Needs to be generalised similar to `partialSups_succ`.
theorem partialSups_succ' [SemilatticeSup α] (f : ℕ → α) (n : ℕ) :
    partialSups f n.succ = f 0 ⊔ partialSups (f ∘ .succ) n := by
  induction' n with n hn; rfl
  have : (partialSups (f ∘ Nat.succ)) (Nat.succ n) =
      ((partialSups (f ∘ Nat.succ)) n ⊔ (f ∘ Nat.succ) (n + 1)) := by simp
  simp [this, ← sup_assoc, ← hn]
-- The general statement would be:
-- example {α : Type u_1} {ι : Type u_2} [SemilatticeSup α] [LinearOrder ι] [LocallyFiniteOrderBot ι]
--     [SuccOrder ι] [OrderBot ι] (f : ι → α) (i : ι) :
--     (partialSups f) (Order.succ i) = f ⊥ ⊔ (partialSups (f ∘ Order.succ)) i := by
--   sorry
