import Mathlib

-- To go in `Logic/Function/Iterate`? Name as `iterate_of_invariant`?
/-- If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`),
then `φ` remains invariant under any number of iterations of `f`. -/
lemma invariant_iter (h : φ ∘ f = φ) : ∀ i, φ ∘ f^[i] = φ
  | 0 => rfl
  | n + 1 => by
    change (φ ∘ f^[n]) ∘ f = φ
    rwa [invariant_iter h n]

-- To go in `Dynamics/BirkhoffSum/Basic`
open Finset in
/-- If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`),
then the Birkhoff sum of `φ` over `f` for `n` iterations is equal to `n • φ`. -/
theorem birkhoffSum_of_invariant [AddCommMonoid M] {φ : α → M}
    (h : φ ∘ f = φ) : birkhoffSum f φ n = n • φ := by
  funext x
  unfold birkhoffSum
  conv in fun _ => _ => intro k; change (φ ∘ f^[k]) x; rw [invariant_iter h k]
  simp

variable {R α : Type*} [DivisionSemiring R]

-- To go in `Dynamics/BirkhoffSum/Average`
-- Note: `[CharZero R]` required for `Nat.cast_ne_zero`.
open Finset in
/-- If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`),
then the Birkhoff average of `φ` over `f` for `n` iterations is equal to `φ`
provided `0 < n`. -/
theorem birkhoffAverage_of_invariant {M : Type*} [AddCommMonoid M] [Module R M] [CharZero R]
    {f : α → α} {φ : α → M} (h : φ ∘ f = φ) {n : ℕ} (hn : 0 < n) : birkhoffAverage R f φ n = φ := by
  funext x
  simp only [birkhoffAverage, birkhoffSum_of_invariant h, Pi.smul_apply]
  refine (inv_smul_eq_iff₀ ?_).mpr (by norm_cast)
  exact Nat.cast_ne_zero.mpr <| Nat.ne_zero_of_lt hn

-- To go in `Dynamics/BirkhoffSum/Average`
-- Note: need something more than `[AddCommMonoid M]` here to have subtraction.
lemma birkhoffAverage_neg {M : Type*} [AddCommGroup M] [Module R M] {f : α → α} {φ : α → M} :
    birkhoffAverage R f (-φ) = - birkhoffAverage R f φ := by
  funext n x
  simp [birkhoffAverage, birkhoffSum]

-- To go in `Dynamics/BirkhoffSum/Average`
open Finset in
lemma birkhoffAverage_add {M : Type*} [AddCommMonoid M] [Module R M] {f : α → α} {φ ψ : α → M} :
    birkhoffAverage R f (φ + ψ) = birkhoffAverage R f φ + birkhoffAverage R f ψ := by
  funext n x
  simp [birkhoffAverage, birkhoffSum, sum_add_distrib]

-- To go in `Dynamics/BirkhoffSum/Average`
-- Note: need something more than `[AddCommMonoid M]` here to have subtraction.
open Finset in
lemma birkhoffAverage_sub {M : Type*} [AddCommGroup M] [Module R M] {f : α → α} {φ ψ : α → M} :
    birkhoffAverage R f (φ - ψ) = birkhoffAverage R f φ - birkhoffAverage R f ψ := by
  funext n x
  simp [birkhoffAverage, birkhoffSum, smul_sub]
