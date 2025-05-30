import Mathlib

/-- If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`),
then `φ` remains invariant under any number of iterations of `f`. -/
lemma invariant_iter (h : φ ∘ f = φ) : ∀ i, φ ∘ f^[i] = φ
  | 0 => rfl
  | n + 1 => by
    change (φ ∘ f^[n]) ∘ f = φ
    rwa [invariant_iter h n]

open Finset in

/-- If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`),
then the Birkhoff sum of `φ` over `f` for `n` iterations is equal to `n • φ`. -/
theorem birkhoffSum_eq_of_invariant [AddCommMonoid M] {φ : α → M}
    (h : φ ∘ f = φ) : birkhoffSum f φ n = n • φ := by
  funext x
  unfold birkhoffSum
  conv in fun _ => _ => intro k; change (φ ∘ f^[k]) x; rw [invariant_iter h k]
  simp

open Finset in

/-- If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`),
then the Birkhoff average of `φ` over `f` for `n` iterations is equal to `φ`
provided `0 < n`. -/
theorem birkhoffAverage_eq_of_invariant
    {φ : α → ℝ} (h : φ ∘ f = φ) (hn : 0 < n) : birkhoffAverage ℝ f φ n = φ := by
  funext x
  unfold birkhoffAverage
  rw [birkhoffSum_eq_of_invariant h]
  refine (inv_smul_eq_iff₀ ?_).mpr ?_
  · norm_cast; linarith
  · simp

lemma birkhoffAverage_neg {φ : α → ℝ} :
    birkhoffAverage ℝ f (-φ) = - birkhoffAverage ℝ f φ := by
  funext n x
  simp [birkhoffAverage, birkhoffSum]

open Finset in
lemma birkhoffAverage_add {φ ψ : α → ℝ} :
    birkhoffAverage ℝ f (φ + ψ) = birkhoffAverage ℝ f φ + birkhoffAverage ℝ f ψ := by
  funext n x
  simp only [birkhoffAverage, birkhoffSum, Pi.add_apply, sum_add_distrib, smul_eq_mul]
  linarith

open Finset in
lemma birkhoffAverage_sub {φ ψ : α → ℝ} :
    birkhoffAverage ℝ f (φ - ψ) = birkhoffAverage ℝ f φ - birkhoffAverage ℝ f ψ := by
  funext n x
  simp only [birkhoffAverage, birkhoffSum, Pi.sub_apply, sum_sub_distrib, smul_eq_mul]
  linarith
