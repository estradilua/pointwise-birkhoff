import Mathlib.Tactic

namespace Filter.EventuallyEq

variable {f : Filter α} {f₁ f₂ f₃ : α → β} [Mul β]

@[to_additive]
lemma mul_right (h : f₁ =ᶠ[f] f₂) : f₁ * f₃ =ᶠ[f] f₂ * f₃ := mul h (by rfl)

@[to_additive]
lemma mul_left (h : f₁ =ᶠ[f] f₂) : f₃ * f₁ =ᶠ[f] f₃ * f₂ := mul (by rfl) h
