import analysis.p_series
import number_theory.arithmetic_function
import algebra.squarefree
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral
import analysis.special_functions.integrals
import defs
import summability

noncomputable theory
-- open_locale classical
open nat finset list finsupp set function filter measure_theory
open_locale topological_space interval big_operators filter ennreal asymptotics

variables {α : Type*} [preorder α]

namespace squarefree_sums

lemma real_tendsto_implies_nat_tendsto
{a : ℝ}
{f : ℝ → ℝ}
(hf : tendsto f at_top (𝓝 a))
:
tendsto (λ (n : ℕ), f ↑n) at_top (𝓝 a) :=
begin
  rw tendsto_at_top',
  intros s hs,
  rw tendsto_at_top' at hf,
  specialize hf s hs,
  cases hf with a ha,
  use ⌈a⌉₊,
  intros b,
  specialize ha ↑b,
  intros hb,
  have : ⌈a⌉₊ ≤ b, exact hb,
  have : a ≤ ↑b,
    calc a ≤ ↑⌈a⌉₊ : nat.le_ceil a
      ... ≤ ↑b : cast_le.mpr this,
  exact ha this,
end

end squarefree_sums
