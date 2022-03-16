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

lemma tendsto_le_of_eventually_le
  {α : Type*}  {γ : Type*}
  [topological_space α] [linear_order α] [order_closed_topology α]
  {l : filter γ} [ne_bot l]
  {f g : γ → α} {u v : α} (hf : filter.tendsto f l (𝓝 u))
  (hg : filter.tendsto g l (𝓝 v)) (hfg : f ≤ᶠ[l] g) :
  u ≤ v :=
begin
  by_contradiction H,
  push_neg at H,

  by_cases h_sep : ∃ x, v < x ∧ x < u,
  { rcases h_sep with ⟨x, hxl, hxr⟩,
    cases filter.nonempty_of_mem (
      l.inter_sets (hf $ Ioi_mem_nhds hxr) (l.inter_sets (hg $ Iio_mem_nhds hxl) hfg)) with c hc,
    simp at hc,
    exact ne_of_lt (
      calc f c ≤ g c : hc.right.right
        ... < x : hc.right.left
        ... < f c : hc.left
    ) rfl, },
  { cases filter.nonempty_of_mem (
      l.inter_sets (hf $ Ioi_mem_nhds H) (l.inter_sets (hg $ Iio_mem_nhds H) hfg)) with c hc,
    simp at hc,

    push_neg at h_sep,
    by_cases hf_lt : f c < u,
      specialize h_sep (f c) hc.left,
      exact not_le_of_lt hf_lt h_sep,

    by_cases hg_lt : v < g c,
      specialize h_sep (g c) hg_lt,
      exact ne_of_lt (calc u ≤ g c : h_sep ... < u : hc.right.left) rfl,

    push_neg at hf_lt,
    push_neg at hg_lt,
    have : u < u,
      calc u ≤ f c : hf_lt
        ... ≤ g c : hc.right.right
        ... ≤ v : hg_lt
        ... < u : H,
   exact ne_of_lt this rfl, },
end

end squarefree_sums
