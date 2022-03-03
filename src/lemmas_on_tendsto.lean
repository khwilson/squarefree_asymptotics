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
open_locale classical topological_space interval big_operators filter ennreal asymptotics

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

lemma tendsto_le_zero_ev
{a : ℝ}
{f : ℝ → ℝ}
(hf_le : ∃ (X : ℝ), ∀ (x : ℝ), X ≤ x → f x ≤ 0)
(hf : tendsto f at_top (𝓝 a))
:
a ≤ 0 :=
begin
  by_contradiction H,
  push_neg at H,
  let s := set.Ioo (a / 2) (3 * a / 2),
  have : s ∈ 𝓝 a,
  {
    rw mem_nhds_iff_exists_Ioo_subset,
    use [(a / 2), (3 * a / 2)],
    split,
    simp,
    split,
    linarith,
    linarith,
    exact rfl.subset,
  },
  specialize hf this,
  rw mem_map_iff_exists_image at hf,
  rcases hf with ⟨t, ht, ht'⟩,
  simp at ht,
  cases ht with B hB,
  cases hf_le with X hX,
  specialize hB (max B X) (by simp),
  have : f (max B X) ∈ s,
    calc f (max B X) ∈ f '' t : by { use (max B X), exact ⟨hB, rfl⟩, }
      ... ⊆ s : ht',
  have : 0 < f (max B X),
    calc 0 < a / 2 : by linarith
      ... < f (max B X) : by { simp at this, exact this.left, },

  linarith [this, hX (max B X) (by simp)],
end

lemma tendsto_le_zero_ev'
{a : ℝ}
{f : ℕ → ℝ}
(hf_le : ∃ (X : ℕ), ∀ (x : ℕ), X ≤ x → f x ≤ 0)
(hf : tendsto f at_top (𝓝 a))
:
a ≤ 0 :=
begin
  by_contradiction H,
  push_neg at H,
  let s := set.Ioo (a / 2) (3 * a / 2),
  have : s ∈ 𝓝 a,
  {
    rw mem_nhds_iff_exists_Ioo_subset,
    use [(a / 2), (3 * a / 2)],
    split,
    simp,
    split,
    linarith,
    linarith,
    exact rfl.subset,
  },
  specialize hf this,
  rw mem_map_iff_exists_image at hf,
  rcases hf with ⟨t, ht, ht'⟩,
  simp at ht,
  cases ht with B hB,
  cases hf_le with X hX,
  specialize hB (max B X) (by simp),
  have : f (max B X) ∈ s,
    calc f (max B X) ∈ f '' t : by { use (max B X), exact ⟨hB, rfl⟩, }
      ... ⊆ s : ht',
  have : 0 < f (max B X),
    calc 0 < a / 2 : by linarith
      ... < f (max B X) : by { simp at this, exact this.left, },

  linarith [this, hX (max B X) (by simp)],
end

lemma tendsto_le_ev
{a b : ℝ}
{f g : ℝ → ℝ}
(hfg : ∃ (X : ℝ), ∀ (x : ℝ), X ≤ x → f x ≤ g x)
(hf : tendsto f at_top (𝓝 a))
(hg : tendsto g at_top (𝓝 b))
:
a ≤ b :=
begin
  cases hfg with X hfg,
  have : tendsto (f - g) at_top (𝓝 (a - b)),
    exact filter.tendsto.sub hf hg,
  have hfg' : ∃ (X : ℝ), ∀ (x : ℝ), X ≤ x → (f - g) x ≤ 0, use X, intros x, simp, exact hfg x,
  have : a - b ≤ 0, exact tendsto_le_zero_ev hfg' this,
  linarith,
end

lemma tendsto_le'
{a b : ℝ}
{f g : ℕ → ℝ}
(hfg : ∃ (X : ℕ), ∀ (x : ℕ), X ≤ x → f x ≤ g x)
(hf : tendsto f at_top (𝓝 a))
(hg : tendsto g at_top (𝓝 b))
:
a ≤ b :=
begin
  cases hfg with X hfg,
  have : tendsto (f - g) at_top (𝓝 (a - b)),
    exact filter.tendsto.sub hf hg,
  have hfg' : ∃ (X : ℕ), ∀ (x : ℕ), X ≤ x → (f - g) x ≤ 0, use X, intros x, simp, exact hfg x,
  have : a - b ≤ 0, exact tendsto_le_zero_ev' hfg' this,
  linarith,
end

lemma tendsto_nonneg_ev
{a : ℝ}
{f : ℕ → ℝ}
(hf : ∃ (X : ℕ), ∀ (x : ℕ), X ≤ x → 0 ≤ f x)
(hf': tendsto f at_top (𝓝 a))
:
0 ≤ a
:=
begin
  have : tendsto (λ (n : ℕ), (0 : ℝ)) at_top (𝓝 0),
  {
    rw tendsto_at_top',
    intros s hs,
    have : (0 : ℝ) ∈ s, rcases mem_nhds_iff.mp hs with ⟨t, ht, ht'⟩, calc (0 : ℝ) ∈ t : ht'.right ... ⊆ s : ht,
    simp [this],
  },
  exact tendsto_le' hf this hf',
end

end squarefree_sums
