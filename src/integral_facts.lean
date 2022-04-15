import analysis.p_series
import number_theory.arithmetic_function
import algebra.squarefree
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral
import analysis.special_functions.integrals
import defs
import summability
import general

noncomputable theory
open nat finset list finsupp set function filter measure_theory
open_locale topological_space interval big_operators filter ennreal asymptotics

namespace squarefree_sums

lemma mem_Icc_Ico
{a b c : ℝ}
(hc : c ∈ set.Icc a b)
(hc' : c ≠ b) :
c ∈ set.Ico a b :=
begin
  simp, simp at hc,
  simp [hc.left],
  exact lt_of_le_of_ne hc.right hc',
end

lemma blech
{a m : ℕ}
{f : ℝ → ℝ}
(ham : a ≤ m)
(hf_nonneg : ∀ (b : ℝ), b ∈ set.Ici (a : ℝ) → 0 ≤ f b)
:
{x : ℝ | x ∈ set.Icc (m : ℝ) (↑m + 1) → 0 ≤ f x} = univ
:=
begin
  simp,
  apply eq_univ_of_forall,
  intros x,
  simp,
  intros hx hx',
  have : x ∈ set.Ici (a : ℝ),
    simp,
    calc (a : ℝ) ≤ ↑m : cast_le.mpr ham ... ≤ x : hx,
  exact hf_nonneg x this,
end

lemma tail_sum_le_tail_integral
{a : ℕ}
{l : ℝ}
{f : ℝ → ℝ}
(hf : tendsto (λ (b : ℕ), ∫ (x : ℝ) in a..b, f x) at_top (𝓝 l))
(hf_mono : antitone_on f (set.Ici (a : ℝ)))
(hf_nonneg : ∀ (b : ℝ), b ∈ set.Ici (a : ℝ) → 0 ≤ f b)
:
(∑' (i : ℕ), (λ (j : ℕ), ite (a + 1 ≤ j) (f ↑j) 0) i) ≤ l :=
begin
  by_cases h : summable (λ (j : ℕ), ite (a + 1 ≤ j) (f ↑j) 0),
  obtain ⟨c, hc⟩ := h,
  rw has_sum.tsum_eq hc,
  rw has_sum_iff_tendsto_nat_of_nonneg at hc,
  simp at hf,
  refine le_of_tendsto_of_tendsto hc hf _,
  rw [filter.eventually_le, eventually_at_top],
  use a + 100,
  intros n hn,
  rw sum_ite,
  simp,
  have : filter (has_le.le (a + 1)) (finset.range n) = finset.Ico (a + 1) n,
  {
    ext d,
    rw finset.mem_filter,
    simp,
    conv {to_lhs, rw and_comm},
  },
  rw this,
  obtain ⟨m, hm⟩ : ∃m, n = m + 1, {
    use n - 1,
    exact (nat.sub_add_cancel (calc 1 ≤ 100 : by linarith ... ≤ a + 100 : by linarith ... ≤ n : hn)).symm,
  },
  have : a ≤ m, {
    have : a + 1 ≤ m + 1, {
      rw ← hm,
      calc a + 1 ≤ a + 100 : by linarith ... ≤ n : hn,
    },
    linarith,
  },
  rw hm,
  transitivity,
  refine antitone_sum_le_integral this _,
  intros x hx y hy hxy,
  exact hf_mono (mem_Icc_mem_Ici hx) (mem_Icc_mem_Ici hy) hxy,

  have hf_mono_local: antitone_on f [(a : ℝ), ↑m + 1], {
    have : (n : ℝ) = (m : ℝ) + 1, simp [hm],
    rw ← this,
    rw interval_eq_Icc (cast_le.mpr (calc a ≤ a + 100 : by linarith ... ≤ n : hn)),
    intros x hx y hy hxy,
    exact hf_mono (mem_Icc_mem_Ici hx) (mem_Icc_mem_Ici hy) hxy,
  },
  have uu: interval_integrable f real.measure_space.volume ↑a (↑m + 1), {
    exact antitone_on.interval_integrable hf_mono_local,
  },

  have hf_mono_local: antitone_on f [(a : ℝ), ↑m], {
    rw interval_eq_Icc (cast_le.mpr this),
    intros x hx y hy hxy,
    exact hf_mono (mem_Icc_mem_Ici hx) (mem_Icc_mem_Ici hy) hxy,
  },
  have ul: interval_integrable f real.measure_space.volume ↑a ↑m, {
    exact antitone_on.interval_integrable hf_mono_local,
  },

  have hf_mono_local: antitone_on f [(m : ℝ), ↑m + 1], {
    rw interval_eq_Icc (calc (m : ℝ) ≤ ↑m + 1 : by simp),
    intros x hx y hy hxy,
    have ut : (m : ℝ) + 1 = ↑(m + 1), simp,
    rw ut at hx,
    rw ut at hy,
    exact hf_mono (mem_Icc_mem_Ici' hx this) (mem_Icc_mem_Ici' hy this) hxy,
  },
  have ur: interval_integrable f real.measure_space.volume ↑m (↑m + 1), {
    exact antitone_on.interval_integrable hf_mono_local,
  },

  have aa : interval_integral f ↑a ↑(m + 1) real.measure_space.volume = interval_integral f ↑a ↑m real.measure_space.volume + interval_integral f ↑m ↑(m + 1) real.measure_space.volume, {
    symmetry,
    refine interval_integral.integral_add_adjacent_intervals ul ur,
  },
  rw aa,
  simp,
  apply interval_integral.integral_nonneg_of_ae_restrict,
  simp,
  unfold filter.eventually_le,
  simp,
  rw filter.eventually_inf_principal,
  rw filter.eventually_iff,
  rw blech this hf_nonneg,
  simp,
  intros i,
  by_cases hi : a + 1 ≤ i,
  simp [hi],
  refine hf_nonneg i _,
  simp,
  calc a ≤ a + 1 : le_succ a ... ≤ i : hi,
  simp [hi],

  -- Now to the not summable case
  rw not_summable_eq_zero h,
  refine le_of_tendsto_of_tendsto (tendsto_const_nhds) hf _,
  rw [filter.eventually_le, eventually_at_top],
  use a + 1,
  intros x hx,
  apply interval_integral.integral_nonneg,
  norm_cast, linarith,
  intros u hu,
  exact hf_nonneg u (mem_Icc_mem_Ici hu),
end

theorem integral_tendsto_of_has_deriv_at {a b : ℝ} {f f' : ℝ → ℝ}
  (hderiv : ∀ x ∈ Ici a, has_deriv_at f (f' x) x)
  (hvanish : tendsto f at_top (𝓝 b))
  (hint : ∀ (b : ℝ), b ∈ Ici a → interval_integrable f' volume a b) :
  tendsto (λ (b : ℝ), ∫ y in a..b, f' y) at_top (𝓝 (b - f a)) :=
begin
  have hev : (λ (x : ℝ), f x - f a) =ᶠ[at_top] (λ (b : ℝ), ∫ y in a..b, f' y),
  { rw [eventually_eq, eventually_at_top],
    use a,
    intros b hb,
    have hderiv' : ∀ x ∈ [a, b], has_deriv_at f (f' x) x,
    { intros x hx,
      exact hderiv x (calc a = min a b : (min_eq_left hb.le).symm ... ≤ x : hx.left), },
    rw interval_integral.integral_eq_sub_of_has_deriv_at hderiv' (hint b hb.le), },
  exact tendsto.congr' hev (filter.tendsto.sub_const (f a) hvanish),
end

lemma integral_rpow_tendsto_at_top (a r : ℝ) (ha : 0 < a) (hr : r < -1) :
tendsto
(λ (y : ℝ), ∫ (x : ℝ) in a..y, x ^ r)
at_top
(𝓝 (-a ^ (r + 1) / (r + 1)))
:=
begin
  have : (λ (y : ℝ), ∫ (x : ℝ) in a..y, x ^ r) =ᶠ[at_top] (λ (y : ℝ), (y ^ (r + 1) / (r + 1)) - (a ^ (r + 1) / (r + 1))),
  { rw [eventually_eq, eventually_at_top],
    refine ⟨20, (λ b hb, _)⟩,
    rw integral_rpow,
    { ring, },
    { right,
      split,
      { linarith [hr], },
      { exact not_mem_interval_of_lt ha (by linarith [hb.le]), }, }, },
  rw tendsto_congr' this,
  have : -a ^ (r + 1) / (r + 1) = 0 - (a ^ (r + 1) / (r + 1)), { ring, },
  rw this,
  apply tendsto.sub_const,
  rw ← zero_div (r + 1),
  apply tendsto.div_const,
  have hinf : tendsto (λ (k : ℝ), k ^ -(r + 1)) at_top at_top,
  { apply tendsto_rpow_at_top,
    linarith [hr], },
  have hev : (λ (k : ℝ), k ^ -(r + 1)) =ᶠ[at_top] (λ (k : ℝ), (k ^ (r + 1))⁻¹),
  { rw [eventually_eq, eventually_at_top],
    use 0,
    intros b hb,
    rw [←real.inv_rpow hb.le, real.rpow_neg hb.le, ←real.inv_rpow hb.le], },
  refine tendsto.congr _ (tendsto_inv_at_top_zero.comp (tendsto.congr' hev hinf)),
  intros x,
  simp only [comp_app, inv_inv],
end

end squarefree_sums
