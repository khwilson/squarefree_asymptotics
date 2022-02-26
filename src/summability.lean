/-
This file concerns itself with extending various summability lemmas
that are useful in manipulating tsums and sums
-/
import number_theory.arithmetic_function
import algebra.squarefree
import algebra.order.floor
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral
import general

noncomputable theory
open nat finset function filter
open_locale classical topological_space interval big_operators filter asymptotics arithmetic_function

namespace squarefree_sums

lemma one_dirichlet_summable : ∀ (d : ℕ), 2 ≤ d → summable (λ (n : ℕ), ((n : ℝ) ^ d)⁻¹) :=
begin
  intros d hd,
  apply real.summable_nat_pow_inv.mpr,
  linarith,
end

lemma const_dirichlet_summable : ∀ (d : ℕ) (C : ℝ), 2 ≤ d → summable (λ (n : ℕ), C * ((n : ℝ) ^ d)⁻¹) :=
begin
  intros d C hd,
  by_cases C = 0,
  conv { congr, funext, rw h, simp, },
  exact summable_zero,
  rw ← summable_mul_left_iff,
  exact one_dirichlet_summable d hd,
  exact h,
end

lemma bounded_dirichlet_summable
(f : ℕ → ℝ)
(hC : ∃ C, ∀ (n : ℕ), |f n| ≤ C) :
 ∀ (d : ℕ), 2 ≤ d
 → summable (λ (n : ℕ), (f n) * ((n : ℝ) ^ d)⁻¹):=
begin
  intros d hd,
  rw ← summable_abs_iff,
  conv { congr, funext, rw abs_mul},
  cases hC with C hC,
  apply summable_of_nonneg_of_le,
  intros b,
  rw ← abs_mul,
  refine abs_nonneg _,
  intros b,
  have : |f b| * |(↑b ^ d)⁻¹| ≤ C * |(↑b ^ d)⁻¹|, {
    specialize hC b,
    apply mul_le_mul hC rfl.le,
    refine abs_nonneg _,
    transitivity,
    exact abs_nonneg (f b),
    exact hC,
  },
  exact this,
  apply summable.mul_left,
  have : ∀ (b : ℕ), 0 ≤ ((b : ℝ) ^ d)⁻¹, {
    intros b,
    simp,
  },
  conv { congr, funext, rw abs_of_nonneg (this b), },
  exact one_dirichlet_summable d hd,
end

lemma abs_sum_le_sum_abs' {f : ℕ → ℝ} {s : finset ℕ}: | ∑ d in s, f d | ≤ ∑ d in s, | f d | :=
begin
  apply finset.induction_on s,
  simp only [finset.sum_empty, abs_zero],
  {
    intros i s his IH,
    simp only [his, finset.sum_insert, not_false_iff],
    exact (abs_add _ _).trans (add_le_add (le_refl (|f i|)) IH),
  },
  sorry,
end

lemma abs_tsum_le_tsum_abs {f : ℕ → ℝ} : | ∑' i, f i | ≤ (∑' i, |f i|) :=
begin
  by_cases summable f,
  have : has_sum f (∑' i, f i), exact summable.has_sum h,
  unfold has_sum at this,
  have hf : filter.tendsto
    (λ (s : finset ℕ), |∑ (b : ℕ) in s, f b|) at_top (nhds (|∑' i, f i|)),
    exact tendsto_abs this,

  have : summable (λ n, |f n|), simp [summable_abs_iff, h],
  have hg : has_sum (λ n, |f n|) (∑' i, |f i|), exact summable.has_sum this,
  unfold has_sum at hg,

  have h_le : ∀ (s : finset ℕ), (λ (s : finset ℕ), |∑ (b : ℕ) in s, f b|) s ≤ (λ (s : finset ℕ), ∑ (b : ℕ) in s, |f b|) s,
  {
    intros s,
    simp,
    exact abs_sum_le_sum_abs f s,
  },

  exact le_of_tendsto_of_tendsto' hf hg h_le,

  have : ¬ summable (λ n, |f n|), simp [summable_abs_iff, h],
  unfold tsum,
  simp [h, this],
end

lemma summable_of_eventually_zero
{f : ℕ → ℝ}
(hf : ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → f n = 0)
:
summable f
:=
begin
  cases hf with N hN,
  rw summable_iff_vanishing,
  intros s hs,
  use finset.range N,
  intros t ht,
  have aa : t = t, exact rfl,
  have bb : ∀ (x : ℕ), x ∈ t → f x = 0,
  {
    intros x hx,
    have : N ≤ x, {
      rw finset.disjoint_iff_ne at ht,
      by_contradiction H,
      push_neg at H,
      exact ht x hx x (by simp [H]) rfl,
    },
    exact hN x this,
  },
  rw finset.sum_congr aa bb,
  simp,
  exact mem_of_mem_nhds hs,
end

lemma head_summable
{n : ℕ}
{f : ℕ → ℝ}
:
summable (λ (i : ℕ), ite (i ≤ n) (f i) 0)
:=
begin
  apply summable_of_eventually_zero,
  use n + 1,
  intros n' hn',
  have : ¬ n' ≤ n,
    by_contradiction H,
    linarith,
  simp [this],
end

lemma finite_diff_summable_aux
{f : ℕ → ℝ}
{g : ℕ → ℝ}
(hfg : ∃ (s : finset ℕ), ∀ (i : ℕ), i ∉ s → f i = g i)
:
summable f → summable g
:=
begin
  intros hf,
  have : summable (λ (b : ℕ), g b - f b),
  {
    apply summable_of_eventually_zero,
    cases hfg with s hs,
    by_cases s = ∅,
    simp [h] at hs,
    use 1, intros i hi, simp [hs i],
    have : s.nonempty, exact nonempty_iff_ne_empty.mpr h,
    use (max' s this) + 1,
    intros i hi,
    have : i ∉ s, exact not_mem_if_gt_max' (calc s.max' this < s.max' this + 1 : by linarith ... ≤ i : hi),
    simp [hs i this],
  },
  exact summable.trans_sub hf this,
end

lemma finite_diff_summable
{f : ℕ → ℝ}
{g : ℕ → ℝ}
(hfg : ∃ (s : finset ℕ), ∀ (i : ℕ), i ∉ s → f i = g i)
:
summable f ↔ summable g
:=
begin
  split,
  intros hf,
  exact finite_diff_summable_aux hfg hf,

  intros hg,
  have hfg' : ∃ (s : finset ℕ), ∀ (i : ℕ), i ∉ s → g i = f i,
    cases hfg with s hs,
    use s,
    intros i hi,
    exact (hs i hi).symm,
  exact finite_diff_summable_aux hfg' hg,
end

lemma tail_summable
{n : ℕ}
{f : ℕ → ℝ}
(hf : summable f)
:
summable (λ (i : ℕ), ite (n < i) (f i) 0)
:=
begin
  have : ∃ (s : finset ℕ), ∀ (i : ℕ), i ∉ s → (λ (i : ℕ), ite (n < i) (f i) 0) i = f i,
  {
    use finset.range (n + 1),
    intros i hi,
    rw finset.mem_range at hi,
    simp [hi],
    intros hn,
    linarith,
  },
  rw finite_diff_summable this,
  simp [hf],
end


lemma head_summable'
{n : ℕ}
{f : ℕ → ℝ}
:
summable (λ (i : ℕ), ite (i < n) (f i) 0)
:=
begin
  apply summable_of_eventually_zero,
  use n + 1,
  intros n' hn',
  have : ¬ n' < n,
    by_contradiction H,
    linarith,
  simp [this],
end

lemma single_summable
{n : ℕ}
{f : ℕ → ℝ}
:
summable (λ (i : ℕ), ite (i = n) (f i) 0)
:=
begin
  apply summable_of_eventually_zero,
  use n + 1,
  intros n' hn',
  have : n' ≠ n,
    by_contradiction H,
    linarith,
  simp [this],
end

lemma tsum_head_succ
{n : ℕ}
{f : ℕ → ℝ}
:
∑' (i : ℕ), ite (i ≤ n.succ) (f i) 0 = ∑' (i : ℕ), ite (i ≤ n) (f i) 0 + f n.succ
:=
begin
  have h : ∀ (i : ℕ), ite (i ≤ n.succ) (f i) 0 = ite (i ≤ n) (f i) 0 + ite (i = n.succ) (f i) 0,
    intros i,
    by_cases i ≤ n,
      simp [h],
      have : i ≤ n.succ, calc i ≤ n : h ... ≤ n.succ : le_succ n,
      simp [this],
      intros h',
      exfalso,
      have : i < n.succ, calc i ≤ n : h ... < n.succ : lt_succ_self n,
      linarith,
    by_cases h' : i = n.succ,
      simp [le_of_eq h', h'],
      intros h'',
      exfalso,
      linarith [calc n.succ ≤ n : h'' ... < n.succ : lt_succ_self n],

    have : n.succ < i,
    {
      push_neg at h,
      have : n.succ ≤ i, exact succ_le_iff.mpr h,
      exact (ne.symm h').le_iff_lt.mp this,
    },
    simp [h, h'],
    intros h'',
    exfalso,
    linarith,
  conv {
    to_lhs,
    congr,
    funext,
    rw h i,
  },
  rw tsum_add,
  conv {
    to_lhs,
    congr,
    skip,
    congr,
    funext,
    rw ite_const_rw,
  },
  rw tsum_ite_eq _ (f n.succ),
  exact head_summable,
  exact single_summable,
end

lemma tsum_sub_head_eq_tail
{n : ℕ}
{f : ℕ → ℝ}
:
-- must be summable or else 0s mess things up
summable f → ∑' (i : ℕ), f i - ∑' (i : ℕ), ite (i ≤ n) (f i) 0 = ∑' (i : ℕ), ite (n < i) (f i) 0
:=
begin
  intros hf,
  induction n with n hn,
  simp,
  rw tsum_ite_eq_extract hf 0,
  have : ∀ (i : ℕ), ite (i = 0) (f i) 0 = ite (i = 0) (f 0) 0,
    intros i, by_cases i = 0, simp [h], simp [h],
  conv {
    to_lhs,
    congr,
    skip,
    congr,
    funext,
    rw this i,
  },
  rw tsum_ite_eq,
  simp,
  have : ∀ (i : ℕ), ite (i = 0) 0 (f i) = ite (0 < i) (f i) 0,
    intros i, by_cases i = 0, simp [h], simp [h, zero_lt_iff.mpr h],
  conv {
    to_rhs,
    congr,
    funext,
    rw ← this i,
  },
  rw tsum_head_succ,
  have : ∑' (i : ℕ), f i - (∑' (i : ℕ), ite (i ≤ n) (f i) 0 + f n.succ) = (∑' (i : ℕ), f i - ∑' (i : ℕ), ite (i ≤ n) (f i) 0) - f n.succ, ring,
  rw this,
  rw hn,
  have : f n.succ = ∑' (i : ℕ), ite (i = n.succ) (f n.succ) 0, exact (tsum_ite_eq n.succ (f n.succ)).symm,
  rw this,
  rw ← tsum_sub,
  congr,
  funext,
  by_cases b = n.succ,
    simp [h, lt_succ_self n],

    by_cases h' : n < b,
      have : n.succ < b,
      {
        have : n.succ ≤ b, exact succ_le_iff.mpr h',
        exact lt_of_le_of_ne this (ne.symm h),
      },
      simp [h, h', this],

      have : ¬ n.succ < b, {
        push_neg,
        push_neg at h',
        calc b ≤ n : h' ... ≤ n.succ : le_succ n,
      },
      simp [h, h', this],
      exact tail_summable hf,
      exact single_summable,
end

lemma not_summable_eq_zero
{f : ℕ → ℝ}
(hf : ¬ summable f)
:
∑' (i : ℕ), f i = 0
:=
begin
  unfold tsum,
  simp [hf],
end

end squarefree_sums
