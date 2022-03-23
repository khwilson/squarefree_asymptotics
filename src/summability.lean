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
import analysis.p_series
import general

noncomputable theory
open nat finset function filter
open_locale topological_space interval big_operators filter asymptotics arithmetic_function

namespace squarefree_sums

lemma not_summable_eq_zero {f : ℕ → ℝ} (hf : ¬ summable f) : ∑' (i : ℕ), f i = 0 :=
begin
  unfold tsum,
  simp only [hf, dif_neg, not_false_iff],
end

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

lemma abs_tsum_le_tsum_abs {f : ℕ → ℝ} : | ∑' i, f i | ≤ (∑' i, |f i|) :=
begin
  by_cases h : summable f,
  { obtain ⟨d, hd⟩ := summable_abs_iff.mpr h,
    obtain ⟨c, hc⟩ := h,
    rw [hc.tsum_eq, hd.tsum_eq],
    apply le_of_tendsto_of_tendsto ((continuous_abs.tendsto c).comp hc) hd,
    apply eventually_of_forall,
    intros s,
    exact finset.abs_sum_le_sum_abs _ s, },
  { unfold tsum,
    simp [h, (not_iff_not.mpr summable_abs_iff).mpr h], },
end

lemma abs_tsum_nonneg_eq_tsum
{f : ℕ → ℝ}
(hf : ∀ (n : ℕ), 0 ≤ f n)
:
|∑' (i : ℕ), f i| = ∑' (i : ℕ), f i
:=
begin
  by_cases h : summable f,
  { obtain ⟨c, hc⟩ := h,
    rw has_sum.tsum_eq hc,
    exact abs_of_nonneg (has_sum_mono has_sum_zero hc hf), },
  { simp [h, not_summable_eq_zero], },
end

lemma summable_of_eventually_zero
{N : ℕ}
{f : ℕ → ℝ}
(hf : ∀ (n : ℕ), N ≤ n → f n = 0)
:
summable f
:=
begin
  have : ∀ (b : ℕ), b ∉ finset.Ico 0 N → f b = 0,
  {
    intros b hb,
    simp at hb,
    exact hf b hb,
  },
  exact summable_of_ne_finset_zero this,
end

lemma tsum_of_eventually_zero_eq_finset_sum
{N : ℕ}
{f : ℕ → ℝ}
(hf : ∀ (n : ℕ), N ≤ n → f n = 0)
:
∑' i, f i = ∑ (i : ℕ) in finset.Ico 0 N, f i
:=
begin
  obtain ⟨c, hc⟩ := summable_of_eventually_zero hf,
  rw has_sum.tsum_eq hc,
  have : ∀ (b : ℕ), b ∉ finset.Ico 0 N → f b = 0,
  {
    intros b hb,
    simp at hb,
    exact hf b hb,
  },
  exact has_sum.unique hc (has_sum_sum_of_ne_finset_zero this),
end


lemma head_summable
{n : ℕ}
{f : ℕ → ℝ}
:
summable (λ (i : ℕ), ite (i ≤ n) (f i) 0)
:=
begin
  apply @summable_of_eventually_zero (n + 1),
  intros n' hn',
  have : ¬ n' ≤ n,
    by_contradiction H,
    linarith,
  simp [this],
end

lemma head_sum_eq
{n : ℕ}
{f : ℕ → ℝ}
:
∑' (i : ℕ), ite (i ≤ n) (f i) 0 = ∑ (i : ℕ) in finset.Icc 0 n, f i
:=
begin
  have : ∀ (m : ℕ), n + 1 ≤ m → (λ i, ite (i ≤ n) (f i) 0) m = 0, {
    intros m hm,
    simp,
    intros xf,
    exfalso,
    linarith,
  },
  rw tsum_of_eventually_zero_eq_finset_sum this,
  have : finset.Ico 0 (n + 1) = finset.Icc 0 n, {
    ext x,
    simp,
    exact lt_succ_iff,
  },
  rw this,
  refine sum_congr rfl _,
  intros x hx,
  simp at hx,
  simp [hx],
end

lemma head_sum_eq'
{n : ℕ}
{f : ℕ → ℝ}
:
∑' (i : ℕ), ite (i < n) (f i) 0 = ∑ (i : ℕ) in finset.Ico 0 n, f i
:=
begin
  have : ∀ (m : ℕ), n ≤ m → (λ i, ite (i < n) (f i) 0) m = 0, {
    intros m hm,
    simp,
    intros xf,
    exfalso,
    linarith,
  },
  rw tsum_of_eventually_zero_eq_finset_sum this,
  refine sum_congr rfl _,
  intros x hx,
  simp at hx,
  simp [hx],
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
    cases hfg with s hs,
    by_cases s = ∅,
    apply @summable_of_eventually_zero 1,
    simp [h] at hs,
    intros i hi, simp [hs i],
    have : s.nonempty, exact nonempty_iff_ne_empty.mpr h,
    apply @summable_of_eventually_zero ((max' s this) + 1),
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

lemma tail_summable'
{n : ℕ}
{f : ℕ → ℝ}
(hf : summable f)
:
summable (λ (i : ℕ), ite (n ≤ i) (f i) 0)
:=
begin
  have : ∃ (s : finset ℕ), ∀ (i : ℕ), i ∉ s → (λ (i : ℕ), ite (n ≤ i) (f i) 0) i = f i,
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
  apply @summable_of_eventually_zero n,
  intros n' hn',
  simp [hn'],
  intros hn'',
  linarith,
end

lemma single_summable
{n : ℕ}
{f : ℕ → ℝ}
:
summable (λ (i : ℕ), ite (i = n) (f i) 0)
:=
begin
  apply @summable_of_eventually_zero (n + 1),
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
  rw sub_eq_iff_eq_add,
  rw ← tsum_add,
  congr,
  funext,
  by_cases h : n < i,
    simp [h], intros hi, exfalso, exact ne_of_lt (calc n < i : h ... ≤ n : hi) rfl,

    push_neg at h,
    simp [h], intros hi, exfalso, exact ne_of_lt (calc n < i : hi ... ≤ n : h) rfl,

  exact tail_summable hf,
  exact head_summable,
end

lemma tsum_sub_head_eq_tail_lt
{n : ℕ}
{f : ℕ → ℝ}
:
-- must be summable or else 0s mess things up
summable f → ∑' (i : ℕ), f i - ∑' (i : ℕ), ite (i < n) (f i) 0 = ∑' (i : ℕ), ite (n ≤ i) (f i) 0
:=
begin
  intros hf,
  rw sub_eq_iff_eq_add,
  rw ← tsum_add,
  congr,
  funext,
  by_cases h : n ≤ i,
    simp [h], intros hi, exfalso, exact ne_of_lt (calc n ≤ i : h ... < n : hi) rfl,

    push_neg at h,
    simp [h], intros hi, exfalso, exact ne_of_lt (calc n ≤ i : hi ... < n : h) rfl,

  exact tail_summable' hf,
  exact head_summable',
end

lemma ite_floor_le' {b c d : ℝ}
(hb : 0 ≤ b) :
∀ (n : ℕ), ite (↑n ≤ b) c d = ite (n ≤ ⌊b⌋₊) c d :=
begin
  intros n,
  by_cases h : ↑n ≤ b,
    simp [h, le_floor h],
    push_neg at h,
    simp [not_le.mpr h, not_le.mpr ((floor_lt hb).mpr h)],
end

lemma ite_floor_le {b c d : ℝ}
(hb : 0 ≤ b) :
(λ (n : ℕ), ite (↑n ≤ b) c d) = (λ (n : ℕ), ite (n ≤ ⌊b⌋₊) c d) :=
begin
  ext n,
  exact ite_floor_le' hb n,
end

lemma ite_lt_floor' {b c d : ℝ}
(hb : 0 ≤ b) :
∀ (n : ℕ), ite (b < ↑n) c d = ite (⌊b⌋₊ < n) c d :=
begin
  intros n,
  by_cases h : b < ↑n,
    simp [h, (floor_lt hb).mpr h],
    push_neg at h,
    simp [not_lt.mpr h, not_lt.mpr (le_floor h)],
end

lemma ite_lt_floor {b c d : ℝ}
(hb : 0 ≤ b) :
(λ (n : ℕ), ite (b < ↑n) c d) = (λ (n : ℕ), ite (⌊b⌋₊ < n) c d) :=
begin
  ext n,
  exact ite_lt_floor' hb n,
end


lemma tsum_sub_head_eq_tail'
{b : ℝ}
{f : ℝ → ℝ}
(hb : 0 ≤ b)
:
summable (λ (i : ℕ), f ↑i) → ∑' (i : ℕ), f ↑i - ∑' (i : ℕ), ite (↑i ≤ b) (f i) 0 = ∑' (i : ℕ), ite (b < ↑i) (f ↑i) 0
:=
begin
  let g : ℕ → ℝ := (λ n, f ↑n),
  have gequiv : g = (λ n, f ↑n), refl,
  have gequiv' : ∀ (n : ℕ), g n = f ↑n, intros n, refl,
  rw ← gequiv,
  intros hg,
  conv {
    congr,congr,skip,congr,funext, rw ← gequiv' i, skip, congr, funext, rw ← gequiv' i,
  },
  conv {
    congr,congr,skip,funext,congr, funext, rw ite_floor_le' hb i,
    skip, congr, funext, rw ite_lt_floor' hb i,
  },
  exact tsum_sub_head_eq_tail hg,
end

lemma shift_sum
{a b d : ℕ}
{f : ℕ → ℝ}
:
∑ (i : ℕ) in finset.Ico (a + d) (b + d), f i = ∑ (i : ℕ) in finset.Ico a b, f (i + d)
:=
begin
  apply finset.sum_bij (λ (i : ℕ) (hi : i ∈ finset.Ico (a + d) (b + d)), i - d),
  intros m hm, simp, simp at hm, split,
  let blah := nat.sub_le_sub_right hm.left d, rw nat.add_sub_cancel at blah, exact blah,
  have : m - d + d < b + d → m - d < b, simp,
  apply this,
  have : d ≤ m, calc d ≤ a + d : by simp ... ≤ m : hm.left,
  rw nat.sub_add_cancel this,
  exact hm.right,

  intros m hm, simp, congr, symmetry, apply nat.sub_add_cancel, simp at hm, calc d ≤ a + d : by simp ... ≤ m : hm.left,

  intros m n hm hn, simp, simp at hm, simp at hn,
  have : d ≤ m, calc d ≤ a + d : by simp ... ≤ m : hm.left,
  rw nat.sub_eq_iff_eq_add this,
  have : d ≤ n, calc d ≤ a + d : by simp ... ≤ n : hn.left,
  rw nat.sub_add_cancel this,
  intros h, exact h,

  intros m hm, use m + d,
  have : m + d ∈ finset.Ico (a + d) (b + d), {
    simp at hm,
    simp [hm],
  },
  use this,
  simp,
end


end squarefree_sums
