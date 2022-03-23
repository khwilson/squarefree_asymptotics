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
-- open_locale classical
open nat finset list finsupp set function filter measure_theory
open_locale classical topological_space interval big_operators filter ennreal asymptotics

namespace squarefree_sums

lemma const_eq_integral_const_on_unit_interval (a : ℕ) (b : ℝ) : ∫ (x : ℝ) in a..(a + 1), b = b :=
begin
  simp,
end

lemma measure_subset_null (s t : set ℝ) : s ⊆ t →  measure_theory.measure_space.volume t = 0 → measure_theory.measure_space.volume s = 0 :=
begin
  intros h ht,
  let foo := measure_theory.outer_measure.mono' measure_theory.measure_space.volume.to_outer_measure h,
  have om_t: measure_theory.measure_space.volume t = measure_theory.measure_space.volume.to_outer_measure t, simp,
  rw om_t at ht,
  have om_s: measure_theory.measure_space.volume s = measure_theory.measure_space.volume.to_outer_measure s, simp,
  rw om_s,
  have aa : 0 ≤ measure_theory.measure_space.volume.to_outer_measure s, simp,
  have bb : measure_theory.measure_space.volume.to_outer_measure s ≤ 0,
    calc measure_theory.measure_space.volume.to_outer_measure s ≤ measure_theory.measure_space.volume.to_outer_measure t : foo
      ... = 0 : ht,
  -- Why doesn't squeezing just work? Seems like this should be a lot simpler
  apply eq_iff_le_not_lt.mpr,
  split,
  exact bb,
  push_neg,
  exact aa,
end

lemma foooo {a b : ℝ} (hab : a < b): (set.Ioo a b)ᶜ ∩ (set.Ioc a b) = {b} :=
begin
  ext,
  rw mem_singleton_iff,
  simp only [set.mem_Ioc, set.mem_Ioo, mem_inter_eq, not_and, not_lt, mem_compl_eq],
  split,
  { rintros ⟨ha, hb, hc⟩, linarith [hc, ha hb], },
  { intros h, exact ⟨λ _, h.symm.le, lt_of_lt_of_le hab h.symm.le, h.le⟩, },
end

lemma real_constant_on_interval_integrable
(a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : ∃c, ∀ (x : ℝ), x ∈ set.Ioo a b → f x = c) :
interval_integrable f real.measure_space.volume a b :=
begin
  rw interval_integrable_iff,
  rcases hf with ⟨c, hc⟩,
  have : measure_theory.integrable_on (λ x, c) (set.interval_oc a b) real.measure_space.volume,
  { exact continuous_const.integrable_on_interval_oc, },
  apply measure_theory.integrable_on.congr_fun' this,
  rw eventually_eq_iff_exists_mem,
  use set.Ioo a b,
  split,
  { rw mem_ae_iff,
    simp only [measurable_set.compl_iff, measurable_set_Ioo, measure.restrict_apply],
    rw [interval_oc_of_le (le_of_lt hab), foooo hab],
    exact real.volume_singleton, },
  { intros x hx, exact (hc x hx).symm, },
end

lemma interval_integrable.trans_iterate'
  {α : Type*} [linear_order α] [measurable_space α] [topological_space α] [order_closed_topology α] [opens_measurable_space α]
  {ν : measure α}
  {a : ℕ → α} {m n : ℕ}
  {f : α → ℝ}
  (hint : ∀ (k : ℕ), (k < m + n) → interval_integrable f ν (a k) (a $ k+1)) :
  interval_integrable f ν (a m) (a (m + n)) :=
begin
  induction n with n hn,
  { simp },
  {
    have :  ∀ (k : ℕ), k < m + n → interval_integrable f ν (a k) (a (k + 1)),
    intros k hk,
    have : k < m + n.succ, {
      transitivity,
      exact hk,
      apply nat.add_lt_add_left,
      rw lt_succ_iff,
    },
    exact hint k this,
    specialize hn this,
    exact interval_integrable.trans hn (hint (m + n) (by {apply nat.add_lt_add_left, rw lt_succ_iff})),
  },
end

lemma sum_integral_adjacent_intervals'
  {α : Type*} [linear_order α] [measurable_space α] [topological_space α] [order_closed_topology α] [opens_measurable_space α]
  {ν : measure α}
  {a : ℕ → α} {m n : ℕ}
  {f : α → ℝ}
  (hint : ∀ (k : ℕ), (k < m + n) → interval_integrable f ν (a k) (a $ k+1)) :
  ∑ (k : ℕ) in finset.Ico m (m + n), ∫ x in (a k)..(a $ k+1), f x ∂ν = ∫ x in (a m)..(a (m + n)), f x ∂ν :=
begin
  induction n with n hn,
  { simp, },
  have : m + n.succ = (m + n).succ, exact add_succ m n,
  rw this,
  rw finset.sum_Ico_succ_top,
  rw hn,
  apply interval_integral.integral_add_adjacent_intervals,
  have : ∀ (k : ℕ), k < m + n → interval_integrable f ν (a k) (a (k + 1)),
  { intros k hk,
    have : k < m + n.succ, calc k < m + n : hk ... < m + n.succ : nat.add_lt_add_left (lt_succ_self n) m,
    exact hint k this, },
  apply interval_integrable.trans_iterate',
  intros k hk, exact this k hk,
  exact hint (m + n) (nat.add_lt_add_left (lt_succ_self n) m),
  intros k hk,
  exact hint k (by calc k < m + n : hk ... < m + n.succ : nat.add_lt_add_left (lt_succ_self n) m),
  simp,
end

lemma sum_integral_adjacent_intervals''
  {α : Type*} [linear_order α] [measurable_space α] [topological_space α] [order_closed_topology α] [opens_measurable_space α]
  {ν : measure α}
  {a : ℕ → α} {m n : ℕ}
  {f : α → ℝ}
  (hmn : m ≤ n)
  (hint : ∀ (k : ℕ), (k < n) → interval_integrable f ν (a k) (a $ k+1)) :
  ∑ (k : ℕ) in finset.Ico m n, ∫ x in (a k)..(a $ k+1), f x ∂ν = ∫ x in (a m)..(a n), f x ∂ν :=
begin
  have : n = m + (n - m), {
    zify,
    ring,
  },
  rw this, rw this at hint,
  exact sum_integral_adjacent_intervals' hint,
end

lemma convert_finite_sum_to_interval_integral' {m n : ℕ} {f : ℝ → ℝ} (hmn : m ≤ n) :
∑ (i : ℕ) in finset.Ico m n,
∫ (x : ℝ) in ↑i..↑i + 1,
f ↑i
=
∫ (x : ℝ) in m..n, f ↑⌊x⌋₊
:=
begin
  let g : ℝ → ℝ := (λ x, f ↑⌊x⌋₊),
  -- Problem: There are a lot of lemmas that show that if a function is constant
  -- on all of ℝ then the function is integrable, but this function is constant _only_
  -- on the interval of integration. This is messing up the parser.
  have hint : ∀ (k : ℕ), k < n → interval_integrable g measure_theory.measure_space.volume (k : ℝ) ((k : ℝ) + 1),
  {
    intros k hk,
    have : ∃c, ∀ (x : ℝ), x ∈ set.Ioo (k : ℝ) (↑k + 1) → g x = c, {
      use f k,
      intros x hx,
      simp [g],
      rw floor_of_unit_Ioo_val hx,
    },
    exact real_constant_on_interval_integrable k (k + 1) (by linarith) g this,
  },
  have t1 : ∀ (i : ℕ), (i : ℝ) ≤ ↑i + 1, {
    intros i,
    simp,
  },
  have : ∀ (i : ℕ), ∫ (x : ℝ) in ↑i..↑i + 1, f ↑i = ∫ (x : ℝ) in ↑i..↑i + 1, f ⌊x⌋₊, {
    intros i,
    rw interval_integral.integral_of_le (t1 i),
    rw interval_integral.integral_of_le (t1 i),
    rw integral_Ioc_eq_integral_Ioo,
    rw integral_Ioc_eq_integral_Ioo,
    apply integral_congr_ae,
    rw filter.eventually_eq_iff_exists_mem,
    use set.Ioo (i : ℝ) (↑i + 1),
    split,
    rw mem_ae_iff,
    simp,
    unfold eq_on,
    intros x hx,
    rw floor_of_unit_Ioo_val hx,
  },
  conv {
    to_lhs,
    congr,
    skip,
    funext,
    rw this i,
  },
  exact sum_integral_adjacent_intervals'' hmn hint,
end

lemma antitone_integral_le_sum
{a b : ℕ}
{f : ℝ → ℝ}
(hab : a ≤ b)
(hf : antitone_on f (set.Icc a b)) :
∫ x in a..b, f x ≤ ∑ x in finset.Ico a b, f x :=
begin
  -- This (a : ℝ) is necessary or else confusion happens
  have : ∀ (x : ℝ), x ∈ set.Icc (a : ℝ) ↑b → f x ≤ f ⌊x⌋₊, {
    intros x hx,
    apply hf,
    exact floor_of_Icc_mem_Icc hx,
    exact hx,
    have : ↑a ≤ x, {
      simp at hx,
      exact hx.left,
    },
    have : 0 ≤ x, calc (0 : ℝ) ≤ ↑a : by simp ... ≤ x : this,
    exact floor_le this,
  },
  transitivity,
  refine interval_integral.integral_mono_on (cast_le.mpr hab) _ _ this,
  apply antitone_on.interval_integrable,
  simp,
  rwa interval_eq_Icc (cast_le.mpr hab),
  apply antitone_on.interval_integrable,
  rwa interval_eq_Icc (cast_le.mpr hab),
  unfold antitone_on,
  intros c hc d hd hcd,
  have u1 : (⌊c⌋₊ : ℝ) ≤ ⌊d⌋₊, {
    rw cast_le,
    exact floor_mono hcd,
  },
  have u2 : ↑⌊c⌋₊ ∈ set.Icc (a : ℝ) ↑b, exact floor_of_Icc_mem_Icc hc,
  have u3 : ↑⌊d⌋₊ ∈ set.Icc (a : ℝ) ↑b, exact floor_of_Icc_mem_Icc hd,
  exact hf u2 u3 u1,
  conv {
    to_rhs,
    congr,
    skip,
    funext,
    rw ← const_eq_integral_const_on_unit_interval x (f ↑x),
  },
  rw convert_finite_sum_to_interval_integral' hab,
end

lemma somethingblah
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ioo (a : ℝ) ↑b → (⌊x⌋₊ : ℝ) + 1 ∈ set.Icc (a : ℝ) ↑b
:=
begin
  simp,
  intros is_gt is_lt,
  have : (1 : ℝ) = ↑(1 : ℕ), simp,
  split,
  rw this,
  rw ← cast_add,
  rw cast_le,
  calc a ≤ ⌊x⌋₊ : le_floor (le_of_lt is_gt) ... ≤ ⌊x⌋₊ + 1 : le_succ ⌊x⌋₊,
  rw this,
  rw ← cast_add,
  rw cast_le,
  have zero_le_x : 0 ≤ x,
  {
    have : 0 ≤ a, by simp,
    calc (0 : ℝ) ≤ ↑a : cast_le.mpr this ... ≤ x : le_of_lt is_gt,
  },
  have : ⌊x⌋₊ < b, {
    exact cast_lt.mp (calc ↑⌊x⌋₊ ≤ x : floor_le zero_le_x ... < ↑b : is_lt),
  },
  exact succ_le_of_lt this,
end

lemma castalot
{a : ℕ} :
⌊(a : ℝ)⌋₊ = a :=
begin
  simp,
end

lemma mem_Ico_Ioo
{a b c : ℝ}
(hc : c ∈ set.Ico a b)
(hc' : c ≠ a) :
c ∈ set.Ioo a b :=
begin
  simp,
  simp at hc,
  cases hc with ha hb,
  exact ⟨lt_of_le_of_ne ha hc'.symm, hb⟩,
end

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

lemma somethingblah'
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ico (a : ℝ) ↑b → (⌊x⌋₊ : ℝ) + 1 ∈ set.Icc (a : ℝ) ↑b
:=
begin
  intros hx,
  have hab : a < b,
  {
    simp at hx,
    exact cast_lt.mp (calc ↑a ≤ x : hx.left ... < b : hx.right),
  },
  by_cases h : x = ↑a,
  {
    simp,
    split,
    rw [h, castalot], norm_cast, exact le_succ a,
    rw [h, castalot], norm_cast, exact succ_le_of_lt hab,
  },
  {
    exact somethingblah (mem_Ico_Ioo hx h),
  },
end

lemma fooooo
{x y : ℝ}
{a b : ℕ}
{f : ℝ → ℝ}
(hxy : x ≤ y)
(hf : antitone_on f (set.Icc (a : ℝ) ↑b))
(hx : x ∈ set.Icc (a : ℝ) ↑b)
(hy : y ∈ set.Icc (a : ℝ) ↑b) :
ite (⌊y⌋₊ + 1 ≤ b) (f ↑(⌊y⌋₊ + 1)) (f ↑b) ≤ ite (⌊x⌋₊ + 1 ≤ b) (f ↑(⌊x⌋₊ + 1)) (f ↑b)
:=
begin
  by_cases hy' : y = ↑b,
  {
    have : ¬ (⌊y⌋₊ + 1  ≤ b), rw hy', rw castalot, simp,
    simp [this],
    by_cases hx' : x = ↑b,
      have : ¬ (⌊x⌋₊ + 1  ≤ b), rw hx', rw castalot, simp,
      simp [this],

      have xxx : ↑(⌊x⌋₊ + 1) ∈ set.Icc (a : ℝ) ↑b, exact somethingblah' (mem_Icc_Ico hx hx'),
      have bbb : ↑b ∈ set.Icc (a : ℝ) ↑b,
      {
        simp,
        simp at hx,
        exact cast_le.mp (calc ↑a ≤ x : hx.left ... ≤ ↑b : hx.right),
      },
      have : ⌊x⌋₊ + 1 ≤ b, simp at xxx, norm_cast at xxx, exact xxx.right,
      simp [this],
      exact hf xxx bbb (cast_le.mpr this),
  },
  {
    have : y ∈ set.Ico (a : ℝ) ↑b, exact mem_Icc_Ico hy hy',
    have hy_icc : ↑(⌊y⌋₊ + 1) ∈ set.Icc (a : ℝ) ↑b, exact somethingblah' this,
    have hy_le_b : ⌊y⌋₊ + 1 ≤ b, { simp at hy_icc, norm_cast at hy_icc, exact hy_icc.right, },

    have hxy' : ⌊x⌋₊ + 1 ≤ ⌊y⌋₊ + 1,
    {
      have : ⌊x⌋₊ ≤ ⌊y⌋₊, exact floor_mono hxy,
      linarith [this],
    },

    have : x ≠ ↑b, apply ne_of_lt, simp at this, calc x ≤ y : hxy ... < ↑b : this.right,
    have : x ∈ set.Ico (a : ℝ) ↑b, exact mem_Icc_Ico hx this,
    have hx_icc: ↑(⌊x⌋₊ + 1) ∈ set.Icc (a : ℝ) ↑b, exact somethingblah' this,
    have hx_le_b : ⌊x⌋₊ + 1 ≤ b, { simp at hx_icc, norm_cast at hx_icc, exact hx_icc.right, },

    simp [hx_le_b, hy_le_b],
    exact hf hx_icc hy_icc (cast_le.mpr hxy'),
  },

end

lemma antitone_sum_le_integral
{a b : ℕ}
{f : ℝ → ℝ}
(hab : a ≤ b)
(hf : antitone_on f (set.Icc a b))
:
∑ x in finset.Ico (a + 1) (b + 1), f x  ≤ ∫ x in a..b, f x :=
begin
  rw shift_sum,
  have hf' : antitone_on f (set.Ioo (a : ℝ) ↑b), {
    intros x hx y hy hxy,
    apply hf,
    exact mem_Ioo_mem_Icc hx,
    exact mem_Ioo_mem_Icc hy,
    exact hxy,
  },
  have hf_integrable : integrable_on f (set.Ioo (a : ℝ) ↑b), {
    by_cases hab' : a = b, simp [hab'],
    have hab' : a < b, exact lt_of_le_of_ne hab hab',
    let blah := hf,
    rw ← interval_eq_Icc (cast_le.mpr hab) at blah,
    let foo := antitone_on.interval_integrable blah,
    unfold interval_integrable at foo,
    rcases foo with ⟨lfoo, rfoo⟩,
    have : set.Ioc (a : ℝ) ↑b = (set.Ioo (a : ℝ) ↑b) ∪ {(b : ℝ)},
    {
      ext,
      simp,
      split,
      rintros ⟨is_gt, is_lt⟩,
      by_cases h : x = ↑b, simp [h],
      right,
      split,
      exact is_gt,
      exact lt_of_le_of_ne is_lt h,
      intros h,
      cases h,
      rw h,
      split,
      exact cast_lt.mpr hab',
      simp,
      split,
      exact h.left,
      exact le_of_lt h.right,
    },
    rw this at lfoo,
    exact integrable_on.left_of_union lfoo,
    apply is_locally_finite_measure_of_is_finite_measure_on_compacts,
  },

  let g := (λ (i : ℝ), f (i + 1)),
  have gequiv : ∀ (i : ℕ), g ↑i = f ↑(i + 1), simp,
  conv {
    to_lhs,
    congr,
    skip,
    funext,
    rw ← gequiv i,
  },

  have hg_integrable : integrable_on (λ (x : ℝ), g ↑⌊x⌋₊) (Ioo (a : ℝ) ↑b),
  {
    by_cases hab' : a = b, simp [hab'],
    have hab' : a < b, exact lt_of_le_of_ne hab hab',
    let h := (λ x : ℝ, ite (⌊x⌋₊ + 1 ≤ b) (f ↑(⌊x⌋₊ + 1)) (f ↑b)),
    have hequiv : ∀ (x : ℝ), h x = ite (⌊x⌋₊ + 1 ≤ b) (f ↑(⌊x⌋₊ + 1)) (f ↑b), { intros x, by_cases hh : ⌊x⌋₊ + 1 ≤ b, simp [h, hh],},
    have : eq_on h (λ x : ℝ, g ↑⌊x⌋₊) (set.Ioo (a : ℝ) ↑b),
    {
      unfold eq_on,
      intros x hx,
      have : ⌊x⌋₊ + 1 ≤ b, {
        have foo : (⌊x⌋₊ : ℝ) + 1 ∈ set.Icc (a : ℝ) ↑b, exact somethingblah hx,
        simp at foo,
        have : (1 : ℝ) = ↑(1 : ℕ), simp,
        rw this at foo,
        rw ← cast_add at foo,
        rw cast_le at foo,
        rw cast_le at foo,
        exact foo.right,
      },
      rw hequiv x,
      rw gequiv ⌊x⌋₊,
      simp [this],
    },
    refine integrable_on.congr_fun _ this (by simp),
    have : set.Ioc (a : ℝ) ↑b =ᵐ[real.measure_space.volume] set.Ioo (a : ℝ) ↑b,
    {
      rw filter.eventually_eq_set,
      rw filter.eventually_iff,
      rw measure_theory.mem_ae_iff,
      have : {x : ℝ | x ∈ set.Ioc (a : ℝ) ↑b ↔ x ∈ Ioo (a : ℝ) ↑b}ᶜ ⊆ {(b : ℝ)}, {
        rw compl_subset_iff_union,
        ext,simp,
        by_cases hhh : x = ↑b,
        simp [hhh],
        right,
        intros nope,
        split,
        intros xxx,
        exact lt_of_le_of_ne xxx hhh,
        intros xxx,
        exact le_of_lt xxx,
      },
      exact measure_subset_null _ {(b : ℝ)} this real.volume_singleton,
    },
    refine integrable_on.congr_set_ae _ this.symm,
    have : antitone_on h (set.Icc (a : ℝ) ↑b),
    {
      intros x hx y hy hxy,
      rw hequiv x, rw hequiv y,
      exact fooooo hxy hf hx hy,
    },
    rw ← interval_eq_Icc (cast_le.mpr hab) at this,
    let blah := antitone_on.interval_integrable this,
    unfold interval_integrable at blah,
    rcases blah with ⟨lfoo, rfoo⟩,
    exact lfoo,
    apply is_locally_finite_measure_of_is_finite_measure_on_compacts,
  },

  have : ∀ (x : ℝ), x ∈ set.Icc (a : ℝ) ↑b → f ⌈x⌉₊ ≤ f x, {
    intros x hx,
    apply hf,
    exact hx,
    exact ceil_of_Icc_mem_Icc hx,
    exact le_ceil x,
  },
  conv {
    to_lhs,
    congr,
    skip,
    funext,
    rw ← const_eq_integral_const_on_unit_interval i (g ↑i),
  },
  rw convert_finite_sum_to_interval_integral' hab,
  have hab' : (a : ℝ) ≤ ↑b, exact cast_le.mpr hab,
  rw interval_integral.integral_of_le hab',
  rw interval_integral.integral_of_le hab',
  rw integral_Ioc_eq_integral_Ioo,
  rw integral_Ioc_eq_integral_Ioo,
  apply set_integral_mono_on,
  simp,
  exact hg_integrable,
  simp, exact hf_integrable,

  simp,

  intros x hx, conv { to_lhs, rw gequiv ⌊x⌋₊},
  apply hf,
  exact mem_Ioo_mem_Icc hx,
  exact somethingblah hx,
  apply le_of_lt,
  exact nat.lt_succ_floor x,
end

lemma blahblah
{a b c d : ℝ}
{f : ℝ → ℝ}
(hf : interval_integrable f real.measure_space.volume a b)
(hac : a ≤ c)
(hcd : c ≤ d)
(hdb : d ≤ b)
:
interval_integrable f real.measure_space.volume c d
:=
begin
  have hab : a ≤ b, calc a ≤ c : hac ... ≤ d : hcd ... ≤ b : hdb,
  unfold interval_integrable,
  unfold interval_integrable at hf,
  simp [hcd],
  have : set.Ioc c d ⊆ set.Ioc a b, {
    unfold has_subset.subset,
    unfold set.subset,
    intros x hx,
    simp at hx,
    simp,
    split,
    calc a ≤ c : hac ... < x : hx.left,
    calc x ≤ d : hx.right ... ≤ b : hdb,
  },
  exact integrable_on.mono_set hf.left this,
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

lemma goal (a r : ℝ) (ha : 0 < a) (hr : r < -1):
tendsto
(λ (y : ℝ), ∫ (x : ℝ) in a..y, x ^ r)
at_top
(𝓝 (-a ^ (r + 1) / (r + 1)))
:=
begin
  have : tendsto (λ (y : ℝ), (y ^ (r + 1))) at_top (𝓝 0),
  have : (r + 1) = - - (r + 1), simp,
  rw this,
  apply tendsto_rpow_neg_at_top,
  linarith,
  have : tendsto (λ (y : ℝ), (y ^ (r + 1) / (r + 1))) at_top (𝓝 0),
  conv {
    congr,
    skip, skip, congr,
    rw ← zero_div (r + 1),
  },
  apply tendsto.div_const,
  exact this,
  have fooooo : (λ (y : ℝ), ((y ^ (r + 1) - a ^ (r + 1)) / (r + 1))) = (λ (y : ℝ), y ^ (r + 1) / (r + 1)) + (λ (y : ℝ), -a ^ (r + 1) / (r + 1)), {
    funext,
    simp,
    ring,
  },
  have : tendsto (λ (y : ℝ), ((y ^ (r + 1) - a ^ (r + 1)) / (r + 1))) at_top (𝓝 (-a ^ (r + 1) / (r + 1))),
  {
    rw fooooo,
    conv {
      congr,
      skip,
      skip,
      congr,
      rw ← zero_add (-a ^ (r + 1) / (r + 1)),
    },
    apply tendsto.add,
    simp,
    exact this,
    exact tendsto_const_nhds,
  },
  refine tendsto.congr' _ this,
  rw eventually_eq_iff_exists_mem,
  use { y : ℝ | a < y },
  split,
  simp,
  use a + 1,
  intros b hb,
  linarith,
  unfold set.eq_on,
  intros x hx,
  simp at hx,
  rw integral_rpow,
  right,
  split,
  linarith,
  apply not_mem_interval_of_lt,
  exact ha,
  calc 0 < a : ha ... < x : hx,
end

end squarefree_sums
