import analysis.p_series
import number_theory.arithmetic_function
import algebra.squarefree
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral
import analysis.special_functions.integrals
import defs
import summability
import lemmas_on_tendsto
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

def coi (f : ℕ → ℝ) := (λ (x : ℝ), f (⌊x⌋₊))

def coi' (f : ℝ → ℝ) := (λ (x : ℝ), f (⌊x⌋₊))

instance : floor_semiring ℝ :=
{ floor := λ a, ⌊a⌋.to_nat,
  ceil := λ a, ⌈a⌉.to_nat,
  floor_of_neg := λ a ha, int.to_nat_of_nonpos (int.floor_nonpos ha.le),
  gc_floor := λ a n ha, by { rw [int.le_to_nat_iff (int.floor_nonneg.2 ha), int.le_floor], refl },
  gc_ceil := λ a n, by { rw [int.to_nat_le, int.ceil_le], refl } }


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

lemma doodoo (k : ℕ) : ∀ (x : ℝ), x ∈ set.Ioo (k : ℝ) (↑k + 1) → ⌊x⌋₊ = k :=
begin
  intros x hx,
  simp at hx,
  have zero_le_x : 0 ≤ x, {
    have : 0 ≤ k, linarith,
    calc (0 : ℝ) ≤ ↑k : by simp ... ≤ x : by simp [hx.left, le_of_lt],
  },
  have is_le : ⌊x⌋₊ ≤ k, {
    rw ← lt_succ_iff,
    have : (⌊x⌋₊ : ℝ) < k.succ, calc ↑⌊x⌋₊ ≤ x : nat.floor_le zero_le_x ... < k.succ : by simp [hx.right],
    rw cast_lt at this,
    exact this,
  },
  have : ↑k ≤ x, exact le_of_lt hx.left,
  have is_ge : k ≤ ⌊x⌋₊, exact nat.le_floor this,
  linarith [is_le, is_ge],
end

lemma fafa (n : ℕ) (f : ℕ → ℝ) :
∫ (x : ℝ) in ↑n..↑n + 1, f n
=
∫ (x : ℝ) in ↑n..↑n + 1, (coi f) x
:=
begin
  apply interval_integral.integral_congr_ae',
  rw filter.eventually_iff,
  rw measure_theory.mem_ae_iff,
  have : {x : ℝ | x ∈ set.Ioc (n : ℝ) (↑n + 1) → f n = coi f x}ᶜ ⊆ {↑n + 1},
  {
    rw compl_subset_iff_union,
    ext,
    simp,
    by_cases x = n + 1,
    simp [h],
    simp [h],
    intros ha hb,
    let foooo := lt_or_eq_of_le hb,
    simp [h] at foooo,
    rw ← nat.cast_one at foooo,
    rw ← nat.cast_add at foooo,
    unfold coi,
    have fdfdfdfd : 0 ≤ x, exact le_of_lt (calc (0 : ℝ) ≤ n : by simp ... < x : ha),
    have : n ≤ ⌊x⌋₊, exact nat.le_floor (le_of_lt ha),
    have : ⌊x⌋₊ < ↑n + 1, simp [(nat.floor_lt fdfdfdfd).mpr foooo],
    have : ⌊x⌋₊ = n, linarith,
    rw this,
  },
  exact measure_subset_null _ {↑n + 1} this real.volume_singleton,
  simp,
end

lemma real_constant_on_interval_integrable
(a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : ∃c, ∀ (x : ℝ), x ∈ set.Ioo a b → f x = c) :
interval_integrable f real.measure_space.volume a b :=
begin
  rw interval_integrable_iff,
  rcases hf with ⟨c, hc⟩,
  have : measure_theory.integrable_on (λ x, c) (set.interval_oc a b) real.measure_space.volume,
  {
    unfold measure_theory.integrable_on,
    apply continuous.integrable_on_interval_oc,
    exact continuous_const,
  },
  apply measure_theory.integrable_on.congr_fun' this,
  rw eventually_eq_iff_exists_mem,
  use set.Ioo a b,
  split,
  rw measure_theory.mem_ae_iff,
  conv {
    congr,
    simp,
  },
  have : (set.Ioo a b)ᶜ ∩ (set.interval_oc a b) = {b},
  {
    ext,
    simp,
    split,
    rintros ⟨ha, hb⟩,
    unfold set.interval_oc at hb,
    simp [hab] at hb,
    rcases hb with ⟨hba, hbb⟩,
    cases hba,
    specialize ha hba,
    cases hbb,
    linarith,
    linarith,
    cases hbb,
    linarith,
    linarith,
    intros hx,
    simp [hx],
    unfold set.interval_oc,
    simp [hab],
  },
  rw this,
  exact real.volume_singleton,
  unfold set.eq_on,
  intros x hx,
  exact (hc x hx).symm,
end

lemma convert_finite_sum_to_interval_integral (n : ℕ) (f : ℕ → ℝ) :
∑ (i : ℕ) in finset.range n,
∫ (x : ℝ) in ↑i..↑i + 1,
f i
=
∫ (x : ℝ) in 0..n, (coi f) x
:=
begin
  conv {
    to_lhs,
    congr,
    skip,
    funext,
    rw fafa i f,
  },
  -- Problem: There are a lot of lemmas that show that if a function is constant
  -- on all of ℝ then the function is integrable, but this function is constant _only_
  -- on the interval of integration. This is messing up the parser.
  have hint : ∀ (k : ℕ), k < n → interval_integrable (coi f) measure_theory.measure_space.volume (k : ℝ) ((k : ℝ) + 1),
  {
    intros k hk,
    have : ∃c, ∀ (x : ℝ), x ∈ set.Ioo (k : ℝ) (↑k + 1) → (coi f) x = c, {
      use f k,
      intros x hx,
      unfold coi,
      rw doodoo k x hx,
    },
    exact real_constant_on_interval_integrable k (k + 1) (by linarith) (coi f) this,
  },
  exact interval_integral.sum_integral_adjacent_intervals hint,
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
      rw doodoo k x hx,
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
    rw doodoo i x hx,
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

lemma doodoo'
{a b : ℕ}
{x : ℝ}
(hx : x ∈ set.Icc (a : ℝ) ↑b)
:
↑⌊x⌋₊ ∈ set.Icc (a : ℝ) ↑b
:=
begin
  simp at hx,
  have : 0 ≤ x, calc (0 : ℝ) ≤ ↑a : by simp ... ≤ x : hx.left,
  simp,
  split,
  exact le_floor hx.left,
  have : (⌊x⌋₊ : ℝ) ≤ ↑b, calc ↑⌊x⌋₊ ≤ x : floor_le this ... ≤ ↑b : hx.right,
  exact cast_le.mp this,
end

lemma doodoo_ceil'
{a b : ℕ}
{x : ℝ}
(hx : x ∈ set.Icc (a : ℝ) ↑b)
:
↑⌈x⌉₊ ∈ set.Icc (a : ℝ) ↑b
:=
begin
  simp at hx,
  simp,
  split,
  have : ↑a ≤ (⌈x⌉₊ : ℝ), calc ↑a ≤ x : hx.left ... ≤ ↑⌈x⌉₊ : le_ceil x,
  exact cast_le.mp this,
  exact hx.right,
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
    exact doodoo' hx,
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
  have u2 : ↑⌊c⌋₊ ∈ set.Icc (a : ℝ) ↑b, exact doodoo' hc,
  have u3 : ↑⌊d⌋₊ ∈ set.Icc (a : ℝ) ↑b, exact doodoo' hd,
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

lemma mem_Ioo_mem_Icc
{a b x : ℝ}
:
x ∈ Ioo a b → x ∈ Icc a b :=
begin
  simp,
  intros is_gt is_lt,
  split,
  exact le_of_lt is_gt,
  exact le_of_lt is_lt,
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
      sorry,
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
    exact doodoo_ceil' hx,
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


-- lemma bdd_step_above
-- {a : ℝ}
-- {n : ℕ}
-- {f : ℝ → ℝ}
-- (ha : 0 ≤ a)
-- (hf_mono_ev : ∀ (b b' : ℝ), a ≤ b → b ≤ b' → f b' ≤ f b)
-- (hf_nonneg : ∀ (b : ℝ), 0 ≤ f b)
-- :
-- ∀ (x : ℝ), a ≤ ⌊x⌋₊ → f x ≤ f ↑⌊x⌋₊
-- :=
-- begin
--   intros x hx,
--   sorry,
-- end



-- lemma coi_antitone_integrable
-- {a b : ℝ}
-- {f : ℝ → ℝ}
-- (hf : antitone_on f [a, b])
-- :
-- interval_integrable (coi f) real.measure_space.volume a b

lemma mem_Icc_mem_Ici
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Icc (a : ℝ) ↑b → x ∈ set.Ici (a : ℝ) :=
begin
  simp,
  intros h _,
  exact h,
end

lemma tail_sum_to_tail_integral
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
  refine tendsto_le' _ hc hf,
  use max 100 a,
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
  obtain ⟨m, hm⟩ : ∃m, n = m + 1, sorry,
  have : a ≤ m, sorry,
  rw hm,
  transitivity,
  refine antitone_sum_le_integral this _,
  intros x hx y hy hxy,
  exact hf_mono (mem_Icc_mem_Ici hx) (mem_Icc_mem_Ici hy) hxy,
  sorry,
  intros i,
  by_cases hi : a + 1 ≤ i,
  simp [hi],
  refine hf_nonneg i _,
  simp,
  calc a ≤ a + 1 : le_succ a ... ≤ i : hi,
  simp [hi],
  rw not_summable_eq_zero h,
  sorry,
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


lemma tsum_sub_head_eq_tail'
{b : ℝ}
{f : ℝ → ℝ}
:
summable (λ (i : ℕ), f ↑i) → ∑' (i : ℕ), f ↑i - ∑' (i : ℕ), ite (↑i ≤ b) (f i) 0 = ∑' (i : ℕ), ite (b < ↑i) (f ↑i) 0
:=
begin
  sorry,
end

lemma goal2
{r : ℝ}
{f : ℝ → ℝ}
-- If f is not summable, then the RHS of O is all 0 which doesn't work
(hf : summable (λ (i : ℕ), f ↑i))
:
is_Ot
(λ (x : ℝ), x ^ r * ∑' (i : ℕ), ite (↑i ≤ x) (f ↑i) 0)
(λ (x : ℝ), x ^ r * ∑' (i : ℕ), f ↑i)
(λ (x : ℝ), x ^ r * ∑' (i : ℕ), ite (x < ↑i) (|f ↑i|) 0)
at_top
:=
begin
  unfold is_Ot,
  use 1,
  unfold asymptotics.is_O_with,
  simp,
  use 200,
  intros b hb,
  rw real.norm_eq_abs,
  rw real.norm_eq_abs,
  rw real.norm_eq_abs,
  rw ← mul_sub (b ^ r),
  rw abs_mul (b ^ r),
  apply mul_le_mul_of_nonneg_left,
  rw abs_sub_comm,
  simp [hf],
  rw tsum_sub_head_eq_tail',
  transitivity,
  exact abs_tsum_le_tsum_abs,
  rw abs_tsum_nonneg_eq_tsum,
  have : ∀ (i : ℕ), |ite (b < ↑i) (f ↑i) 0| = ite (b < ↑i) (|f ↑i|) 0,
  -- Not sure why abs_of_ite isn't working here....
  intros i,
  by_cases h : b < ↑i,
  simp [h],
  simp [h],

  conv {
    to_lhs,
    congr,
    funext,
    rw this i,
  },
  intros n,
  by_cases b < ↑n,
  simp [h, abs_nonneg],
  simp [h],
  exact hf,
  exact abs_nonneg _,
end

end squarefree_sums
