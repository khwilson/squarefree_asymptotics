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

lemma doodoo (k : ℕ) : ∀ (x : ℝ), x ∈ set.Ioo (k : ℝ) (↑k + 1) → ⌊x⌋₊ = k := sorry

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
    let tail := hint (m + n) (by sorry),
    have :  ∀ (k : ℕ), k < m + n → interval_integrable f ν (a k) (a (k + 1)),
    intros k hk,
    have : k < m + n.succ, sorry,
    exact hint k this,
    specialize hn this,
    exact interval_integrable.trans hn tail,
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
    have : k < m + n.succ, calc k < m + n : hk ... < m + n.succ : by sorry,
    exact hint k this, },
  apply interval_integrable.trans_iterate',
  intros k hk, exact this k hk,
  exact hint (m + n) (by sorry),
  intros k hk, exact hint k (by sorry),
  simp,
end

lemma sum_le_antitone_integral {a b : ℕ} {f : ℝ → ℝ} (hab : a ≤ b) (hf : antitone_on f (set.Icc a b)) :
∑ x in finset.Ico a b, f x ≤ ∫ x in a..b, f x :=
begin

  conv {
    to_lhs,
    congr,
    skip,
    funext,
    rw ← fdsa x (f ↑x),
  },
  unfold antitone_on at hf,
  have : ∀ (x : ℕ), x ∈ finset.Ico a b → ∫ (y : ℝ) in ↑x..↑x + 1, f ↑x ≤ ∫ (y : ℝ) in ↑x..↑x + 1, f y,
  {
    intros x hx,
    have hhf : interval_integrable (λ y, f ↑x) real.measure_space.volume a b, sorry,
    have hhg : interval_integrable f real.measure_space.volume a b, sorry,
    have hh : ∀ (y : ℝ), y ∈ set.Icc (x : ℝ) (↑x + 1) → ((λ y, f ↑x) y) ≤ f y, sorry,
    have hxx : (x : ℝ) ≤ ↑x + 1, sorry,
    exact interval_integral.integral_mono_on hxx hhf hhg hh,
  },
  obtain ⟨k', hk'⟩ := le_iff_exists_add.mp hab,
  rw hk',
  have hint : ∀ (i : ℕ), (i < a + k') → interval_integrable f real.measure_space.volume i (i+1),
  {
    sorry,
  },

  rw [sum_integral_adjacent_intervals' hint],
end

lemma bdd_step_above
{a : ℝ}
{n : ℕ}
{f : ℝ → ℝ}
(ha : 0 ≤ a)
(hf_mono_ev : ∀ (b b' : ℝ), a ≤ b → b ≤ b' → f b' ≤ f b)
(hf_nonneg : ∀ (b : ℝ), 0 ≤ f b)
:
∀ (x : ℝ), a ≤ ⌊x⌋₊ → f x ≤ f ↑⌊x⌋₊
:=
begin
  intros x hx,
  sorry,
end

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

lemma coi_antitone_integrable
{a b : ℝ}
{f : ℝ → ℝ}
(hf : antitone_on f [a, b])
:
interval_integrable (coi f) real.measure_space.volume a b

lemma tail_sum_to_tail_integral
{a l : ℝ}
{f : ℝ → ℝ}
(hf : tendsto (λ (b : ℝ), ∫ (x : ℝ) in a..b, f x) at_top (𝓝 l))
(hf_mono : ∀ (b b' : ℝ), a ≤ b → b ≤ b' → f b' ≤ f b)
(hf_nonneg : ∀ (b : ℝ), 0 ≤ f b)
:
(∑' (i : ℕ), (λ (j : ℕ), ite (a < j) (f ↑j) 0) i) ≤ l :=
begin
  by_cases summable (λ (j : ℕ), ite (a < j) (f ↑j) 0),
  obtain ⟨c, hc⟩ := h,
  rw has_sum.tsum_eq hc,
  rw has_sum_iff_tendsto_nat_of_nonneg at hc,
  let hf' := real_tendsto_implies_nat_tendsto hf,
  simp at hf',
  refine tendsto_le' _ hc hf',
  use max 100 ⌈a⌉₊,
  intros n hn,
  conv {
    to_lhs, congr, skip, funext,
    rw ← const_eq_integral_const_on_unit_interval i (ite (a < ↑i) (f ↑i) 0),
  },
  rw convert_finite_sum_to_interval_integral,
  simp,
  have ff : interval_integrable (coi (λ (i : ℕ), ite (a < ↑i) (f ↑i) 0)) real.measure_space.volume 0 a, sorry,
  have gg : interval_integrable (coi (λ (i : ℕ), ite (a < ↑i) (f ↑i) 0)) real.measure_space.volume a ↑n, sorry,
  conv {
    to_lhs,
    rw ← interval_integral.integral_add_adjacent_intervals ff gg,
  },
  by_cases ha : a < 0, {
    sorry,
  },

  push_neg at ha,
  have : (∫ (x : ℝ) in 0..a, coi (λ (i : ℕ), ite (a < ↑i) (f ↑i) 0) x) = (∫ (x : ℝ) in 0..a, 0), {
    apply interval_integral.integral_congr,
    unfold eq_on,
    intros x hx,
    unfold interval at hx,
    simp [ha] at hx,
    unfold coi,
    have : ↑⌊x⌋₊ ≤ a,
      calc (⌊x⌋₊ : ℝ) ≤ x : floor_le hx.left
        ... ≤ a : hx.right,
    simp [this],
    intros boo,
    exfalso,
    linarith,
  },
  rw this,
  simp,
  apply interval_integral.integral_mono,
  calc
    a ≤ ↑⌈a⌉₊ : le_ceil a
      ... ≤ max 100 ↑⌈a⌉₊ : le_max_right 100 ↑⌈a⌉₊
      ... = ↑(max 100 ⌈a⌉₊) : by simp [cast_max.symm]
      ... ≤ ↑n : cast_le.mpr hn,
  -- have gg : interval_integrable f real.measure_space.volume a ↑n, sorry,
  -- refine interval_integral.integral_mono _ ff gg _,
  sorry,
  sorry,
  unfold has_le.le,
  intros x,
  simp,
  funext,
  funext,

  intros x,
  by_cases a < ↑x,
  simp [h, hf_nonneg],
  simp [h],
  unfold tsum,
  simp [h],
  have : ∀ (b : ℝ), a ≤ b → 0 ≤ ∫ (x : ℝ) in a..b, f x, {
    intros b hab,
    apply interval_integral.integral_nonneg,
    exact hab,
    intros u hu,
    exact hf_nonneg u,
  },
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

lemma abs_tsum_nonneg_eq_tsum
{f : ℕ → ℝ}
(hf : ∀ (n : ℕ), 0 ≤ f n)
:
|∑' (i : ℕ), f i| = ∑' (i : ℕ), f i
:=
begin
  by_cases h : summable f,
  obtain ⟨c, hc⟩ := h,
  rw has_sum.tsum_eq hc,
  apply abs_of_nonneg,
  exact has_sum_mono has_sum_zero hc hf,
  unfold tsum,
  simp [h],
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
