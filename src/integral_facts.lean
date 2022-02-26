import analysis.p_series
import number_theory.arithmetic_function
import algebra.squarefree
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral
import analysis.special_functions.integrals

noncomputable theory
-- open_locale classical
open nat finset list finsupp set function filter measure_theory
open_locale classical topological_space interval big_operators filter ennreal asymptotics

def is_Ot {α : Type*} (f : α → ℝ) (g : α → ℝ) (h : α → ℝ) (l : filter α) : Prop :=
∃ c : ℝ, asymptotics.is_O_with c (f - g) h l

lemma tendsto_abs {f : finset ℕ → ℝ} {a : ℝ} (h : filter.tendsto f at_top (nhds a)) : filter.tendsto (λ n, |f n|) at_top (nhds (|a|)) :=
begin
  rw ← real.norm_eq_abs,
  conv {
    congr,
    funext,
    rw ← real.norm_eq_abs,
  },
  apply filter.tendsto.norm,
  simp [h],
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

-- {n : ℕ} {x : ℝ} (hx : 1 ≤ x): |↑(heaviside n ⌊x⌋₊) * (x ^ 2)⁻¹| ≤ |↑(heaviside n ⌊x⌋₊) * ((⌊x⌋₊ : ℝ) ^ 2)⁻¹| :=
-- begin
--   unfold heaviside,
--   have zero_lt_x : 0 < x, calc 0 < 1 : by linarith ... ≤ x : hx,
--   have one_le_floor_x : 1 ≤ ⌊x⌋₊, {
--     let foo := floor_mono,
--     unfold monotone at foo,
--     specialize foo hx,
--     rw floor_one at foo,
--     exact foo,
--   },

--   by_cases ⌊x⌋₊ < n,
--   simp [h],
--   simp [h],
--   rw abs_of_nonneg,
--   rw abs_of_nonneg,
--   rw inv_le,
--   simp,
--   apply pow_le_pow_of_le_left,
--   simp,
--   exact floor_le (le_of_lt zero_lt_x),
--   calc 0 < x : zero_lt_x ... = x ^ 1 : by simp ... ≤ x ^ 2 : pow_le_pow hx (by linarith),
--   rw inv_pos,
--   -- So much casting why?
--   calc (0 : ℝ) < (1 : ℝ) : by linarith ... ≤ ↑⌊x⌋₊ : by simp [one_le_floor_x] ... = ↑⌊x⌋₊ ^ 1 : by simp ... ≤ ↑⌊x⌋₊ ^ 2 : pow_le_pow (by simp [one_le_floor_x]) (by linarith),
--   rw inv_nonneg,
--   calc (0 : ℝ) ≤ (1 : ℝ) : by linarith ... ≤ ↑⌊x⌋₊ : by simp [one_le_floor_x] ... = ↑⌊x⌋₊ ^ 1 : by simp ... ≤ ↑⌊x⌋₊ ^ 2 : pow_le_pow (by simp [one_le_floor_x]) (by linarith),
--   rw inv_nonneg,
--   calc 0 ≤ 1 : by linarith ... ≤ x : hx ... = x ^ 1 : by simp ... ≤ x ^ 2 : pow_le_pow hx (by linarith),
-- end

lemma finset.subset_finset_min_max {s : finset ℕ} (hs : s.nonempty) : s ⊆ finset.Icc (s.min' hs) (s.max' hs) :=
begin
  rw subset_iff,
  intros x hx,
  simp,
  by_contradiction H,
  push_neg at H,
  by_cases h : s.min' hs ≤ x,
  specialize H h,
  rw finset.max'_lt_iff at H,
  specialize H x hx,
  linarith,
  push_neg at h,
  rw finset.lt_min'_iff at h,
  specialize h x hx,
  linarith,
end

lemma finset.Icc_subset_range {a b : ℕ} : finset.Icc a b ⊆ finset.range (b + 1) :=
begin
  rw subset_iff,
  intros x hx,
  rw finset.mem_range,
  simp at hx,
  simp [lt_succ_of_le hx.right],
end


lemma asdf (x : ℕ) (hx : 0 < x) :
(∑' i, |↑(heaviside (sqrt x) i) * ((i : ℝ) ^ 2)⁻¹|) ≤
sqrt x
:=
begin
  have one_le_x : 1 ≤ x, linarith,
  apply tsum_le_of_sum_le',
  norm_cast, simp,
  intros s,
  by_cases s = ∅,
  simp [h],
  have : s.nonempty, exact nonempty_of_ne_empty h,
  let l := s.min' this,
  let u := s.max' this,
  have : s ⊆ finset.Icc l u, exact finset.subset_finset_min_max this,
  have : s ⊆ finset.range (u + 1),
  {
    -- Weird cast issues mean I can't just use the above lemma with calc?
    rw subset_iff,
    intros x hx,
    rw finset.mem_range,
    have : x ∈ finset.Icc l u, calc x ∈ s : hx ... ⊆ finset.Icc l u : this,
    simp at this,
    simp [lt_succ_of_le this.right],
  },
  have fooo : (∑ (i : ℕ) in s, |↑(heaviside (sqrt x) i) * ((i : ℝ) ^ 2)⁻¹|) ≤ (∑ (i : ℕ) in finset.range (u + 1), |↑(heaviside (sqrt x) i) * ((i : ℝ) ^ 2)⁻¹|),
  apply finset.sum_le_sum_of_subset_of_nonneg,
  exact this,
  intros x hx hx',
  simp [abs_nonneg],
  transitivity,
  exact fooo,
  conv {
    to_lhs,
    congr,
    skip,
    funext,
    rw ← fdsa i (|((heaviside (sqrt x) i) : ℝ) * (↑i ^ 2)⁻¹|),
  },

  rw convert_finite_sum_to_interval_integral,
  -- Now we have an integral of a step function
  -- Next: convert to integral of rpow for sufficiently large x
  -- measure_theory.integral_mono
  unfold coi,
  -- transitivity,
  -- apply measure_theory.integral_mono,
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

lemma helper
{b : ℝ}
{f : ℝ → ℝ}
:
∀ (i : ℕ), |f ↑i - ite (b < ↑i) (f ↑i) 0| ≤ |f ↑i|
:=
begin
  intros i,
  by_cases b < ↑i,
  simp [h, abs_nonneg],
  simp [h],
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

lemma abs_of_ite
{p : Prop}
{a b : ℝ}
:
|ite p a b| = ite p (|a|) (|b|)
:=
begin
  sorry,
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

lemma ite_const_rw
{n : ℕ}
{f : ℕ → ℝ}
:
∀ (i : ℕ), ite (i = n) (f i) 0 = ite (i = n) (f n) 0
:=
begin
  intros i,
  by_cases i = n,
  simp [h],
  simp [h],
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

lemma not_mem_if_gt_max'
{s : finset ℕ}
{hs : s.nonempty}
{n : ℕ}
(hn : max' s hs < n)
:
n ∉ s
:=
begin
  by_contradiction H,
  linarith [calc n ≤ max' s hs : le_max' s n H ... < n : hn],
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
