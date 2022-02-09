import analysis.p_series
import number_theory.arithmetic_function
import algebra.squarefree
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral

noncomputable theory
-- open_locale classical
open nat finset list finsupp set function filter
open_locale classical topological_space interval big_operators filter ennreal asymptotics

def squarefree_nat (n : ℕ) := if squarefree n then (1 : ℤ) else (0 : ℤ)

def Q (n : ℕ) := ∑ (i : ℕ) in finset.range (n + 1), squarefree_nat i

def Q' (n : ℕ) := (6 * (n : ℝ) / real.pi^2)

def zeta2 (n : ℕ) := ∑ (i : ℕ) in finset.range (n + 1), 1 / (i : ℝ) ^ 2

theorem zeta_2_eq_pi2_div_6 : tendsto zeta2 at_top (𝓝 (real.pi ^ 2 / 6)) :=
begin
  sorry,
end

lemma nat_ne_zero_ne_one_ge_two {n : ℕ} : n ≠ 0 ∧ n ≠ 1 ↔ n ≥ 2 :=
begin
  induction n,
  simp,
  have n_n_ge_one : n_n.succ ≥ 1, {
    calc n_n.succ = n_n + 1 : by exact rfl
      ... ≥ 0 + 1 : le_add_self
      ... ≥ 1 : rfl.ge,
  },
  induction n_n,
  simp,
  have n_n_n_ge_two : n_n_n.succ.succ ≥ 2, {
    calc n_n_n.succ.succ = n_n_n.succ + 1 : rfl
      ... ≥ n_n_n + 1 + 1 : rfl.ge
      ... ≥ n_n_n + 2 : rfl.ge
      ... ≥ 0 + 2 : le_add_self
      ... ≥ 2 : rfl.ge,
  },
  simp,
  linarith,
end

lemma nat_ne_zero_ne_one_two_le {n : ℕ} : n ≠ 0 ∧ n ≠ 1 ↔ 2 ≤ n :=
begin
  rw ← ge_iff_le,
  exact nat_ne_zero_ne_one_ge_two,
end

lemma pow_le_abs_pow {a : ℝ} {b : ℕ} : a^b ≤ |a| ^ b := begin
  by_cases 0 ≤ a,
  rwa abs_of_nonneg,
  have : a < 0, linarith,
  by_cases even b,
  cases h with k hk,
  rw [hk, pow_mul, pow_mul, ← abs_of_nonneg (pow_two_nonneg a), (pow_abs a)],
  have : odd b, simp [h],
  cases this with k hk,
  have : a ^ b ≤ 0, {
    rw hk,
    rw pow_add,
    rw mul_nonpos_iff,
    left,
    split,
    rw pow_mul,
    simp [pow_two_nonneg a, pow_nonneg],
    linarith,
  },
  transitivity,
  exact this,
  simp [abs_nonneg, pow_nonneg],
end

lemma minus_one_pow_odd_eq_minus_one : ∀ (a : ℕ), odd a → (-1 : ℤ) ^ a = -1 :=
begin
  intros a ha,
  cases ha with k hk,
  rw [hk, pow_add, pow_mul],
  simp,
end

lemma minus_one_pow_even_eq_one : ∀ (a : ℕ), even a → (-1 : ℤ) ^ a = 1 :=
begin
  intros a ha,
  cases ha with k hk,
  rw [hk, pow_mul],
  simp,
end

lemma minus_one_pow_eq_pm_one {a : ℕ} : (-1 : ℤ) ^ a = 1 ∨ (-1 : ℤ) ^ a = -1 :=
begin
  have : odd a ∨ even a, simp [odd_iff_not_even, or.symm, or_not],
  cases this,
  simp [minus_one_pow_odd_eq_minus_one a this],
  simp [minus_one_pow_even_eq_one a this],
end

lemma abs_mu_le_one {a : ℕ} : |arithmetic_function.moebius a| ≤ 1 :=
begin
  unfold arithmetic_function.moebius,
  simp,
  by_cases h : squarefree a,
  simp [h],
  simp [h],
end

lemma break_up_sum_sets : ∀ (x X : ℕ), disjoint {d | d < x} {d | x ≤ d ∧ d ≤ X} :=
begin
  intros x X,
  rw disjoint_iff_forall_ne,
  intros y hy z hz,
  by_contradiction H,
  have : y < y,
    calc y < x : hy
      ... ≤ z : hz.left
      ... = y : H.symm,
  linarith,
end

lemma extend_sum_le (a x X : ℕ) (hax : a ≤ x) (hxX : x ≤ X) (f : ℕ → ℝ) (hf : ∀ (y : ℕ), 0 ≤ f y) : (∑ y in Ico a x, f y) ≤ (∑ y in Ico a X, f y) :=
begin
  have : finset.Ico a X = finset.Ico a x ∪ finset.Ico x X, {
    rw finset.Ico_union_Ico_eq_Ico hax hxX,
  },
  have : (∑ y in Ico a X, f y) = (∑ y in Ico a x, f y) + (∑ y in Ico x X, f y),
  {
    rw this,
    apply finset.sum_union,
    exact Ico_disjoint_Ico_consecutive a x X,
  },
  rw this,
  simp,
  have : ∀ (i : ℕ), i ∈ finset.Ico x X → 0 ≤ f i, {
    intros i hi,
    exact hf i,
  },
  apply finset.sum_nonneg,
  intros i hi,
  exact this i hi,
end

lemma one_dirichlet_summable : ∀ (d : ℕ), 2 ≤ d → summable (λ (n : ℕ), ((n : ℝ) ^ d)⁻¹) :=
begin
  intros d hd,
  apply real.summable_nat_pow_inv.mpr,
  linarith,
end

lemma bounded_dirichlet_summable
(f : ℕ → ℝ)
(hC : ∃ C, ∀ (n : ℕ), |f n| ≤ C) :
 ∀ (d : ℕ), 2 ≤ d
 → summable (λ (n : ℕ), (f n) * ((n : ℝ) ^ d)⁻¹):=
begin
  intros d hd,
  rw ← summable_abs_iff,
  have : (λ (x : ℕ), | f x * (↑x ^ d)⁻¹ |) = (λ (x : ℕ), |f x | * |(↑x ^ d)⁻¹|), {
    ext,
    rw abs_mul,
  },
  rw this,
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
  have ffff : (λ (n : ℕ), ((n : ℝ) ^ d)⁻¹) = (λ (n : ℕ), |((n : ℝ) ^ d)⁻¹|), {
    ext,
    rw abs_of_nonneg,
    exact this x,
  },
  rw ← ffff,
  exact one_dirichlet_summable d hd,
end

def μ := arithmetic_function.moebius

def μ_over_d2 (d : ℕ) := ↑(μ d) * ((d : ℝ) ^ 2)⁻¹

def heaviside (d e : ℕ) := ite (e < d) 0 1

def anti_heaviside (d e : ℕ) := ite (e < d) 1 0

def μ_over_d2_upto (d : ℕ) := (∑ i in finset.Ico 1 d, μ_over_d2 i)

def μ_over_d2_heaviside (d i : ℕ) := ↑(heaviside d i) * (μ_over_d2 i)

def μ_over_d2_anti_heaviside (d i : ℕ) := ↑(anti_heaviside d i) * (μ_over_d2 i)

def μ_over_d2_from (d : ℕ) := (∑' i, μ_over_d2_heaviside d i)

def one_over_d2_from (d : ℕ) := (∑' i, ↑(heaviside d i) * ((i : ℝ) ^ 2)⁻¹)

lemma compl_heaviside (d : ℕ) (f : ℕ → ℝ) : (λ n, ↑(heaviside d n) * (f n)) + (λ n, ↑(anti_heaviside d n) * (f n)) = f :=
begin
  ext,
  unfold heaviside,
  unfold anti_heaviside,
  by_cases x < d,
  simp [h], simp [h],
end

lemma summable_μ_over_d2 : summable μ_over_d2 :=
begin
  apply bounded_dirichlet_summable,
  use 1, intros n,
  unfold μ,
  unfold arithmetic_function.moebius,
  simp,
  by_cases squarefree n,
  simp [h], simp [h],
end

lemma summable_of_mul_heaviside (d : ℕ) (f : ℕ → ℝ) : summable f → summable (λ n, ↑(heaviside d n) * (f n)) :=
begin
  intros hf,
  rw ← summable_abs_iff,
  unfold heaviside,
  have : summable (λ n, |f n|), {
    exact summable_abs_iff.mpr hf,
  },
  apply summable_of_nonneg_of_le,
  intros b, exact abs_nonneg _,
  intros b,
  have foo : |↑(ite (b < d) 0 1) * f b| ≤ |f b|, {
    by_cases b < d, simp [h, abs_nonneg], simp [h],
  },
  exact foo,
  exact this,
end

lemma summable_of_mul_anti_heaviside (d : ℕ) (f : ℕ → ℝ) : summable f → summable (λ n, ↑(anti_heaviside d n) * (f n)) :=
begin
  intros hf,
  rw ← summable_abs_iff,
  unfold anti_heaviside,
  have : summable (λ n, |f n|), {
    exact summable_abs_iff.mpr hf,
  },
  apply summable_of_nonneg_of_le,
  intros b, exact abs_nonneg _,
  intros b,
  have foo : |↑(ite (b < d) 1 0) * f b| ≤ |f b|, {
    by_cases b < d, simp [h], simp [h, abs_nonneg],
  },
  exact foo,
  exact this,
end

lemma summable_μ_over_d2_heaviside (d : ℕ) : summable (μ_over_d2_heaviside d) :=
begin
  apply summable_of_mul_heaviside,
  exact summable_μ_over_d2,
end

lemma summable_μ_over_d2_anti_heaviside (d : ℕ) : summable (μ_over_d2_anti_heaviside d) :=
begin
  apply summable_of_mul_anti_heaviside,
  exact summable_μ_over_d2,
end

def μ_sum_at_2 := ∑' i, μ_over_d2 i

def one_over_d2 (d : ℕ) := ((d : ℝ)^2)⁻¹

lemma asdf (d : ℕ) : μ_sum_at_2 - μ_over_d2_upto d = μ_over_d2_from d :=
begin
  unfold μ_sum_at_2,
  unfold μ_over_d2_upto,
  unfold μ_over_d2_from,

  have is_out_val : ∀ (b : ℕ), b ∉ finset.Ico 1 d → ↑(anti_heaviside d b) * μ_over_d2 b = 0, {
    intros b hb,
    simp at hb,
    by_cases b = 0,
    simp [h, anti_heaviside, μ_over_d2],
    have : 1 ≤ b, {
      exact one_le_iff_ne_zero.mpr h,
    },
    specialize hb this,
    simp [anti_heaviside],
    intros hhb,
    exfalso,
    linarith,
  },

  have is_in_val : ∀ (b : ℕ), b ∈ finset.Ico 1 d → ↑(anti_heaviside d b) * μ_over_d2 b = μ_over_d2 b, {
    intros b hb,
    simp at hb,
    simp [hb.right, anti_heaviside],
  },


  have : ∑' i, ↑(anti_heaviside d i) * μ_over_d2 i = ∑ (i : ℕ) in Ico 1 d, ↑(anti_heaviside d i) * μ_over_d2 i,
  {
    exact tsum_eq_sum is_out_val,
  },
  have fdfdfd : ∑ (i : ℕ) in Ico 1 d, ↑(anti_heaviside d i) * μ_over_d2 i = ∑ (i : ℕ) in Ico 1 d, μ_over_d2 i,
  {
    apply finset.sum_congr,
    exact rfl,
    intros x hx,
    exact is_in_val x hx,
  },
  rw ← fdfdfd,
  rw ← tsum_eq_sum,
  {
    rw ← tsum_sub,
    rw ← compl_heaviside d μ_over_d2,
    apply tsum_congr,
    intros b,
    unfold μ_over_d2_heaviside,
    simp [compl_heaviside],
    conv {
      to_lhs,
      congr,
      rw ← compl_heaviside d μ_over_d2,
      simp,
    },
    ring,
    exact summable_μ_over_d2,
    exact summable_μ_over_d2_anti_heaviside d,
  },
  intros x hx,
  exact is_out_val x hx,
end

lemma abs_tsum_le_tsum_abs (f : ℕ → ℝ) : | ∑' i, f i | ≤ (∑' i, |f i|) :=
begin
  by_cases summable f,
  have : summable (λ n, |f n|), simp [summable_abs_iff, h],
  sorry,
  have : ¬ summable (λ n, |f n|), simp [summable_abs_iff, h],
  unfold tsum,
  simp [h, this],
end

lemma abs_sum_le_sum_abs' (f : ℕ → ℝ) (s : finset ℕ): | ∑ d in s, f d | ≤ ∑ d in s, | f d | :=
begin
  apply finset.induction_on s,
  simp only [finset.sum_empty, abs_zero],
  {
    intros i s his IH,
    simp only [his, finset.sum_insert, not_false_iff],
    exact (abs_add _ _).trans (add_le_add (le_refl (|f i|)) IH),
  },
end

lemma sum_const_one (s : finset ℕ) : ∑ i in s, (1 : ℝ) = ↑s.card :=
begin
  have : s.card = s.card * 1, simp,
  rw this,
  simp,
end

def is_square (n : ℕ) : Prop := ∃ s, s * s = n

instance : decidable_pred (is_square : ℕ → Prop)
| n := decidable_of_iff' _ (nat.exists_mul_self n)

def num_square_divisors (n : ℕ) := (n.divisors.filter is_square).card

def divides (d : ℕ) (n : ℕ) : Prop := d ∣ n

def num_divides_upto (d : ℕ) (n : ℕ) := ((finset.Icc 1 n).filter (divides d)).card

lemma Icc_neighbor_disjoint {a b c : ℕ} (hab : a ≤ b) (hbc : b < c) :
  ((finset.Icc a b) ∪ (finset.Icc (b + 1) c) = finset.Icc a c) ∧
  disjoint (finset.Icc a b) (finset.Icc (b + 1) c) :=
begin
  split,
  {
    ext d,
    split,
    intros hd,
    simp at hd,
    simp,
    cases hd,
    simp [hd.left],
    transitivity,
    exact hd.right,
    exact le_of_lt hbc,
    have : b ≤ b + 1, exact le_succ b,
    split,
    transitivity,
    exact hab,
    transitivity,
    exact this,
    exact hd.left,
    exact hd.right,
    intros hd,
    simp at hd,
    simp,
    by_cases d ≤ b,
    left,
    simp [hd.left, h],
    push_neg at h,
    rw lt_iff_add_one_le at h,
    right,
    exact ⟨h, hd.right⟩,
  },
  {
    rw finset.disjoint_iff_ne,
    intros d hd e he,
    simp at hd,
    simp at he,
    have : d < e, {
      calc d ≤ b : hd.right
        ... < b + 1 : lt_succ_self b
        ... ≤ e : he.left,
    },
    linarith,
  },
end


lemma num_divides_upto_eq (d n : ℕ) : num_divides_upto d n = n.div d :=
begin
  unfold num_divides_upto,
  induction n with n hn,
  dec_trivial,
  have aaa : 1 ≤ n, sorry,
  have bbb : n ≤ n.succ, sorry,

  have is_union : (finset.Icc 1 n) ∪ (finset.Icc n.succ n.succ) = finset.Icc 1 n.succ, {
    sorry,
  },
  have is_disjoint : disjoint (finset.Icc 1 n) (finset.Icc n.succ n.succ), {
    sorry,
  },
  rw ← is_union,
  rw filter_union,
  have : disjoint (filter (divides d) (finset.Icc 1 n)) (filter (divides d) (finset.Icc n.succ n.succ)), {
    exact disjoint_filter_filter is_disjoint,
  },
  rw card_disjoint_union this,
  rw hn,
  simp,
  have dvd_case : d ∣ n.succ → (finset.filter (divides d) {n.succ}).card = 1, {
    intros hd,
    rw card_eq_one,
    use n.succ,
    rw finset.eq_singleton_iff_unique_mem,
    split,
    rw finset.mem_filter,
    unfold divides,
    simp [hd],
    intros x,
    rw finset.mem_filter,
    rintros ⟨hx, hxx⟩,
    exact finset.mem_singleton.mp hx,
  },
  have not_dvd_case : ¬ (d ∣ n.succ) → (finset.filter (divides d) {n.succ}).card = 0, {
    intros hd,
    rw card_eq_zero,
    rw finset.eq_empty_iff_forall_not_mem,
    intros x,
    rw finset.mem_filter,
    push_neg,
    intros hx,
    rw finset.mem_singleton at hx,
    rwa ← hx at hd,
  },
  by_cases d ∣ n.succ,
  {
    rw dvd_case h,
    have : n.succ.div d = (n + 1) / d, exact rfl,
    rw this,
    rw succ_div,
    have : n.div d = n / d, exact rfl,
    rw this,
    have : n.succ = n + 1, exact rfl,
    rw this at h,
    simp [h],
  },
  {
    rw not_dvd_case h,
    have : n.succ.div d = (n + 1) / d, exact rfl,
    rw this,
    rw succ_div,
    have : n.div d = n / d, exact rfl,
    rw this,
    have : n.succ = n + 1, exact rfl,
    rw this at h,
    simp [h],
  },
end



lemma step0 (n : ℕ) :
ite (squarefree n) 1 0 = ∑ d in finset.Icc 1 n, ite (d ^ 2 ∣ n) (μ d) 0 :=
begin
  by_cases squarefree n,
  {
    simp [h],
    rw sum_ite,
    simp,
    have : (finset.filter (λ (x : ℕ), x ^ 2 ∣ n) (finset.Icc 1 n)) = {1}, {
      rw finset.eq_singleton_iff_unique_mem,
      split,
      rw finset.mem_filter,
      have : n ≠ 0, {
        by_contradiction H,
        rw H at h,
        exact not_squarefree_zero h,
      },
      simp,
      sorry, -- 1 ≤ n bc n ≠ 0 ugh really should be easier
      {
        intros x hx,
        rw finset.mem_filter at hx,
        unfold squarefree at h,
        specialize h x,
        have : is_unit x, {
          rw pow_two at hx,
          exact h hx.right,
        },
        exact nat.is_unit_iff.mp this,
      },
    },
    rw this,
    rw finset.sum_singleton,
    have : μ 1 = 1, sorry,
    rw ← this,
  },
  {
    simp [h],
    sorry,
  },
end

lemma step2 :
∀ (x : ℕ),
(∑ n in finset.Icc 1 x, ∑ d in finset.Icc 1 x, ite (d ^ 2 ∣ n) (μ d) 0) =
(∑ d in finset.Icc 1 x, ((μ d) * (num_divides_upto (d^2) x)))
:=
begin
  intros x,
  unfold num_divides_upto,
  have : ∀ (y : ℕ) (s : finset ℕ), ↑(∑ a in s, 1) * (μ y) = ∑ a in s, (μ y), {
    simp,
  },
  conv {
    to_rhs,
    congr,
    skip,
    funext,
    rw card_eq_sum_ones,
    rw mul_comm,
    rw this,
  },
  rw finset.sum_comm,
  congr,
  funext,
  rw sum_ite,
  simp,
  left,
  congr,
end


lemma step3 :
∀ (x : ℕ),
(∑ d in finset.Icc 1 x, ((μ d) * (num_divides_upto (d^2) x))) =
(∑ d in finset.Icc 1 x, ((μ d) * x.div (d^2)))
:=
begin
  intros x,
  apply finset.sum_congr,
  simp,
  intros y hy,
  rw num_divides_upto_eq,
end

lemma step35 :
∀ (x : ℕ),
(∑ d in finset.Icc 1 x, ((μ d) * x.div (d^2))) =
(∑ d in finset.Icc 1 (sqrt x), ((μ d) * x.div (d^2)))
:=
begin
  intros x,
  have : finset.Icc 1 x = (finset.Icc 1 (sqrt x)) ∪ (finset.Icc ((sqrt x) + 1) x),
  {
    sorry,
  },
  rw this,
  have : disjoint (finset.Icc 1 (sqrt x)) (finset.Icc ((sqrt x) + 1) x), {
    sorry,
  },
  rw finset.sum_union this,
  simp,
  apply sum_eq_zero,
  intros y hy,
  have : x.div (y ^ 2) = x / (y ^ 2), exact rfl,
  rw this,
  simp,
  right,
  rw int.div_eq_zero_of_lt,
  linarith,
  simp at hy,
  have aaa : x < ((sqrt x) + 1) ^ 2, exact nat.lt_succ_sqrt' x,
  have bbb : ((sqrt x) + 1) ^ 2 ≤ y ^ 2, sorry,
  sorry, --- need to get from ℕ to ℤ
end

--- Here we need to lop off the endpoint of the Icc to get an Ico for the rest of our lemmas

def sum_μ_times_floor_n_over_d2 (n : ℕ) :=
((∑ d in finset.Ico 1 (sqrt n), (μ d) * n.div (d^2)) : ℝ)

def sum_μ_times_n_over_d2 (n : ℕ) :=
∑ d in finset.Ico 1 (sqrt n), ↑(μ d) * ↑n * ((d : ℝ) ^ 2)⁻¹

lemma step4 :
asymptotics.is_O
(λ (n : ℕ), sum_μ_times_floor_n_over_d2 n - sum_μ_times_n_over_d2 n)
(λ n, ((sqrt n) : ℝ))
at_top
:=
begin
  unfold asymptotics.is_O,
  use 1,
  unfold asymptotics.is_O_with,
  simp,
  use 100,
  intros b hb,
  rw real.norm_eq_abs,
  unfold sum_μ_times_floor_n_over_d2,
  unfold sum_μ_times_n_over_d2,
  rw ← finset.sum_sub_distrib,
  have : |∑ (x : ℕ) in finset.Ico 1 (sqrt b), (((μ x) * (b.div (x ^ 2)) : ℝ) - (↑(μ x) * ↑b * ((x : ℝ) ^ 2)⁻¹))| ≤ ∑ (x : ℕ) in finset.Ico 1 (sqrt b), |(↑(μ x) * (b.div (x ^ 2)) - ↑(μ x) * ↑b * (↑x ^ 2)⁻¹)|, {
    apply abs_sum_le_sum_abs',
  },
  have foo : ∀ (x : ℕ), |(((μ x) * (b.div (x ^ 2)) : ℝ) - ↑(μ x) * ↑b * (↑x ^ 2)⁻¹)| ≤ 1, {
    intros x,
    have : ((μ x) * (b.div (x ^ 2)) : ℝ) = ((μ x) : ℝ) * ((b.div (x^2)) : ℝ), simp,
    rw this,
    have : ((μ x) : ℝ) * ((b : ℝ) * ((x : ℝ) ^ 2)⁻¹) = ((μ x) : ℝ) * (b : ℝ) * ((x : ℝ) ^ 2)⁻¹, {
      ring,
    },
    rw ← this,
    have : ((μ x) : ℝ) * (((b.div (x^2)) : ℝ) - (b : ℝ) * ((x : ℝ) ^ 2)⁻¹) = (((μ x) : ℝ) * ((b.div (x^2)) : ℝ) - ((μ x) : ℝ) * ((b : ℝ) * ((x : ℝ) ^ 2)⁻¹)), {
      exact mul_sub _ _ _,
    },
    rw ← this,
    rw abs_mul,
    have : |((μ x) : ℝ)| ≤ 1, { sorry, },
    --  |↑(⇑μ x)| * |↑(b.div (x ^ 2)) - ↑b * (↑x ^ 2)⁻¹| ≤ 1
    have aaa : |((μ x) : ℝ)| * | ((b.div (x^2)) : ℝ) - (b : ℝ) * ((x : ℝ) ^ 2)⁻¹| ≤ | ((b.div (x^2)) : ℝ) - ((b : ℝ) * (x : ℝ) ^ 2)⁻¹|, {
      sorry,
      -- calc |((μ x) : ℝ)| * | ((b.div (x^2)) : ℝ) - ((b : ℝ) * (x : ℝ) ^ 2)⁻¹| ≤ 1 * | ((b.div (x^2)) : ℝ) - ((b : ℝ) * (x : ℝ) ^ 2)⁻¹| : by { sorry, }
      --    ... = | ((b.div (x^2)) : ℝ) - ((b : ℝ) * (x : ℝ) ^ 2)⁻¹| : by { sorry, },
    },
    have bbb : | ((b.div (x^2)) : ℝ) - ((b : ℝ) * (x : ℝ) ^ 2)⁻¹| ≤ 1, {
      sorry,
    },
    transitivity,
    exact aaa,
    exact bbb,
  },
  transitivity,
  exact this,
  have : ∑ (x : ℕ) in finset.Ico 1 (sqrt b), |(((μ x) : ℝ) * (b.div (x ^ 2)) - ↑(μ x) * ↑b * (↑x ^ 2)⁻¹)| ≤ ∑ (x : ℕ) in finset.Ico 1 (sqrt b), (1 : ℝ), {
    apply sum_le_sum,
    intros i hi,
    exact foo i,
  },
  transitivity,
  exact this,
  have : ∑ (x : ℕ) in finset.Ico 1 (sqrt b), (1 : ℝ) = ((sqrt b) : ℝ), {
    have : (finset.Ico 1 (sqrt b)).card = (sqrt b), sorry,
    conv {
      to_rhs,
      rw ← this,
    },
    apply sum_const_one,
  },
  simp [this],
end



lemma step5 :
asymptotics.is_O
(λ (n : ℕ), ↑n * μ_sum_at_2 - n * μ_over_d2_upto (sqrt n))
(λ (n : ℕ), ↑n * one_over_d2_from (sqrt n))
at_top
:=
begin
  unfold asymptotics.is_O,
  use 1,
  unfold asymptotics.is_O_with,
  simp,
  use 100,
  intros b hb,
  have : ↑b * μ_sum_at_2 - ↑b * μ_over_d2_upto (sqrt b) = ↑b * (μ_sum_at_2 - μ_over_d2_upto (sqrt b)), ring,
  have : ∥↑b * μ_sum_at_2 - ↑b * μ_over_d2_upto (sqrt b)∥ = ∥↑b∥ * ∥μ_sum_at_2 - μ_over_d2_upto (sqrt b)∥, {
    simp [real.norm_eq_abs, abs_mul, this],
  },
  rw this,
  rw asdf,
  rw real.norm_eq_abs,
  rw real.norm_eq_abs,
  rw real.norm_eq_abs,
  apply mul_le_mul,
  have : |(b : ℚ)| = (b : ℚ), {
    simp [abs_nonneg],
  },
  rw this,
  {
    unfold μ_over_d2_from,
    unfold one_over_d2_from,
    have : ∥∑' (i : ℕ), μ_over_d2_heaviside (sqrt b) i∥ ≤ ∑' (i : ℕ), ∥μ_over_d2_heaviside (sqrt b) i∥, {
      exact abs_tsum_le_tsum_abs (μ_over_d2_heaviside (sqrt b)),
    },
    have : ∀ (x : ℕ), (λ i, ∥μ_over_d2_heaviside (sqrt b) i∥) x ≤ (λ i, ↑(heaviside (sqrt b) i) * (↑i ^ 2)⁻¹) x, {
      intros x,
      simp,
      unfold μ_over_d2_heaviside,
      unfold heaviside,
      by_cases x < sqrt b,
      simp [h],
      simp [h],
      unfold μ_over_d2,
      simp [abs_mu_le_one],
      have : ((x : ℝ) ^ 2)⁻¹ = 1 * ((x : ℝ) ^ 2)⁻¹, simp,
      conv {
        to_rhs,
        rw this,
      },
      apply mul_le_mul,
      {
        simp [real.norm_eq_abs, abs_mu_le_one, μ],
        sorry,  -- lift to ℝ ?
      },
      exact rfl.le,
      simp [inv_nonneg, pow_nonneg],
      linarith,
    },
    -- keep going
  },
  exact abs_nonneg _,
  simp [hb],
end

/-
  Goal: set of lemmas to show that ∑_{d < √x} μ(d) / d^2 = ∑_d μ(d) / d^2 + O(∑_{d ≥ √x} 1 / x^2)
  Need:
    * |μ d| ≤ 1 - abs_mu_le_one
    * |∑| ≤ ∑||
    * {d < √x} ∪ {d ≥ √ x} = ℕ
    * sums break apart along disjoints
    * some notion of infinite sums converging
-/
theorem squarefree_asymptotics : ↑Q ~[at_top] Q' :=
begin
  rw asymptotics.is_equivalent,
end