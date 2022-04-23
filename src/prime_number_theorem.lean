import algebra.big_operators.ring
import topology.algebra.infinite_sum
import number_theory.arithmetic_function
import data.complex.basic
import analysis.special_functions.pow
import analysis.normed.group.infinite_sum
import order.filter.basic
import order.filter.at_top_bot
import analysis.calculus.fderiv
import measure_theory.integral.integrable_on
import measure_theory.integral.interval_integral
import topology.metric_space.basic

/-!
# Dirchlet Series and the Prime Number Theorem

Take `f` to have image `ℂ`. Many defined functions have image `ℕ` or `ℤ`, but they
have canonical coercions so this should be fine.
-/

open finset filter measure_theory interval_integral metric
open_locale big_operators arithmetic_function uniformity filter

-- variables {α : Type*} {β : Type*} {ι : Type*} [uniform_space β]

-- def uniform_cauchy_seq_on
--   (F : ι → α → β) (p : filter ι) (s : set α) :=
--   ∀ u : set (β × β), u ∈ 𝓤 β → (∀ᶠ (n : ι × ι) in (p ×ᶠ p), ∀ (x : α), x ∈ s → (F n.fst x, F n.snd x) ∈ u)

-- lemma uniform_cauchy_seq_on_iff [complete_space β] [nonempty β] (F : ι → α → β) (p : filter ι) (s : set α) :
--   uniform_cauchy_seq_on F p s ↔ tendsto_uniformly_on F (λ x : α, lim p (λ n : ι, F n x)) p s :=
-- begin

-- end


lemma bah
(F : ℕ → ℝ → ℝ)
(f : ℝ → ℝ)
(G : ℕ → ℝ)
(g : ℝ)
(s : set ℝ)
(hf : tendsto_uniformly_on F f at_top s)
(hg : tendsto G at_top (nhds g)) :
tendsto_uniformly_on (λ n : ℕ, λ x : ℝ, F n x + G n) (λ x : ℝ, f x + g) at_top s :=
begin
  sorry,
end

lemma mul_cancel_inv_left₀ {a b : ℝ} (ha : a ≠ 0) : a⁻¹ * (a * b) = b :=
 begin
  conv { congr, congr, skip, rw ←inv_inv a, },
  have : a⁻¹ ≠ 0, simp [ha],
  rw mul_inv_cancel_left₀ this,
end

lemma norm_add_three_le {a b c : ℝ} : ∥a + b + c∥ ≤ ∥a∥ + ∥b∥ + ∥c∥ :=
begin
  refine le_trans (norm_add_le _ _) _,
  exact add_le_add (norm_add_le _ _) rfl.le,
end

lemma norm_sub_comm {a b : ℝ} : ∥a - b∥ = ∥b - a∥ :=
begin
  have : b - a = (-1) * (a - b), ring,
  rw [this, norm_mul],
  simp,
end

/-- You could rearrange this lemma to actually choose g for the user, but I don't
understand that syntax so would welcome help! -/
lemma uniform_convergence_of_uniform_cauchy
(f : ℕ → ℝ → ℝ)
(g : ℝ → ℝ)
(s : set ℝ)
(hfg : ∀ x : ℝ, x ∈ s → tendsto (λ n, f n x) at_top (nhds (g x)))
(hu : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ m : ℕ, m ≥ N → ∀ n : ℕ, n ≥ N → ∀ x : ℝ, x ∈ s → ∥f m x - f n x∥ < ε) :
tendsto_uniformly_on f g at_top s :=
begin
  rw tendsto_uniformly_on_iff,
  intros ε hε,
  have half_ε : (2⁻¹ * ε) > 0, simp [hε.lt],
  rw eventually_at_top,

  specialize hu (2⁻¹ * ε) half_ε,
  cases hu with N hN,

  use N,
  intros n hn x hx,

  specialize hfg x hx,
  rw metric.tendsto_nhds at hfg,
  specialize hfg (2⁻¹ * ε) half_ε,
  rw eventually_at_top at hfg,
  cases hfg with N2 hN2,

  let m := max N N2,

  specialize hN n hn m (by simp) x hx,
  specialize hN2 m (by simp),
  rw dist_eq_norm,
  rw dist_eq_norm at hN2,
  rw norm_sub_comm,
  have : f n x - g x = (f n x - f m x) + (f m x - g x), ring,
  rw this,
  have : ∥(f n x - f m x) + (f m x - g x)∥ ≤ ∥f n x - f m x∥ + ∥f m x - g x∥, exact norm_add_le _ _,
  refine lt_of_le_of_lt this _,

  have : ∥f n x - f m x∥ + ∥f m x - g x∥ < (2⁻¹ * ε) + (2⁻¹ * ε),
  exact add_lt_add hN hN2,
  exact lt_of_lt_of_eq this (by ring),
end

lemma uniform_cauchy_of_uniform_convergence
(f : ℕ → ℝ → ℝ)
(g : ℝ → ℝ)
(s : set ℝ)
(hu : tendsto_uniformly_on f g at_top s) :
∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ m : ℕ, m ≥ N → ∀ n : ℕ, n ≥ N → ∀ x : ℝ, x ∈ s → ∥f m x - f n x∥ < ε :=
begin
  intros ε hε,
  have half_ε : (2⁻¹ * ε) > 0, simp [hε.lt],
  rw tendsto_uniformly_on_iff at hu,
  specialize hu (2⁻¹ * ε) half_ε,
  rw eventually_at_top at hu,
  cases hu with N hN,
  use N,
  intros m hm n hn x hx,

  have hmm := hN m hm x hx,
  have hnn := hN n hn x hx,
  rw dist_eq_norm at *,

  have : f m x - f n x = f m x - g x + (g x - f n x), ring,
  rw this,
  refine lt_of_le_of_lt (norm_add_le _ _) _,
  rw norm_sub_comm at hmm,
  refine lt_of_lt_of_eq (add_lt_add hmm hnn) _,
  ring,
end

lemma dumb { a b c : ℝ } : (-1) * a / (b - c) = a / (c - b) :=
begin
  ring_nf,
  rw mul_comm,
  rw ←mul_neg,
  rw neg_inv,
  rw neg_sub,
  rw mul_comm,
end

lemma fdfdfd { a b : ℝ} : min a b = a ∨ min a b = b :=
begin
  exact min_choice a b
end

lemma min_eq_max_iff_eq {a b : ℝ} : min a b = max a b ↔ a = b := begin
  refine ⟨(λ heq, _), (λ h, by simp [h])⟩,
  {
    cases min_choice a b,
    rw h at heq,
    rw min_eq_left_iff at h,
    have := max_eq_left_iff.mp heq.symm,
    exact ge_antisymm this h,

    rw h at heq,
    rw min_eq_right_iff at h,
    have := max_eq_right_iff.mp heq.symm,
    exact le_antisymm this h,
  },
end

lemma mean_value_theorem_for_differences
(f : ℕ → ℝ → ℝ)
(f' : ℕ → ℝ → ℝ)
(g : ℝ → ℝ)
(g' : ℝ → ℝ)
(x r R : ℝ)
(hrR : r < R)
(hf : ∀ (n : ℕ), ∀ (y : ℝ), y ∈ ball x R → has_deriv_at (f n) (f' n y) y)
(hfg : ∀ (y : ℝ), y ∈ closed_ball x r → tendsto (λ n, f n y) at_top (nhds (g y)))
(hfg' : tendsto_uniformly_on f' g' at_top (closed_ball x r)) :
∀ (m n : ℕ) (x' y : ℝ), x' ∈ closed_ball x r → y ∈ closed_ball x r → x' ≠ y →
    ∃ (z : ℝ), z ∈ closed_ball x r ∧ (x' - y)⁻¹ * ((f m x' - f n x') - (f m y - f n y)) = f' m z - f' n z :=
begin
  intros m n y' z' hy' hz' h,
  let y := min y' z',
  let z := max y' z',
  have hy : y ∈ closed_ball x r,
  {
    cases le_total y' z' with h h,
    have : y = y', by simp [h],
    rw this, exact hy',
    have : y = z', by simp [h],
    rw this, exact hz',
  },
  have hz : z ∈ closed_ball x r, {
    cases le_total y' z' with h h,
    have : z = z', by simp [h],
    rw this, exact hz',
    have : z = y', by simp [h],
    rw this, exact hy',
  },
  have hyz : y < z, { exact lt_of_le_of_ne min_le_max (λ hb, h (min_eq_max_iff_eq.mp hb)), },
  have hfc : continuous_on (f m - f n) (set.Icc y z), sorry,
  have hff' : ∀ (x : ℝ), x ∈ set.Ioo y z → has_deriv_at (f m - f n) (f' m x - f' n x) x, sorry,
  have mvt := exists_has_deriv_at_eq_slope (f m - f n) (f' m - f' n) hyz hfc hff',
  rcases mvt with ⟨c, hc, hc'⟩,
  use c,
  split,
  { sorry, },
  have : (y' - z')⁻¹ * (f m y' - f n y' - (f m z' - f n z')) = (y - z)⁻¹ * (f m y - f n y - (f m z - f n z)),
  { sorry, },
  rw this,
  simp at hc',
  have : (f m z - f n z - (f m y - f n y)) / (z - y) = (y - z)⁻¹ * (f m y - f n y - (f m z - f n z)),
  {
    have : f m z - f n z - (f m y - f n y) = (-1) * (f m y - f n y - (f m z - f n z)), ring,
    rw this,
    have : (-1) * (f m y - f n y - (f m z - f n z)) / (z - y) = (f m y - f n y - (f m z - f n z)) / (y - z), exact dumb,
    rw this,
    ring,
  },
  rw ←this,
  exact hc'.symm,
end

lemma difference_quotients_converge
(f : ℕ → ℝ → ℝ)
(g : ℝ → ℝ)
(x r : ℝ)
(hfg : ∀ (y : ℝ), y ∈ closed_ball x r → tendsto (λ n, f n y) at_top (nhds (g y))) :
∀ y : ℝ, y ∈ closed_ball x r → ∀ z : ℝ, z ∈ closed_ball x r → tendsto (λ n : ℕ, ∥z - y∥⁻¹ * ((f n z) - (f n y))) at_top (nhds (∥z - y∥⁻¹ * ((g z) - (g y)))) :=
begin
  intros y hy z hz,
  apply tendsto.const_mul,
  exact tendsto.sub (hfg z hz) (hfg y hy),
end

lemma difference_quotients_converge_uniformly
(f : ℕ → ℝ → ℝ)
(f' : ℕ → ℝ → ℝ)
(g : ℝ → ℝ)
(g' : ℝ → ℝ)
(x r R : ℝ)
(hrR : r < R)
(hf : ∀ (n : ℕ), ∀ (y : ℝ), y ∈ ball x R → has_deriv_at (f n) (f' n y) y)
(hfg : ∀ (y : ℝ), y ∈ closed_ball x r → tendsto (λ n, f n y) at_top (nhds (g y)))
(hfg' : tendsto_uniformly_on f' g' at_top (closed_ball x r)) :
∀ y : ℝ, y ∈ closed_ball x r → tendsto_uniformly_on (λ n : ℕ, λ z : ℝ, ∥z - y∥⁻¹ * ((f n z) - (f n y))) (λ z : ℝ, ∥z - y∥⁻¹ * ((g z) - (g y))) at_top ((closed_ball x r)) :=
begin
  -- Proof strategy: Rewrite the Cauchy sequence of difference quotients as
  -- a difference quotient. Then apply the mean value theorem and the uniform
  -- convergence of the derivatives
  intros y hy,
  apply uniform_convergence_of_uniform_cauchy,
  refine difference_quotients_converge _ _ _ _ hfg y hy,
  intros ε hε,

  cases uniform_cauchy_of_uniform_convergence _ _ _ hfg' ε hε with N hN,
  use N,
  intros m hm n hn z hz,
  rw [←mul_sub, ←norm_inv, norm_mul, norm_norm, ←norm_mul],
  by_cases hzy : z = y,
  { simp [hzy, hε.lt], },
  have hmvt := mean_value_theorem_for_differences f f' g g' x r R hrR hf hfg hfg' m n z y hz hy hzy,
  rcases hmvt with ⟨ξ, hξ, hξ'⟩,

  have : (f m z - f n z - (f m y - f n y)) = (f m z - f m y - (f n z - f n y)), ring,
  rw [←this, hξ'],
  exact hN m hm n hn ξ hξ,
end

lemma uniform_convergence_of_uniform_convergence_derivatives
(f : ℕ → ℝ → ℝ)
(f' : ℕ → ℝ → ℝ)
(g : ℝ → ℝ)
(g' : ℝ → ℝ)
(x r R : ℝ)
(hrpos : 0 < r)
(hrR : r < R)
(hf : ∀ (n : ℕ), ∀ (y : ℝ), y ∈ ball x R → has_deriv_at (f n) (f' n y) y)
(hfg : ∀ (y : ℝ), y ∈ closed_ball x r → tendsto (λ n, f n y) at_top (nhds (g y)))
(hfg' : tendsto_uniformly_on f' g' at_top (closed_ball x r)) :
tendsto_uniformly_on f g at_top (closed_ball x r) :=
begin
  refine uniform_convergence_of_uniform_cauchy _ _ _ hfg _,
  intros ε hε,
  have hxcb : x ∈ closed_ball x r, { rw mem_closed_ball, simp, exact hrpos.le, },
  have := metric.cauchy_seq_iff.mp (hfg x hxcb).cauchy_seq,
  have two_inv_pos : 0 < (2 : ℝ)⁻¹, simp,
  have ε_over_two_pos : 0 < (2⁻¹ * ε),
  { exact mul_pos two_inv_pos hε.lt, },
  specialize this (2⁻¹ * ε) ε_over_two_pos.gt,
  cases this with N1 hN1,

  have foo := uniform_cauchy_of_uniform_convergence _ _ _ hfg',
  have : 0 < (2⁻¹ * r⁻¹ * ε), {
    exact mul_pos (mul_pos (by norm_num) (by simp [hrpos])) hε.lt,
  },
  specialize foo (2⁻¹ * r⁻¹ * ε) this.gt,
  cases foo with N2 hN2,

  let N := max N1 N2,
  use N,
  intros m hm n hn y hy,

  have : f m y - f n y = (f m y - f n y) - (f m x - f n x) + (f m x - f n x), ring,
  rw this,
  have : ∥f m y - f n y - (f m x - f n x) + (f m x - f n x)∥ ≤ ∥f m y - f n y - (f m x - f n x)∥ + ∥f m x - f n x∥, exact norm_add_le _ _,
  refine lt_of_le_of_lt this _,

  have : ∥f m y - f n y - (f m x - f n x)∥ = ∥y - x∥ * (∥y - x∥⁻¹ * ∥f m y - f n y - (f m x - f n x)∥), {
    by_cases hyxx : y = x,
    { simp [hyxx], },
    have hxyy : y - x ≠ 0, exact λ H, hyxx (sub_eq_zero.mp H),
    have hxyy' : ∥y - x∥ ≠ 0, simp [hxyy],
    exact (mul_inv_cancel_left₀ hxyy' _).symm,
  },
  rw this,
  by_cases h : y = x,
  { simp only [h, sub_self, norm_zero, mul_zero, zero_add],
    refine lt_trans (hN1 m (ge_trans hm (le_max_left N1 N2).ge) n (ge_trans hn (le_max_left N1 N2).ge)) _,
    rw mul_lt_iff_lt_one_left hε.lt,
    norm_num, },

  rcases mean_value_theorem_for_differences f f' g g' x r R hrR hf hfg hfg' m n y x hy hxcb h with ⟨z, hz, hz'⟩,
  conv {to_lhs, congr, congr, skip, rw ←norm_inv, rw ←norm_mul, rw hz', },
  specialize hN2 m (ge_trans hm (by simp)) n (ge_trans hn (by simp)) z hz,
  have hyx : ∥y - x∥ ≤ r, { rw mem_closed_ball at hy, exact hy, },
  specialize hN1 m (ge_trans hm (by simp)) n (ge_trans hn (by simp)),
  rw dist_eq_norm at hN1,

  have : ε = (2⁻¹ * ε) + (2⁻¹ * ε), ring,
  rw this,

  have : ∥y - x∥ * ∥f' m z - f' n z∥ < 2⁻¹ * ε, {
    sorry,
  },
  exact add_lt_add this hN1,
end

/-! (d/dx) lim_{n → ∞} f_n x = lim_{n → ∞} f'_n x on a closed ball when the f'_n are
continuous and converge _unifomrly_ to their limit -/
lemma swap_limit_and_derivative
(f : ℕ → ℝ → ℝ)
(f' : ℕ → ℝ → ℝ)
(g : ℝ → ℝ)
(g' : ℝ → ℝ)
(x r R : ℝ)
(hrR : r < R)
(hf : ∀ (n : ℕ), ∀ (y : ℝ), y ∈ ball x R → has_deriv_at (f n) (f' n y) y)
(hfg : ∀ (y : ℝ), y ∈ closed_ball x r → tendsto (λ n, f n y) at_top (nhds (g y)))
(hfg' : tendsto_uniformly_on f' g' at_top (closed_ball x r)) :
∀ y : ℝ, y ∈ ball x r → has_deriv_at g (g' y) y :=
begin
  -- We do the famous "ε / 3 proof" which will involve several bouts of utilizing
  -- uniform continuity. First we setup our goal in terms of ε and δ
  intros y hy,
  rw has_deriv_at_iff_tendsto,
  rw tendsto_nhds_nhds,

  -- Now some important auxiliary facts such as:
  have hrpos : 0 < r, {
    rw mem_ball at hy,
    calc 0 ≤ dist y x : dist_nonneg ... < r : hy,
  },

  have hball_mem : ∀ z, z ∈ ball x r → z ∈ ball x R,
  { intros z hz,
    rw mem_ball,
    rw mem_ball at hz,
    calc dist z x < r : hz ... < R : hrR, },

  have hbig_ball_mem : ∀ z, z ∈ closed_ball x r → z ∈ ball x R,
  exact (λ z hz, by calc dist z x ≤ r : hz ... < R : hrR),

  have hyR : y ∈ ball x R, exact hball_mem y hy,

  have hyc : y ∈ closed_ball x r,
  { rw mem_ball at hy,
    exact hy.le, },

  -- The closed ball is compact
  have hball : is_compact (closed_ball x r),
  exact compact_iff_closed_bounded.mpr ⟨is_closed_ball, bounded_closed_ball⟩,

  -- has_deriv_at implies continuity of primal
  have hfc : ∀ (n : ℕ), continuous_on (f n) (closed_ball x r),
  exact λ n z hz, (hf n z (hbig_ball_mem z hz)).continuous_at.continuous_within_at,

  -- continuity of primal implies uniform continuity
  have hfuc : ∀ (n : ℕ), uniform_continuous_on (f n) (closed_ball x r),
  exact (λ n, hball.uniform_continuous_on_of_continuous (hfc n)),

  -- difference of differentiable functions is differentiable
  have hfmndiff : ∀ (m n : ℕ) (y : ℝ), y ∈ ball x R → has_deriv_at (f m - f n) (f' m y - f' n y) y,
  exact (λ m n y hy, (hf m y hy).sub (hf n y hy)),

  -- mean value theorem applied to differences
  have hfmnmvt := mean_value_theorem_for_differences f f' g g' x r R hrR hf hfg hfg',

  -- uniform convergence of the derivatives implies uniform convergence of the primal
  have hfguc := uniform_convergence_of_uniform_convergence_derivatives f f' g g' x r R hrpos hrR hf hfg hfg', -- tendsto_uniformly_on f g at_top (closed_ball x r),

  -- convergence of the primal and uniform convergence of the derivatives implies
  -- uniform convergence of the difference quotients
  have hdiff := difference_quotients_converge_uniformly f f' g g' x r R hrR hf hfg hfg' y hyc,

  -- The first (ε / 3) comes from the convergence of the derivatives
  intros ε hε,
  have : 0 < (3 : ℝ)⁻¹, simp, linarith,
  have ε_over_three_pos : 0 < (3⁻¹ * ε),
  { exact mul_pos this hε.lt, },
  rw tendsto_uniformly_on_iff at hfg',
  specialize hfg' (3⁻¹ * ε) ε_over_three_pos.gt,
  rw eventually_at_top at hfg',
  rcases hfg' with ⟨N1, hN1⟩,

  -- The second (ε / 3) comes from the uniform convergence of the difference quotients
  rw tendsto_uniformly_on_iff at hdiff,
  specialize hdiff (3⁻¹ * ε) ε_over_three_pos.gt,
  rw eventually_at_top at hdiff,
  rcases hdiff with ⟨N2, hN2⟩,

  -- These two N determine our final N
  let N := max N1 N2,

  -- The final (ε / 3) comes from the definition of a derivative
  specialize hf N y hyR,
  rw has_deriv_at_iff_tendsto at hf,
  rw tendsto_nhds_nhds at hf,
  specialize hf (3⁻¹ * ε) ε_over_three_pos.gt,
  rcases hf with ⟨δ', hδ', hf⟩,

  -- Choose our final δ
  let δ := min (r - dist y x) δ',
  have hδ : δ > 0, {
    refine lt_min _ hδ'.lt,
    rw sub_pos,
    exact hy,
  },

  -- Start the final manipulation
  use [δ, hδ],
  intros x' hx',
  have hxc : x' ∈ closed_ball x r, {
    rw mem_closed_ball,
    apply le_of_lt,
    have foo : dist x' y < r - dist y x, calc dist x' y < δ : hx' ... ≤ r - dist y x : by simp [δ],
    have ff : dist x' y + dist y x < r, linarith [foo],
    have fff : dist x' x ≤ dist x' y + dist y x, exact dist_triangle _ _ _,
    calc dist x' x ≤ dist x' y + dist y x : fff ... < r : ff,
  },
  have hxy : dist x' y < δ', calc dist x' y < δ : hx' ... ≤ δ' : by simp [δ],
  specialize hf hxy,

  -- There's a technical issue where we need to rule out the case y = x'
  by_cases hy' : y = x',
  { simp [hy', hε.lt], },

  have hx'y : x' - y ≠ 0, exact λ H, hy' (sub_eq_zero.mp H).symm,

  -- Now our three inequalities come from `hf`, `hN1`, and `hN2`. Specialize
  -- to make this clear
  specialize hN1 N (by simp) y hyc,
  specialize hN2 N (by simp) x' hxc,
  rw dist_eq_norm at *,
  simp only [algebra.id.smul_eq_mul, sub_zero, norm_mul, norm_inv, norm_norm],

  -- Begin algebraic manipulations
  have : ∥x' - y∥⁻¹ * ∥g x' - g y - (x' - y) * g' y∥ =
    ∥(x' - y)⁻¹ * (g x' - g y) - g' y∥,
  { rw [←norm_inv, ←norm_mul],
    congr,
    rw [mul_sub, mul_cancel_inv_left₀ hx'y], },
  rw this,

  -- Add zero a couple times and regroup
  have : (x' - y)⁻¹ * (g x' - g y) - g' y =
    (x' - y)⁻¹ * (g x' - g y) - (x' - y)⁻¹ * (f N x' - f N y) +
    (x' - y)⁻¹ * (f N x' - f N y) - (f' N y) +
    (f' N y) - g' y,
  { ring, },
  rw this,

  -- Triangle inequality twice
  have hregroup : (x' - y)⁻¹ * (g x' - g y) - (x' - y)⁻¹ * (f N x' - f N y) +
    (x' - y)⁻¹ * (f N x' - f N y) - (f' N y) +
    (f' N y) - g' y =
    ((x' - y)⁻¹ * (g x' - g y) - (x' - y)⁻¹ * (f N x' - f N y)) +
    ((x' - y)⁻¹ * (f N x' - f N y) - (f' N y)) +
    ((f' N y) - g' y),
  { ring, },
  have : ∥(x' - y)⁻¹ * (g x' - g y) - (x' - y)⁻¹ * (f N x' - f N y) +
    (x' - y)⁻¹ * (f N x' - f N y) - (f' N y) +
    (f' N y) - g' y∥ ≤
    ∥(x' - y)⁻¹ * (g x' - g y) - (x' - y)⁻¹ * (f N x' - f N y)∥ +
    ∥(x' - y)⁻¹ * (f N x' - f N y) - (f' N y)∥ +
    ∥(f' N y) - g' y∥,
  { rw hregroup,
    exact norm_add_three_le, },
  refine lt_of_le_of_lt this _,

  -- Get contributing factors to the right shape
  rw norm_sub_comm at hN1,
  rw [←mul_sub, norm_mul, ←norm_inv, norm_norm, ←norm_mul, mul_sub] at hN2,
  simp only [algebra.id.smul_eq_mul, sub_zero, norm_mul, norm_inv, norm_norm] at hf,
  rw [←norm_inv, ←norm_mul, mul_sub, mul_cancel_inv_left₀ hx'y] at hf,

  -- Final inequalities
  refine lt_of_lt_of_le (add_lt_add_of_lt_of_lt (add_lt_add_of_lt_of_lt hN2 hf) hN1) _,
  apply le_of_eq,
  ring,
end

variables {α : Type*} [add_comm_monoid α]

def head_sum (f : ℕ → α) : (ℕ → α) := (λ n : ℕ, ∑ i in range n, f i)

variables [topological_space α]

def nat_summable (f : ℕ → α) : Prop := ∃ (a : α), tendsto (head_sum f) at_top (nhds a)

namespace nat
namespace arithmetic_function
variables {R : Type*} [has_zero R] [has_abs R]
(f : arithmetic_function ℂ) (g h : ℂ → ℂ)
(s t : ℂ) (r : ℝ)


/-- A Dirichlet series of a function `f` at `s` is itself a function from `ℕ` to `ℂ`
which returns the `n`th term of the sum ∑ (f n) / n ^ s -/
noncomputable def dirichlet_series := (λ n : ℕ, (f n) / ((n : ℂ) ^ s))

noncomputable def dirichlet_series' := ∑' i, (λ n : ℕ, (f n) / ((n : ℂ) ^ s)) i

noncomputable def dirichlet_head_sum := (λ n : ℕ, λ s : ℂ, ∑ i in range n, (dirichlet_series f s i))

/- Should this be `real.log` or `complex.log`? -/
noncomputable def dderiv : arithmetic_function ℂ := {
  to_fun := λ n : ℕ, (f n) * (real.log n),
  map_zero' := by simp,
}

namespace dirichlet_series
localized "notation `D` := nat.arithmetic_function.dirichlet_series" in dirichlet_series
localized "notation `D'` := nat.arithmetic_function.dirichlet_series'" in dirichlet_series
localized "notation `S` := nat.arithmetic_function.dirichlet_head_sum" in dirichlet_series

/-! ### Definitions of convergence -/
/-- The Dirichlet series is convergent at a point -/
def convergent_at : Prop := nat_summable (D f s)

/-- The Dirichlet series is convergent in a right half-plane -/
def convergent : Prop := ∀ s : ℂ, r < s.re → convergent_at f s

/-- The Dirichlet series is absolutely convergent at a point -/
def abs_convergent_at : Prop := summable (D f s)

/-- The Dirichlet series is absolutely convergent in a right half-plane -/
def abs_convergent : Prop := ∀ s : ℂ, r < s.re → abs_convergent_at f s

/-- The traditional definition of absolutely convergent. Equivalent to our notion of
absolute convergence. See `abs_convergent_at_iff_norm_convergent_at` -/
def norm_convergent_at : Prop := summable (λ n : ℕ, ∥(D f s) n ∥)

/-- The traditional definition of absolutely convergent on a right half-plane.
Equivalent to our notion of
absolute convergence. See `abs_convergent_iff_norm_convergent` -/
def norm_convergent : Prop := ∀ s : ℂ, r < s.re → norm_convergent_at f s

/-- Uniform convergence on a closed ball around a point -/
def uniform_convergent_at : Prop := tendsto_uniformly_on (S f) (D' f) at_top (closed_ball s r)

/-- The set of all complex numbers strictly to the right of `r` -/
def half_plane : set ℂ := { z : ℂ | r < z.re }

/-- The set of all complex numbers at or to the right of `r` -/
def closed_half_plane : set ℂ := { z : ℂ | r ≤ z.re }

/-! ### Relationships between the various convergence modes

Currently enumerating the main theorems which will be turned into
many more useful lemmas later
-/

/-- The notion of norm convergence and absolute convergence are equivalent -/
lemma abs_convergent_at_iff_norm_convergent_at : abs_convergent_at f s ↔ norm_convergent_at f s :=
begin
  sorry,
end

/-- The notion of norm convergence and absolute convergence are equivalent, but
sometimes one may be easier to use than the other -/
lemma abs_convergent_iff_norm_convergent : abs_convergent f r ↔ norm_convergent f r :=
⟨
  λ h s hs, (abs_convergent_at_iff_norm_convergent_at f s).mp (h s hs),
  λ h s hs, (abs_convergent_at_iff_norm_convergent_at f s).mpr (h s hs),
⟩

/-- Convergence at a point implies convergence to the right of that point -/
lemma convergent_of_convergent_at
(hfs : convergent_at f s) :
convergent f s.re :=
begin
  sorry
end

/-- Norm convergence at a point implies norm convergence to the right of that point -/
lemma norm_convergent_of_norm_convergent_at
(hfs : norm_convergent_at f s) :
norm_convergent f s.re :=
begin
  intros t ht,
  refine summable_of_norm_bounded _ hfs _,
  unfold dirichlet_series,
  intros i,
  by_cases hi : i = 0,
  { simp [hi], },
  rw [real.norm_eq_abs, complex.norm_eq_abs, complex.norm_eq_abs, complex.abs_abs,
    complex.abs_div, complex.abs_div],
  refine div_le_div (complex.abs_nonneg _) rfl.le _ _,
  { rw complex.abs_pos,
    intros h,
    rw complex.cpow_eq_zero_iff at h,
    rcases h with ⟨hi', _⟩,
    norm_cast at hi', },
  { have : 1 ≤ i, exact one_le_iff_ne_zero.mpr hi,
    have : 0 < i, linarith [this],
    have aa : 0 < (i : ℝ), { norm_cast, exact this, },
    have bb : (i : ℂ) = ((i : ℝ) : ℂ), simp,
    rw bb,
    rw complex.abs_cpow_eq_rpow_re_of_pos aa,
    rw complex.abs_cpow_eq_rpow_re_of_pos aa,
    refine real.rpow_le_rpow_of_exponent_le _ ht.le,
    norm_cast,
    exact one_le_iff_ne_zero.mpr hi, },
end

/-- Absolute convergence at a point implies absolute convergence to the right of that point -/
lemma abs_convergent_of_abs_convergent_at
(hfs : abs_convergent_at f s) :
abs_convergent f s.re :=
begin
  rw abs_convergent_at_iff_norm_convergent_at at hfs,
  rw abs_convergent_iff_norm_convergent,
  exact norm_convergent_of_norm_convergent_at _ _ hfs,
end

/-- Convergence implies absolute convergence eventually -/
lemma abs_convergent_of_convergent
(hfs : convergent f r) :
abs_convergent f (r + 1) :=
begin
  sorry
end

lemma uniform_convergent_of_convergent
(hfs : convergent f r)
(hs : r < s.re)
:
uniform_convergent_at f s (s.re - r) :=
begin
  sorry,
end

/-! ### Proving convergence -/

lemma abs_convergent_of_eventually_bounded
(hf : ∀ᶠ (n : ℕ) in at_top, complex.abs (f n) ≤ r) : abs_convergent f 1 :=
begin
  sorry
end

lemma abs_convergent_of_bounded
(hf : ∀ (n : ℕ), complex.abs (f n) ≤ r) : abs_convergent f 1 :=
begin
  sorry,
end

/-! ### Differentiability and Convergence -/

/-- Convergence implies holomorphic on the open right half-plane -/
lemma derivative_of_convergent
(hfs : convergent f r)
(hs : r < s.re) :
has_deriv_at (D' f) (D' f.dderiv s) s :=
begin
  sorry,
end

/-- Convergence implies holomorphic on the open right half-plane -/
lemma differentiable_at_of_convergent
(hfs : convergent f r) (hs : r < s.re) :
differentiable_at ℂ (D' f) s :=
begin
  sorry,
end

/-- Holomorphic extension implies convergence -/
lemma convergent_of_differentiable_on
(hg : differentiable_on ℂ g $ half_plane r)
(hfg : ∀ (z : ℂ), z ∈ half_plane r → D' f z = g z) :
convergent f r :=
begin
  sorry,
end

/-! ### Important integrals -/


-- noncomputable def tmp_lo := (λ n : ℕ, (n : ℝ)⁻¹)
-- def tmp_hi := (λ n : ℕ, (n : ℝ))
-- noncomputable def tmp (S : ℝ → ℂ) := λ n : ℕ, (∫ (x : ℝ) in (tmp_lo n)..(tmp_hi n), S x)
-- noncomputable def imp_int_zero_inf (S : ℝ → ℂ) := lim at_top (tmp S)

-- lemma as_integral
-- (hfr : abs_convergent f r)
-- (hrs : r < s.re)
-- :
-- D' f s = s * ∫ x in set.Ioi (0 : ℝ), head_sum f ⌊x⌋₊ / x ^ (s + 1)
-- :=
-- begin
--   sorry
-- end

-- lemma useful_integral
-- {S : ℝ → ℂ}
-- (hbounded : ∀ (x : ℝ), complex.abs (S x) ≤ r)
-- (hint : ∀ (a b : ℝ), interval_integrable S real.measure_space.volume a b)
-- :
-- differentiable_on ℂ (λ z : ℂ, ∫ x in set.Ioi (0 : ℝ), (S x) * complex.exp (-z * s)) $ half_plane 0
-- :=
-- begin
--   sorry,
-- end

-- lemma useful_integral_diff


-- lemma norm_convergent_at.of_norm_convergent_at_re_le
-- (hfs : norm_convergent_at f s) (hst : s.re ≤ t.re) : norm_convergent_at f t :=
-- begin
--   unfold norm_convergent_at,
--   unfold dirichlet_series,
--   refine summable_of_norm_bounded _ hfs _,
--   unfold dirichlet_series,
--   intros i,
--   by_cases hi : i = 0,
--   { simp [hi], },
--   rw real.norm_eq_abs, rw complex.norm_eq_abs, rw complex.norm_eq_abs, rw complex.abs_abs,
--   rw complex.abs_div, rw complex.abs_div,
--   apply div_le_div,
--   exact complex.abs_nonneg _,
--   exact rfl.le,
--   rw complex.abs_pos,
--   intros h,
--   rw complex.cpow_eq_zero_iff at h,
--   rcases h with ⟨hi', _⟩,
--   norm_cast at hi',
--   have : 1 ≤ i, exact one_le_iff_ne_zero.mpr hi,
--   have : 0 < i, linarith [this],
--   have aa : 0 < (i : ℝ), { norm_cast, exact this, },
--   have bb : (i : ℂ) = ((i : ℝ) : ℂ), simp,
--   rw bb,
--   rw complex.abs_cpow_eq_rpow_re_of_pos aa,
--   rw complex.abs_cpow_eq_rpow_re_of_pos aa,
--   refine real.rpow_le_rpow_of_exponent_le _ hst,
--   norm_cast,
--   exact one_le_iff_ne_zero.mpr hi,
-- end

-- lemma abs_convergent_at.of_abs_convergent_at_re_le
-- (hfs : abs_convergent_at f s) (hst : s.re ≤ t.re) : abs_convergent_at f t :=
-- begin
--   rw abs_convergent_at_iff_norm_convergent_at at hfs,
--   rw abs_convergent_at_iff_norm_convergent_at,
--   exact hfs.of_norm_convergent_at_re_le f s t hst,
-- end

/-! ### Special functions -/

theorem zeta.abs_convergent : abs_convergent ζ 1 :=
begin
  refine abs_convergent_of_bounded _ 1 _,
  intros i,
  simp [zeta],
  by_cases hi : i = 0,
  simp [hi],
  simp [hi],
end

theorem moebius.abs_convergent : abs_convergent μ 1 :=
begin
  refine abs_convergent_of_bounded _ 1 _,
  intros i,
  simp [moebius],
  by_cases hi : squarefree i,
  simp [hi],
  simp [hi],
end



end dirichlet_series
end arithmetic_function
end nat