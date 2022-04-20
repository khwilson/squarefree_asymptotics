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
open_locale big_operators arithmetic_function

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

lemma norm_sub_comm {a b : ℝ} : ∥a - b∥ = ∥b - a∥ := sorry

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
(hf' : ∀ (n : ℕ), continuous_on (f' n) (closed_ball x r))
(hfg : ∀ (y : ℝ), y ∈ closed_ball x r → tendsto (λ n, f n y) at_top (nhds (g y)))
(hfg' : tendsto_uniformly_on f' g' at_top (closed_ball x r)) :
∀ y : ℝ, y ∈ ball x r → has_deriv_at g (g' y) y :=
begin
  -- We do the famous "ε / 3 proof" which will involve several bouts of utilizing
  -- uniform continuity. First we setup our goal in terms of ε and δ
  intros y hy,
  rw has_deriv_at_iff_tendsto,
  rw tendsto_nhds_nhds,
  intros ε hε,

  -- Now some important auxiliary facts such as:
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

  -- continuity implies uniform continuity of derivative
  have hf'uc : ∀ (n : ℕ), uniform_continuous_on (f' n) (closed_ball x r),
  exact (λ n, hball.uniform_continuous_on_of_continuous (hf' n)),

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
  -- have hfmnmvt : ∀ (m n : ℕ) (x' y : ℝ), x' ∈ closed_ball x r → y ∈ closed_ball x r → ∃ (z : ℝ), |(f m x' - f n x') - (f m y - f n y)| =

  -- uniform convergence of the derivatives implies uniform convergence of the primal
  have hfguc : tendsto_uniformly_on f g at_top (closed_ball x r),
  { rw tendsto_uniformly_on_iff,
    sorry, },

  -- convergence of the primal and uniform convergence of the derivatives implies
  -- uniform convergence of the difference quotients
  have hdiff : tendsto_uniformly_on (λ n : ℕ, λ z : ℝ, ∥z - y∥⁻¹ * ((f n z) - (f n y))) (λ z : ℝ, ∥z - y∥⁻¹ * ((g z) - (g y))) at_top ((closed_ball x r) \ {y}),
  { sorry, },

  -- The first (ε / 3) comes from the convergence of the derivatives
  rw tendsto_uniformly_on_iff at hfg',
  have : 0 < (3 : ℝ)⁻¹, simp, linarith,
  have ε_over_three_pos : 0 < (3⁻¹ * ε),
  { exact mul_pos this hε.lt, },
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
  have hxc : x' ∈ closed_ball x r, sorry,
  have hxy : dist x' y < δ', sorry,
  specialize hf hxy,

  -- There's a technical issue where we need to rule out the case y = x'
  by_cases hy' : y = x',
  { simp [hy', hε.lt], },

  have hx'y : x' - y ≠ 0, exact λ H, hy' (sub_eq_zero.mp H).symm,

  -- Now our three inequalities come from `hf`, `hN1`, and `hN2`. Specialize
  -- to make this clear
  have hx'' : x' ∈ closed_ball x r \ {y},
  { simp [hxc], intros h, exact hy' h.symm, },
  specialize hN1 N (by simp) y hyc,
  specialize hN2 N (by simp) x' hx'',
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