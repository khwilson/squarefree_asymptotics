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
def is_convergent_at : Prop := nat_summable (D f s)

/-- The Dirichlet series is convergent in a right half-plane -/
def is_convergent : Prop := ∀ s : ℂ, r < s.re → is_convergent_at f s

/-- The Dirichlet series is absolutely convergent at a point -/
def is_abs_convergent_at : Prop := summable (D f s)

/-- The Dirichlet series is absolutely convergent in a right half-plane -/
def is_abs_convergent : Prop := ∀ s : ℂ, r < s.re → is_abs_convergent_at f s

/-- The traditional definition of absolutely convergent. Equivalent to our notion of
absolute convergence. See `is_abs_convergent_at_iff_is_norm_convergent_at` -/
def is_norm_convergent_at : Prop := summable (λ n : ℕ, ∥(D f s) n ∥)

/-- The traditional definition of absolutely convergent on a right half-plane.
Equivalent to our notion of
absolute convergence. See `is_abs_convergent_iff_is_norm_convergent` -/
def is_norm_convergent : Prop := ∀ s : ℂ, r < s.re → is_norm_convergent_at f s

/-- Uniform convergence on a closed ball around a point -/
def is_uniform_convergent_at : Prop := tendsto_uniformly_on (S f) (D' f) at_top (closed_ball s r)

def half_plane : set ℂ := { z : ℂ | r < z.re }

/-! ### Relationships between the various convergence modes

Currently enumerating the main theorems which will be turned into
many more useful lemmas later
-/

/-- The notion of norm convergence and absolute convergence are equivalent -/
lemma is_abs_convergent_at_iff_is_norm_convergent_at : is_abs_convergent_at f s ↔ is_norm_convergent_at f s :=
begin
  sorry,
end

/-- The notion of norm convergence and absolute convergence are equivalent, but
sometimes one may be easier to use than the other -/
lemma is_abs_convergent_iff_is_norm_convergent : is_abs_convergent f r ↔ is_norm_convergent f r :=
begin
  split,
  {
    intros h,
    intros s hs,
    exact (is_abs_convergent_at_iff_is_norm_convergent_at f s).mp (h s hs),
  },
  {
    intros h,
    intros s hs,
    exact (is_abs_convergent_at_iff_is_norm_convergent_at f s).mpr (h s hs),
  },
end

/-- Convergence at a point implies convergence to the right of that point -/
lemma is_covergent_of_is_convergent_at
(hfs : is_convergent_at f s) :
is_convergent f s.re :=
begin
  sorry
end

/-- Absolute convergence at a point implies absolute convergence to the right of that point -/
lemma is_abs_covergent_of_is_abs_convergent_at
(hfs : is_abs_convergent_at f s) :
is_abs_convergent f s.re :=
begin
  sorry
end

/-- Norm convergence at a point implies norm convergence to the right of that point -/
lemma is_norm_covergent_of_is_norm_convergent_at
(hfs : is_norm_convergent_at f s) :
is_norm_convergent f s.re :=
begin
  rw ←is_abs_convergent_iff_is_norm_convergent,
  rw ←is_abs_convergent_at_iff_is_norm_convergent_at at hfs,
  exact is_abs_covergent_of_is_abs_convergent_at f s hfs,
end

/-- Convergence implies absolute convergence eventually -/
lemma is_abs_convergent_of_is_convergent
(hfs : is_convergent f r) :
is_abs_convergent f (r + 1) :=
begin
  sorry
end

lemma is_uniform_convergent_of_is_convergent
(hfs : is_convergent f r)
(hs : r < s.re)
:
is_uniform_convergent_at f s (s.re - r) :=
begin
  sorry,
end

/-! ### Proving convergence -/

lemma is_abs_convergent_of_eventually_bounded
(hf : ∀ᶠ (n : ℕ) in at_top, complex.abs (f n) ≤ r) : is_abs_convergent f 1 :=
begin
  sorry
end

lemma is_abs_convergent_of_bounded
(hf : ∀ (n : ℕ), complex.abs (f n) ≤ r) : is_abs_convergent f 1 :=
begin
  sorry,
end

/-! ### Differentiability and Convergence -/

/-- Convergence implies holomorphic on the open right half-plane -/
lemma derivative_of_is_convergent
(hfs : is_convergent f r)
(hs : r < s.re) :
has_deriv_at (D' f) (D' f.dderiv s) s :=
begin
  sorry,
end

/-- Convergence implies holomorphic on the open right half-plane -/
lemma differentiable_at_of_is_convergent
(hfs : is_convergent f r) (hs : r < s.re) :
differentiable_at ℂ (D' f) s :=
begin
  sorry,
end

/-- Holomorphic extension implies convergence -/
lemma is_convergent_of_differentiable_on
(hg : differentiable_on ℂ g $ half_plane r)
(hfg : ∀ (z : ℂ), z ∈ half_plane r → D' f z = g z) :
is_convergent f r :=
begin
  sorry,
end

/-! ### Important integrals -/


-- noncomputable def tmp_lo := (λ n : ℕ, (n : ℝ)⁻¹)
-- def tmp_hi := (λ n : ℕ, (n : ℝ))
-- noncomputable def tmp (S : ℝ → ℂ) := λ n : ℕ, (∫ (x : ℝ) in (tmp_lo n)..(tmp_hi n), S x)
-- noncomputable def imp_int_zero_inf (S : ℝ → ℂ) := lim at_top (tmp S)

-- lemma as_integral
-- (hfr : is_abs_convergent f r)
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


-- lemma is_norm_convergent_at.of_is_norm_convergent_at_re_le
-- (hfs : is_norm_convergent_at f s) (hst : s.re ≤ t.re) : is_norm_convergent_at f t :=
-- begin
--   unfold is_norm_convergent_at,
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

-- lemma is_abs_convergent_at.of_is_abs_convergent_at_re_le
-- (hfs : is_abs_convergent_at f s) (hst : s.re ≤ t.re) : is_abs_convergent_at f t :=
-- begin
--   rw is_abs_convergent_at_iff_is_norm_convergent_at at hfs,
--   rw is_abs_convergent_at_iff_is_norm_convergent_at,
--   exact hfs.of_is_norm_convergent_at_re_le f s t hst,
-- end

/-! ### Special functions -/

theorem zeta.is_abs_convergent : is_abs_convergent ζ 1 :=
begin
  refine is_abs_convergent_of_bounded _ 1 _,
  intros i,
  simp [zeta],
  by_cases hi : i = 0,
  simp [hi],
  simp [hi],
end

theorem moebius.is_abs_convergent : is_abs_convergent μ 1 :=
begin
  refine is_abs_convergent_of_bounded _ 1 _,
  intros i,
  simp [moebius],
  by_cases hi : squarefree i,
  simp [hi],
  simp [hi],
end



end dirichlet_series
end arithmetic_function
end nat