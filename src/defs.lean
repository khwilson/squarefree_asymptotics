import number_theory.arithmetic_function
import algebra.squarefree
import algebra.order.floor
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral

noncomputable theory
open nat finset function filter
open_locale topological_space interval big_operators filter asymptotics arithmetic_function

namespace squarefree_sums

def square {α : Type*} [comm_monoid α] (n : α) : Prop := ∃ s, n = s ^ 2

instance : decidable_pred (square : ℕ → Prop)
| n := begin
  have := (nat.exists_mul_self n),
  conv at this {
    to_lhs,
    congr,
    funext,
    rw [←pow_two, eq_comm],
  },
  exact decidable_of_iff' _ this,
end

def ssqrt (n : ℕ) := ite (square n) (sqrt n) 0

def sμ : arithmetic_function ℤ := ⟨
  (λ d : ℕ, arithmetic_function.moebius (ssqrt d)),
  by simp [ssqrt]
⟩

def tμ := sμ * ζ

def squarefree_nat : arithmetic_function ℤ :=
⟨
  (λ d : ℕ, ite (squarefree d) (1 : ℤ) (0 : ℤ)),
  (by {
    have : ¬squarefree 0, exact not_squarefree_zero,
    simp [this],
  }),
⟩

def is_Ot {α : Type*} (f : α → ℝ) (g : α → ℝ) (h : α → ℝ) (l : filter α) : Prop :=
∃ c : ℝ, asymptotics.is_O_with c (f - g) h l

end squarefree_sums