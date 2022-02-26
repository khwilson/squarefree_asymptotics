import number_theory.arithmetic_function
import algebra.squarefree
import algebra.order.floor
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral
import hold2

noncomputable theory
open nat finset function filter
open_locale classical topological_space interval big_operators filter asymptotics arithmetic_function


namespace mything

lemma three_add {n : ℕ} (hn : 3 ≤ n) : ∃ n', n = 3 + n' :=
begin
  have : ∃ n', n = 2 + n',
  exact two_add,

end


end mything