# The density of squarefree numbers

This repository formally verifies the fact that the density of squarefree numbers is ζ(2)⁻¹. That is, if $\nu : \mathbb{N} \to \{ 0, 1 \}$ is defined as

\[
  \nu(n) =
  \begin{cases}
    1 & n\text{ is squarefree} \\
    0 & n\text{ is not squarfree} \\
  \end{cases}
\]

then

\[
  \sum_{n = 0}^N \nu(n) = \zeta(2)^{-1} N + O\left(\sqrt{N}\right).
\]

## Requirements

We perform this proof in the [Lean](https://leodemoura.github.io/files/lean_cade25.pdf) proof environment with the [mathlib](https://leanprover-community.github.io) library. For more information on setup, consult the [setup guide](https://leanprover-community.github.io/get_started.html).

## Outline of the proof in words

We attempt perhaps the most classic proof of this fact, in which we rewrite $\nu$ is a sum

\[
  \nu(n) = \sum_{d^2 \mid n} \mu(d)
\]

where $\mu(d)$ is the Moebius function. The proof then goes along the usual lines. The first half is all equalities:

\[
  \sum_{n = 0}^N \nu(n)
  = \sum_{n = 0}^N \sum_{d^2 \mid n} \mu(d)
  = \sum_{d = 0}^N \sum_{d^2 \mid n; n \leq N} \mu(d)
  = \sum_{d = 0}^N \lfloor \frac{N}{d^2} \rfloor \mu(d)
  = \sum_{d = 0}^{sqrt{N}} \lfloor \frac{N}{d^2} \rfloor \mu(d)
\]

At this point, we begin estimating. Specifically, we use the facts that:

  1. $\lfloor \frac{N}{d^2} \rfloor$ and $\frac{N}{d^2}$ differ by at most 1 and
  2. The tail sum $\sum_{d = \sqrt{N} + 1}^\infty \frac{1}{d^2} = O(N^{-1/2})$.

These two facts will complete the proof. For a further explication, see [the Wikipedia article](https://en.wikipedia.org/wiki/Square-free_integer) on squarefree integers.

## Outline of the proof in code

The main proof is contained in [moebius_notes.lean](https://github.com/khwilson/squarefree_asymptotics/blob/main/src/moebius_notes.lean), specifically `theorem bigbad` describes the above outline. The equality portion resides in lemmas `step0` through `step3` and the totality is captured in `lemma first_steps`. The lemmas `step4` through `step6` capture the estimation portion. Lemma `step35` bridges the gap between these two, transforming the equalities into asymptotics.

Many auxiliary steps were necessary to get to this point. At this point, I shall confess, this is my first proof in Lean and with Mathlib and so many of these lemmas may already be contained elsewhere or may be much easier to prove. Indeed, over the course of performing this proof, I've cut down multi-hundred line proofs into short ten-liners several times after realizing there's particular facilities available in mathlib.

### Big Step 1: Rewriting $\nu$

The first big obstacle in the proof is showing $\nu(n) = \sum_{d^2 \mid n} \mu(d)$. This is described primarily in [squarefree_rw.lean](https://github.com/khwilson/squarefree_asymptotics/blob/main/src/squarefree_rw.lean), specifically, `theorem squarefree_nat_eq_tμ`, and its cousin `lemma rw_tμ`.

The idea of this proof is to write $\nu$ and $\sum_{d^2 \mid n} \mu(d)$ are both multiplicative (the latter because it is the Dirichlet convolution of two more easily seen as multiplicative functions). This occurs primarily in [multiplicativaty.lean](https://github.com/khwilson/squarefree_asymptotics/blob/main/src/multiplicativaty.lean). Then we show that the functions agree on prime powers, and thus the functions agree (using `lemma multiplicative_eq_iff_eq_on_prime_powers` in [multiplicativaty.lean](https://github.com/khwilson/squarefree_asymptotics/blob/main/src/multiplicativaty.lean)).

Along the way, we define several auxiliary functions in [defs.lean](https://github.com/khwilson/squarefree_asymptotics/blob/main/src/defs.lean) and prove various facts about them in [lemmas_on_defs.lean](https://github.com/khwilson/squarefree_asymptotics/blob/main/src/lemmas_on_defs.lean).

### Miniboss: Floor division and real division differ by at most 1

Our next main obstacle is showing that $\lfloor \frac{N}{d^2} \rfloor$ and $\frac{N}{d^2}$ differ by at most $1$. This proof occurs in `lemma floor_off_by_le_one` in [general.lean](https://github.com/khwilson/squarefree_asymptotics/blob/main/src/general.lean).

### Big Obstactle 2: Completing the sum

Finally, the rest of the repository is deals with bounding the error we pick up from completing the sum. This error is itself the tail sum $\sum_{d = \sqrt{N} + 1}^\infty \frac{1}{d^2}$ and we need to show $\sum_{d = \sqrt{N} + 1}^\infty \frac{1}{d^2} = O(N^{-1/2})$.

This involves two major components: Describing various lemmas on summability in [summability.lean](https://github.com/khwilson/squarefree_asymptotics/blob/main/src/summability.lean) and swapping the tail sum for a tail integral in [integral_facts.lean](https://github.com/khwilson/squarefree_asymptotics/blob/main/src/integral_facts.lean).

The first file is mostly just making manipulation easier, e.g., replacing things that look like `∑' (i : ℕ), f ↑i - ∑' (i : ℕ), ite (↑i ≤ b) (f i) 0 = ∑' (i : ℕ), ite (b < ↑i) (f ↑i) 0`, i.e., that a sum minus its head sum is its tail sum. These are all fiddly, and almost certainly there's a better way to do this. Most of the file is dealing with weird casting issues between $\mathbb{N}$ and $\mathbb{R}$.

The second file could _definitely_ be improved. But the main lemma is `lemma antitone_sum_le_integral` which says:

```lean
lemma antitone_sum_le_integral
{a b : ℕ}
{f : ℝ → ℝ}
(hab : a ≤ b)
(hf : antitone_on f (set.Icc a b))
:
∑ x in finset.Ico (a + 1) (b + 1), f x  ≤ ∫ x in a..b, f x
```

that is, the sum of a decreasing function evaluated at integers in a range is less than or equal to the same function integrated over that range. (Note the shifts!) For completeness, there is a companion lemma which is unused in the main proof, but which is the opposite:

```lean
lemma antitone_integral_le_sum
{a b : ℕ}
{f : ℝ → ℝ}
(hab : a ≤ b)
(hf : antitone_on f (set.Icc a b)) :
∫ x in a..b, f x ≤ ∑ x in finset.Ico a b, f x
```

### The long road to Mithlond: Manipulating asymptotics

In order to make all of this come together, we derive several lemmas on asymptotics in [lemmas_on_asymptotics.lean](https://github.com/khwilson/squarefree_asymptotics/blob/main/src/lemmas_on_asymptotics.lean). In particular, we introduce the notation (should be changed!) `is_Ot` which allows users to express `f = g + O(h)` and several lemmas on how this can be manipulated.

There are also several [lemmas_on_tendsto.lean](https://github.com/khwilson/squarefree_asymptotics/blob/main/src/lemmas_on_tendsto.lean) and one particularly nasty computation in [archive.lean](https://github.com/khwilson/squarefree_asymptotics/blob/main/src/archive.lean). In both instances, I estimate that there must be a better way to do these.

## Thoughts on this proof

First and foremost, this was very fun, though frustrating at times. I've heard people say that it's "addicting" to try and eliminate goals, and I really must agree. I was doing this proof primarily instead of reading novels in bed, and there were several nights I stayed up way too late picking off goals.

On the other hand, this system is really not ready for anything even remotely resembling analysis. Primarily the obstacles come in two forms: small examples and fiddly arithmetic.

The first of these is probably the most annoying. Take, for example, `lemma nat_div_sqrt_sqrt_eq_one` in [moebius_notes.lean](https://github.com/khwilson/squarefree_asymptotics/blob/main/src/moebius_notes.lean). It says

```lean
lemma nat_div_sqrt_sqrt_eq_one
{n : ℕ} :
9 ≤ n → n.div (sqrt n * sqrt n) = 1
```

That is, for all natural numbers `n` which are at least 9, dividing `n` as an integer (i.e., keeping only the integral part) by `sqrt n * sqrt n` is `1`. The trickiness here arises from the fact that `sqrt n` for natural numbers is defined as the largest natural number `m` such that `m * m ≤ n`. For big numbers, indeed `9 ≤ n`, this doesn't create a problem, but `sqrt 8 = 2` and so `8.div (sqrt 8 * sqrt 8) = 2`.

This is a classic example in asymptotics. Something is _morally_ true, but there are lots of counterexamples for small numbers. This phenomenon leads to practicing mathematicians to say "for sufficiently large" a lot, and everyone agrees to just implicitly keep bumping up this number for every time this phrase is found.

In Lean, you have to specify exactly what you mean by "sufficiently large," and you end up carrying around a bunch of `(hb : 200 ≤ b)` assumptions. Or if you want to be specific, you end up with giant strings of `max`'s.

On the one hand, this is amazing! Analysts can often get into trouble by ending up in loops where things are "small enough" or "large enough". On the other hand, there are a lot of facts like "polynomials with positive leading coefficients go to infinity" which are easy to think about but very fiddly to write down in Lean. See, e.g., `lemma quadratic_monotone_eventually` in [moebius_notes.lean](https://github.com/khwilson/squarefree_asymptotics/blob/main/src/moebius_notes.lean).

If there were a good way to capture these notions of "sufficiently large" and have the system handle them, I think this would be a massive improvement!

The second major problem is arithmetic remains very fiddly. Here are three examples:

  * Casting
  * Unexpected behavior due to univesal definitions
  * Algebraic manipulation

The biggest of these is casting. So many times I would struggle to understand why my editor said my goal was `x ^ 2 = x ^ 2` and why `refl` wouldn't work. I eventually realized I could hover over elements and see their type and it would turn out that one `2` was a natural number and one `2` was a real number. Similarly, I often would have a function `f : ℝ → ℝ` and would, e.g., want to sum `f ↑i` for `i : ℕ`. This is _not_ the same thing as `(f ∘ ↑) i` where `↑ : ℕ → ℝ` and so there's a lot of gunk to get around this.

The unexpected behavior, honestly, isn't that unexpected, but `a - b` when `a` and `b` are natural numbers is generally a bad thing to write. In mathlib, if `b > a` then `a - b = 0`. This isn't wrong in any sense or bad, it's just very unexpected and hard for noobs to debug. My code, if you look, is filled with many lemmas named along the line of `blarg` to get around these facts.

This in turn exacerbates the difficulty of algebraic manipulation. The worst version of this occurs in [archive.lean](https://github.com/khwilson/squarefree_asymptotics/blob/main/src/archive.lean). Here I had a lemma which precisely computed the limit of a certain integral, and I needed to show it was less than the asymptotic value I actually wanted. You can see all the wonkiness just from the statement:

```lean
lemma extraordinarily_annoying
{b c : ℕ}
(hb : 200 ≤ b)
(hbc : sqrt b = c + 1)
:
- ↑c ^ (-(2 : ℝ) + 1) / (-(2 : ℝ) + 1) ≤ 2 * |(b : ℝ) ^ (2 : ℝ)⁻¹| / ↑b
```

I found myself many times saying to the computer "just multiply both sides by 2!" and then spending many minutes searching the docs for whatever lemma let me "just multiply both sides by 2," realizing that I needed to actually multiply by `↑(2 : ℕ)` in order to use that lemma, and then being very sad.

### Some suggestions

Of course, these are complaints. What about potential suggestions? First, while there are several tutorials and the documentation is extremely detailed, the documentation contains _very few examples_. This was exacerbated as this sort of asymptotic computation touches a lot of areas of mathematics. In each case, I had to relearn the conventions of that area of Lean.

This, of course, mimics real life, so it's not a big surprise! But it would be useful if the documentation said things like "here is an example of how to use these lemmas to prove a simple fact." For example, it took me quite a while to figure out what to do with statements around filters, e.g., what magical incantation lets me prove `set.Ioc (a : ℝ) ↑b =ᵐ[real.measure_space.volume] set.Ioo (a : ℝ) ↑b`?

As another example of where examples might help, I realized much too late that the `zify` technique exists. Specifically, I would often want to prove some equality that required manipulating both sides of an equation. The `ring` technique is great! But `ℕ` is not a ring and so it would often choke. But `zify, ring` would sometimes just work.

Now "produce more content" is great and all as a suggestion (it's the number one suggestion for new open source contributors for a reason), but what about code suggestions? Here I do think that some sort of notion of an "absorbing structure" that could capture things like multiple instances of "sufficiently large" would be very helpful. It may even be expressible in terms of raw filters, but I couldn't quite grok it.

Similarly, if there are further ways to turbocharge `ring` to be aware of the weirdness of the natural numbers specifically, it would be very helpful.

Finally, I would love to be able to say `14 = sqrt 200, eval` or some similar thing to capture the `#eval` macro _in a proof_. This may exist somewhere, but I couldn't find it.
