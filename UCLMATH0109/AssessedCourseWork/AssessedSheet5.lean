import Mathlib.Tactic
import Mathlib.Data.Real.Irrational

/-
# Assessed Sheet 5 covering material from 4A-C
-/

section groups

variable {G H : Type} [Group G] [Group H]

/-
Prove that the image of `f` is a subgroup of `H`
and the kernel is a subgroup of `G`.-/
--01
def Ker (φ : G →* H) : Subgroup G where
  carrier := {g : G | φ g = 1}
  mul_mem' :=
  by
    sorry
  one_mem' :=
  by
    sorry
  inv_mem' :=
  by
    sorry


#check Set.mem_singleton_iff
#check Function.Injective

--02
theorem injective_iff (φ : G →* H) :
    Function.Injective φ ↔ (Ker φ : Set G) = {1} :=
by
  sorry

end groups


/-
Prove that the Rationals form an additive subgroup of ℝ

You could start with:
`carrier := Set.range ((↑) : ℚ → ℝ)`
-/
--03
def Rat_AddSubgroup : AddSubgroup ℝ := sorry


/-
  # Defining functions using  if - then - else and choice

Mathematics (and computer science) is full of functions defined in terms
of `if-then-else` logic. For example, characteristic functions of sets.

The characteristic function of the irrationals:

 `χ_irrat : ℝ → ℝ`
 `χ_irrat(x) = 1 if x is irrational and 0 otherwise`

[Note : There is no algorithm for deciding whether `x : ℝ` is irrational so we need
to use Classical reasoning and mark the functions in this section as `noncomputable` since
we can't execute them (although we can and will reason about them, i.e. prove theorems).]
-/
open Classical
/-- The characteristic function of the irrationals -/
noncomputable
def χ_irrat : ℝ → ℝ := fun x => if (Irrational x) then 1 else 0

/- We can also use the slightly less readable (but more compact)
`ite` syntax -/
lemma χ_irrat_eq (x : ℝ): χ_irrat x  = ite (Irrational x) 1 0 :=
by
  rfl

/-
If we define a function using `if - then - else` it can  be useful to have lemmas
that allow us to rewrite the function in the two branches (true/false).

A helpful tactic for this is `split_ifs` which will split an `ite goal` into multiple
goals. (It can also be used in the local context as `split_ifs at h1` where `h1`
is an ite statement in the local context.)

If the `split_ifs` produces more than one goal you can give a name to the hypothesis
in each branch with `split_ifs with hx` or `split_ifs at h with hx`
-/

/-- If x is irrational then ...-/
lemma χ_irrat_of_irrat (hx : Irrational x) : χ_irrat x = 1:=
by
  rw [χ_irrat_eq] -- without this Lean can't see that there is an `ite` to split
  split_ifs; rfl

--04
/-- If x is not irrational then ...-/
lemma χ_irrat_of_not_irrat (hx : ¬Irrational x) : χ_irrat x = 0:=
by
  sorry

--05
lemma χ_irrat_one (h : χ_irrat x = 1) : Irrational x :=
by
  rw [χ_irrat_eq] at h
  split_ifs at h with hx
  · sorry
  · sorry


--06
lemma χ_irrat_sq_eq_one (h : (χ_irrat x)^2 = 1) : Irrational x:=
by
  sorry

/-
For the next result we need to understand exactly how `Irrational x` is defined in Lean -/
#print Irrational
/-
def Irrational : ℝ → Prop :=
fun x => ¬x ∈ Set.range Rat.cast

This means `Irrational x` ↔ `¬ ∃ (q : ℚ), (q : ℝ) = x`
i.e. iff there does not exist a rational y, which when coerced into a real equals x.
-/

--07
lemma χ_irrat_comp : χ_irrat (χ_irrat x) = 0 :=
by
  rw [χ_irrat_eq,χ_irrat_eq]
  -- We now have two nested if - then - else statements
  sorry


/-
# Dependent if - then - else using choice

We now want to define a function `irrat_mem` that maps any set S of reals to
an arbitrary irrational number in S (if one exists) and to 0 otherwise.

This will also be an `if then else` function, but it is a `dependent-if-then-else`
since the value it returns depends on the proof of the existence statement (in the true branch).

Given `h : ∃ (x : ℝ), x ∈ S ∧ Irrational x` we use the axiom of choice to choose an
arbitrary `x` with this property. This `x` is called `Exists.choose h` or `h.choose` in Lean.
-/
noncomputable -- Since there is no algorithm for checking if `h` below is true or false.
def irrat_mem : Set ℝ → ℝ := fun S =>
  if h : ∃ (x : ℝ), x ∈ S ∧ Irrational x then h.choose else 0

/- As before we give a simple definitional lemma for rewriting this definition.-/
lemma irrat_mem_eq (S : Set ℝ) :
(irrat_mem S) = if h : ∃ x, x ∈ S ∧ Irrational x then h.choose else 0 := rfl

 /-
 When reasoning about this function we will need to use `Exists.choose_spec h` or `h.choose_spec`
 where `h : ∃ x, x ∈ S ∧ Irrational x`

`h.choose_spec` is a proof that the element given by `h.choose` satisfies `x ∈ S ∧ Irrational x`
-/


--08
/-- The value returned by `irrat_mem` has the correct property (given the condition `h` is true)-/
lemma irrat_mem_spec (S : Set ℝ) (h : ∃ x, x ∈ S ∧ Irrational x) :
(irrat_mem S) ∈ S ∧ Irrational (irrat_mem S) :=
by
  rw [irrat_mem_eq] -- this unfolds the definition of `irrat_mem` as an `if then else` statement
  split_ifs         -- chooses the correct branch (since we have `h` in the local context)
  sorry

/-
When reasoning about a case where `h` is false we don't need to (indeed can't) use `h.choose_spec`
since we don't have a proof of `h`.
-/

--09
lemma irrat_mem_empty (S : Set ℝ) (h : S = ∅) : irrat_mem S = 0 :=
by
  rw [irrat_mem_eq]
  sorry



section subsequences
variable {x : ℕ → ℝ}
#check StrictMono -- Lean for strictly increasing function
-- To prove `f : ℕ → α` is StrictMono it is sufficient to check `∀ n, f n < f (n + 1)`
#check strictMono_nat_of_lt_succ

/--
If x: ℕ → ℝ is a real sequence that is unbounded above, then it contains a StrictMono
subsequence -/
lemma exists_strictMono_of_unbounded_above  (hb : ∀ b, ∃ m, b < x m ) :
    ∃ f : ℕ → ℕ,  StrictMono (x ∘ f) :=
by
-- We can construct `f` inductively:
  let f : ℕ → ℕ :=
  by
    intro n;
    induction n with
    | zero =>
      exact 0  -- f 0 = 0
    | succ _ ih =>
/-
Defining a function on ℕ inductively means that when we define `f (n + 1)`
we have `ih := f n` as our inductive hypothesis.
So `hb (x ih)` is the proposition that `∃ m, (x (f n)) < x m`
and hence we can define `f (n + 1) = m` where `m` is extracted using `choose`
-/
      exact (hb (x ih)).choose
-- Having defined f we can now prove that it has the required properties.
  have f_spec : ∀ n, x (f n ) < x (f (n + 1))
  · intro n; apply (hb (x (f n))).choose_spec
  use f
  apply strictMono_nat_of_lt_succ f_spec;


/-
One problem with this last result is that `x ∘ f` is not necessarily a proper subsequence of `x`
For this we would also need `f` to be strictly increasing (StrictMono f)

You will prove this stronger result below as `exists_proper_strictMono_of_unbounded_above`.

First we prove a simple lemma.
-/


--10
/-- If a sequence `xₙ` is unbounded above then its tail, `xₙ₊ₘ` is unbounded above for any m -/
lemma tail_unb_abv_of_unb_abv (hb : ∀ b, ∃ n, b < x n ) :
∀ m b, ∃ n, b < x (n + m) :=
by
  intro m
  sorry


#check Function.comp_apply
#check strictMono_nat_of_lt_succ
/-
Now we prove that any real sequence that is unbounded above contains a proper
strictly increasing subsequence. (The lemma `tail_unb_abv_of_unb_abv` may be useful here.)
Make sure you understand the proof of `exists_strictMono_of_unbounded_above` before starting
this question.
-/

--11
theorem exists_proper_strictMono_of_unbounded_above (hb : ∀ b, ∃ n, b < x n ) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ StrictMono (x ∘ f) :=
by
  sorry

end subsequences
