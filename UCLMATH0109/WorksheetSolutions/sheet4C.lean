import Mathlib.Tactic
namespace Sheet4Csol
variable {G H K : Type} [Group G] [Group H] [Group K]


/-
The first few exercises can be done by `exact?`.
-/

--01
example : (1 : G)⁻¹ = 1 :=by
  exact inv_one

--02
example (x y : G) : x^2 * x⁻¹ * y = x * y :=by
  group


--03
example (x y : G) (h : y = x^2 * y⁻¹) : x^2 = y^2 :=by
  rw [← mul_left_inj (y⁻¹),← h, pow_two, mul_inv_cancel_right]

--04
example (x y : G) (h : x * y = y * x) : (x * y)^2 = x^2 * y^2 :=by
  have : (x*y)^2 = x*(y*x)*y
  · rw [pow_two]
    group
  rw [this,← h, ←mul_assoc,←pow_two,mul_assoc, ←pow_two]


--05
/-
Show that if `φ : G →* H` and `ψ : H →* K` are homomorphisms
then their composition is also a homomorphism:
-/
example (φ : G →* H) (ψ : H →* K) : G →* K where
  toFun := ψ ∘ φ
  map_one' :=by
    dsimp; rw [φ.map_one,ψ.map_one]
  map_mul' :=by
    intro x y
    dsimp;  rw [φ.map_mul,ψ.map_mul]

--06
/-
Show that if `A` is an Abelian group then
the map `a ↦ a ^ 2` is a group homomorphism from `A` to `A`.
-/
example (A : Type) [CommGroup A] : A →* A where
  toFun     := fun a ↦ a ^ 2
  map_one'  := by
    dsimp; rw [pow_two,one_mul]
  map_mul'  := by
    intro x y
    dsimp
    rw [pow_two,mul_assoc,mul_comm x y,←mul_assoc y,←pow_two,mul_comm _ x,← mul_assoc,
        pow_two x]

--07
/-
Show that if `A` is abelian, then the product of
two homomorphisms `G →* A` is a homomorphism.
-/
example {A : Type} [CommGroup A] (φ ψ : G →* A) : G →* A where
  toFun     := fun g ↦ (φ g) * (ψ g)
  map_one'  :=by
    dsimp
    rw [φ.map_one,ψ.map_one,one_mul]
  map_mul'  :=by
    intro x y
    dsimp
    rw [φ.map_mul,ψ.map_mul,mul_comm (ψ x),←mul_assoc,mul_comm,
      ←mul_assoc,←mul_assoc,←mul_assoc, mul_comm (ψ x)]

--08
/-
Show that if `A` is abelian and `φ : G →* A` is a homomorphism,
then the map `g ↦ (φ g)⁻¹` is also a homomorphism.
-/
def homomorphism_inv {A : Type} [CommGroup A] (φ : G →* A) : G →* A where
  toFun     := fun g ↦ (φ g)⁻¹
  map_one'  :=by
    dsimp
    rw [φ.map_one]
    exact inv_one
  map_mul'  :=by
    intro x y
    dsimp; rw [φ.map_mul]
    rw [mul_inv]

--09
/-
Prove that the set of all elements of `G` is a subgroup of `G`.
(Note that the set of all elements of a given `Type` is called `Set.univ`.)
-/
example : Subgroup G where
  carrier := Set.univ
  mul_mem' :=by
    intro _ _  _ _ ; trivial
  one_mem' :=by trivial
  inv_mem' :=by
    intro _ _ ; trivial

--10
/-
Prove that the image of `f` is a subgroup of `H`
and the kernel is a subgroup of `G`.
-/
def Ker (φ : G →* H) : Subgroup G where
  carrier := {g : G | φ g = 1}
  mul_mem' :=by
    intro a b ha hb
    have : φ (a*b) = 1
    · rw [φ.map_mul,ha,hb,one_mul]
    exact this
  one_mem' :=by
    apply φ.map_one
  inv_mem' :=by
    intro x hx
    have : φ (x⁻¹) = 1
    · have : φ (x * x⁻¹) = 1
      · rw [mul_inv_self,φ.map_one]
      rw [← this,φ.map_mul,hx,one_mul]
    exact this

/-
# The last few questions are more challenging.
-/

--11
/-
Have a think about this one. Of course you could prove it by a very
long sequence of rewrites. However it is easier to prove a more general
statement by induction.
Alternatively you could try `apply?`, and try to find the most relevant
result.
-/
example (x y : G) (h : x * y = y * x) : x^45 * y^4 = y^4 * x^45 :=by
  refine Eq.symm (Commute.eq ?h) -- found via `apply?`
  exact Commute.pow_pow (id (Eq.symm h)) 4 45 -- also found via `apply?`


--12
/-
Suppose `G` is a group in which `z ^ 2 = 1` for every element `z`.
Prove that `G` is abelian.
-/
example (h : ∀ z : G , z ^ 2 = 1) :
    ∀ x y : G, x * y = y * x :=by
  -- first prove that `z⁻¹ = z` for all elements `z` in the group.
  have hz: ∀z : G, z = z⁻¹
  · intro z
    rw [←mul_one (z⁻¹),←h z, pow_two]
    exact eq_inv_mul_of_mul_eq rfl -- found by apply?
  -- Using this formula in the case `z = y * x`,
  -- we get `(y * x)⁻¹ = y * x`.
  -- Next, simplify the left hand side to get `x⁻¹ * y⁻¹ = y * x`.
  -- After that, rewrite `x⁻¹` and `y⁻¹` as `x` and `y`.
  intro x y
  rw [hz (x*y),mul_inv_rev,← hz,← hz]


--13
/-
We defined the kernel of a homomorphism in question 10.
Prove that a homomorphism `φ` is injective iff its kernel is `{1}`.

In this last example, you might want to use `Set.mem_singleton_iff`.
You might also want to look up `Function.Injective`.
-/
theorem injective_iff (φ : G →* H) :
    Function.Injective φ ↔ (Ker φ : Set G) = {1} :=by
  constructor
  · intro hinj
    ext x; rw [Set.mem_singleton_iff]
    constructor
    · intro hf
      apply hinj
      rwa [φ.map_one]
    · intro hone
      rw [hone]
      apply one_mem
  · intro h
    intro x y hxy
    have : φ (x*y⁻¹) = 1
    · rwa [φ.map_mul,φ.map_inv,mul_inv_eq_one]
    rw [←one_mem (Ker φ)] at this
    have : x*y⁻¹ = 1
    · have : x*y⁻¹ ∈ (Ker φ : Set G)
      · rwa [φ.map_one] at this
      rwa [h] at this
    rwa [mul_inv_eq_one] at this


--14
example (x y : G) (h : x * y = y^2 * x) (n : ℕ) : x^n * y = y ^ (2^n) * x^n :=by
  have : ∀ k : ℕ, x* y^k = y^(2*k) * x
  · intro k
    induction k with
    | zero =>
      rw [pow_zero,one_mul,mul_one]
    | succ n ih =>
      rw [pow_add,←mul_assoc,ih,pow_one,mul_assoc,h,←mul_assoc,←pow_add,
        two_mul,two_mul,← add_assoc,Nat.succ_add]
  induction n with
  | zero =>
    rw [pow_zero,one_mul,pow_zero,mul_one,pow_one]
  | succ n ih =>
    rw [add_comm,pow_add,mul_assoc,ih,pow_one,← mul_assoc,this,mul_assoc]
    congr
    rw [pow_add,pow_one]

--15
example {x y : G} (h : x * y = y⁻¹ * x) : x ^ (2 * n) * y = y * x^(2 * n) :=by
  have h1 : y*x*y = x
  · rw [mul_assoc,h,mul_inv_cancel_left]
  have h2 : x^2*y = y*x^2
  · nth_rw 1 [← h1, pow_two]
    rw [mul_assoc y x y]
    nth_rw 2 [h]
    rw [←mul_assoc y (y⁻¹),mul_right_inv,one_mul,mul_assoc]
    nth_rw 2 [h]
    rw [← mul_assoc,←mul_assoc,mul_assoc (y*x),mul_right_inv,mul_one,pow_two,mul_assoc]
  induction n with
  | zero =>
    rw [pow_zero,one_mul,mul_one]
  | succ n ih =>
    have : 2*n.succ = 2 + 2*n
    · rw [Nat.mul_succ,add_comm]
    rw [this,pow_add,mul_assoc,ih,←mul_assoc,h2,mul_assoc]

end Sheet4Csol
