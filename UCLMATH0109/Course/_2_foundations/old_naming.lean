import Mathlib.Tactic

variable (R : Type)
variable (x y z u v : R)
variable [CommRing R]

/- 

A commutative ring R is a set R with two binary operations: + and *

`add`ition, `mul`tiplication, `comm`utativity, `assoc`iativity,
`zero` and `one`. 

Lean's maths library `mathlib` follows very simple naming patterns that allow us to guess
the name of results we wish to use.

The purpose of this file is to introduce you to these naming conventions.

The only tactics you will need are `rw` and `simp_rw`, which we will use to rewrite identities.  

Remember that if we have an equality `h : a = b` then `rw [h]` will replace a by b 
while `rw [← h]` will replace b by a.  -/


/-- 0 is the additive right identity : x + 0 = x -/
lemma lem_1_1 : x + 0 = x :=
by
  rw [add_zero]



/-- 0 is the additive left identity : 0 + x = x -/
lemma lem_1_2 : 0 + x = x :=
by
  rw [zero_add]



/-- addition is commutative -/
lemma lem_1_3 : x + y = y + x :=
by
  rw [add_comm]



/-- addition is associative -/
lemma lem_1_4 : x + y + z = x + (y + z) :=
by
  rw [add_assoc]



/-- 1 is the multiplicative right identity : x*1 = x -/
lemma lem_1_5 : x*1 = x :=
by
  rw [mul_one]



/-- 1 is the multiplicative left identity : 1*x = x -/
lemma lem_1_6 : 1*x = x :=
by
  sorry



/-- multiplication is commutative -/
lemma lem_1_7 : x*y = y*x :=
by
  sorry



/-- multiplication is associative -/
lemma lem_1_8 : x*y*z = x*(y*z) :=
by
  sorry



/-- multiplication is left distributive over addtion-/
lemma lem_1_9 : x*(y + z) = x * y + x * z:=
by
  rw [mul_add] -- mul_add is shorter and possibly easier to remember than
  --rw [left_distrib] 


/-- multiplication is right distributive over addtion-/
lemma lem_1_10 : (x + y)*z = x*z+ y*z:=
by
  -- Hint: which operation comes first?
  sorry



/- Up to this point we have been able to use `rw` without trouble, 
  but when we have a goal such as
   `⊢ x + y + z = y + x + z`
if we do `rw add_comm`, Lean will produce the rather unhelpful new goal:
   `⊢ z + (x + y) = y + x + z`  

To understand why Lean does this we need to think about how Lean parses the expression

 `x + y + z = y + x + z`

 In Lean `+` associates left, in the sense that it is defined to be:
 `(x + y) + z = (y + x) + z`

When we ask Lean to `rw add_comm` it looks for the first `+`. 

It looks at the LHS of `=` first and then goes down expression looking for the first
occurence of `_ + _`. It finds on the LHS `(x+y)+z` and so swaps them to get `z+(x+y)`
                
                                   
      (x+y) + z       =        (y+x) + z           
      /        \               /        \ 
   x+y          z            y+x         z  
  /   \                     /   \        
 x     y                   y     x

Fortunately `add_comm` is the general statement :

add_comm : ∀ (a b : ?M_1), a + b = b + a

and we can specify `a` and `b`

If we want to tell Lean to apply it to `x + y` then we can specify this as
`rw [add_comm x y]`  -/


lemma lem_2_1 : x + y + z = y + x + z:=
by
  rw [add_comm x y]


/- 

In fact we could also use `rw [add_comm x]`. To see why this works recall that:

add_comm : ∀ (a b : ?M_1), a + b = b + a

So `add_comm` is a function taking two inputs, a and b and returning a proof that
  `a + b = b + a`.
Hence `add_comm x` is a function taking a single input `b` and returning 
a proof that `x + b = b + x`:

add_comm x : ∀ (b : R), x + b = b + x

If we do `rw add_comm x` then Lean looks for the first occurence of `x + _` and 
finds (x + y) in the LHS and rewrites this to `(y + x) + z` as required. -/

lemma lem_2_2 : x + y + z = y + x + z:=
by
  rw [add_comm x]


lemma lem_2_3 : (u + v) + (x + y) = (u + x) + (v + y):=
by
-- We can group successive rewrites
  rw [add_assoc, add_comm v, add_comm v, add_assoc u x, add_assoc x]






/- 
Other useful naming conventions that occur in results about rings include:
 `sub`traction eg x - y, 
 `neg`ation (additive inverses),eg -x 
 `pow`ers eg x^n, where n: ℕ
 `two` also makes sense in any ring (2 = 1 + 1)
 `self` if the same variable occurs twice in a result then it may
  use `self` to refer to this.
 `cancel` to refer to cancellation eg `a + b - b = a`  
 -/

lemma lem_3_1 : x - x = 0:=
by
  rw [sub_self]


lemma lem_3_2 : x + (-x) = 0:=
by
  rw [add_neg_self]


lemma lem_3_3 : x - (x + y) + y = 0:=
by
  rw [sub_add, add_sub_cancel, sub_self]


lemma lem_3_4: (x + y) + (y + x)  = 2*(x + y):=
by
  rw [add_comm y,  two_mul]



lemma lem_3_5 : x*x -2*x*y + y*y = (x-y)^2:=
by
  rw [sub_pow_two, pow_two, pow_two]


lemma lem_3_6 : x - y + z - u = x+ z - (y + u) :=
by
  rw [add_sub_add_comm, add_sub]


lemma lem_3_7 : (x-y+z)*(x-y) = x^2 -2*x*y + y ^2+x*z -z*y:=
by
  rw [add_mul,←pow_two,sub_pow_two,mul_sub,mul_comm _ z,add_sub]

