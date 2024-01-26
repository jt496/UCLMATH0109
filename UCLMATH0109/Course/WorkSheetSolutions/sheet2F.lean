import UCLMATH0109.Course._2_foundations.F_nat

namespace N


theorem one_pow (n : N) : 1 ^ n = 1:=
by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ,one_mul,ih]


theorem pow_add (a b c: N) : a ^ (b + c) = a ^ b * a ^ c :=
by
  induction c with
  | zero =>
    rw [zero_eq,add_zero,pow_zero,mul_one]
  | succ c ih =>
    rw [add_succ,pow_succ,ih,pow_succ,←mul_assoc,mul_comm a,←mul_assoc]

theorem pow_mul (a b c : N) : a ^ (b * c) = (a ^ b) ^ c :=
by
  induction c with
  | zero => rfl
  | succ n ih =>
    rw [mul_succ,pow_add,ih,pow_succ,mul_comm]

theorem two_eq_succ_one : 2 = succ 1 :=
by
  rfl

theorem two_mul (n : N) : 2 * n = n + n :=
by
  rw [two_eq_succ_one,succ_mul,one_mul]

theorem pow_two (n : N) : n ^ 2 = n * n:=
by
  rw [two_eq_succ_one,pow_succ,pow_one]

theorem add_sq (a b : N) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
by
  rw [pow_two,add_mul,mul_add,mul_add,pow_two,pow_two,two_mul,add_mul,mul_comm b a, add_assoc,add_assoc,add_assoc]

theorem pow_pow (a b c : N) : (a ^ b) ^ c = a ^(b * c) :=
by
  rw [pow_mul]
