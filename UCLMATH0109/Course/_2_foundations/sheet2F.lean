import UCLMATH0109.Course._2_foundations.F_nat

namespace N


theorem one_pow (n : N) : 1 ^ n = 1:=
by
  sorry

theorem pow_add (a b c: N) : a ^ (b + c) = a ^ b * a ^ c :=
by
  sorry

theorem pow_mul (a b c : N) : a ^ (b * c) = (a ^ b) ^ c :=
by
  sorry

theorem two_eq_succ_one : 2 = succ 1 :=
by
  sorry

theorem two_mul (n : N) : 2 * n = n + n :=
by
  sorry

theorem pow_two (n : N) : n ^ 2 = n * n:=
by
  sorry

theorem add_sq (a b : N) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
by
  sorry

theorem pow_pow (a b c : N) : (a ^ b) ^ c = a ^(b * c) :=
by
  sorry
