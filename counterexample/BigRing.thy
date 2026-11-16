theory BigRing
  imports Small_Range
begin

text \<open>The trivial square-zero extension of the reals by the real vector space of all
real functions: a commutative local ring with exactly one prime ideal and more than
continuum many elements.\<close>

datatype bigring = BR (re: real) (fn: "real \<Rightarrow> real")

instantiation bigring :: comm_ring_1
begin

definition zero_bigring :: bigring where "zero_bigring = BR 0 (\<lambda>_. 0)"
definition one_bigring :: bigring where "one_bigring = BR 1 (\<lambda>_. 0)"
definition plus_bigring :: "bigring \<Rightarrow> bigring \<Rightarrow> bigring" where
  "plus_bigring x y = BR (re x + re y) (\<lambda>t. fn x t + fn y t)"
definition uminus_bigring :: "bigring \<Rightarrow> bigring" where
  "uminus_bigring x = BR (- re x) (\<lambda>t. - fn x t)"
definition minus_bigring :: "bigring \<Rightarrow> bigring \<Rightarrow> bigring" where
  "minus_bigring x y = BR (re x - re y) (\<lambda>t. fn x t - fn y t)"
definition times_bigring :: "bigring \<Rightarrow> bigring \<Rightarrow> bigring" where
  "times_bigring x y = BR (re x * re y) (\<lambda>t. re x * fn y t + re y * fn x t)"

instance
proof
  fix a b c :: bigring
  show "a * b * c = a * (b * c)"
    by (simp add: times_bigring_def fun_eq_iff algebra_simps)
  show "a * b = b * a"
    by (simp add: times_bigring_def fun_eq_iff algebra_simps)
  show "1 * a = a"
    by (cases a) (simp add: times_bigring_def one_bigring_def)
  show "a + b + c = a + (b + c)"
    by (simp add: plus_bigring_def fun_eq_iff algebra_simps)
  show "a + b = b + a"
    by (simp add: plus_bigring_def fun_eq_iff algebra_simps)
  show "0 + a = a"
    by (cases a) (simp add: plus_bigring_def zero_bigring_def)
  show "- a + a = 0"
    by (simp add: plus_bigring_def uminus_bigring_def zero_bigring_def)
  show "a - b = a + - b"
    by (simp add: plus_bigring_def uminus_bigring_def minus_bigring_def)
  show "(a + b) * c = a * c + b * c"
    by (simp add: plus_bigring_def times_bigring_def fun_eq_iff algebra_simps)
  show "(0::bigring) \<noteq> 1"
    by (simp add: zero_bigring_def one_bigring_def)
qed

end

lemma re_simps [simp]:
  "re (0::bigring) = 0" "re (1::bigring) = 1"
  "re (x + y) = re x + re y" "re (x * y) = re x * re y" "re (- x) = - re x"
  by (simp_all add: zero_bigring_def one_bigring_def plus_bigring_def times_bigring_def
      uminus_bigring_def)

lemma bigring_unit:
  assumes "re x \<noteq> 0"
  shows "\<exists>y. x * y = 1 \<and> y * x = 1"
proof -
  define y where "y = BR (1 / re x) (\<lambda>t. - fn x t / (re x * re x))"
  have "x * y = 1"
    using assms by (simp add: y_def times_bigring_def one_bigring_def fun_eq_iff field_simps)
  then show ?thesis by (metis mult.commute)
qed

lemma bigring_nonunit: "x * y = (1::bigring) \<Longrightarrow> re x \<noteq> 0"
  by (metis re_simps(2,4) mult_zero_left zero_neq_one)

lemma bigring_square_zero: "re x = 0 \<Longrightarrow> x * x = (0::bigring)"
  by (simp add: times_bigring_def zero_bigring_def)

lemma bigring_not_csmall: "\<not> csmall (UNIV :: bigring set)"
proof
  assume "csmall (UNIV :: bigring set)"
  then obtain g :: "real \<Rightarrow> bigring" where g: "surj g"
    unfolding csmall_def using card_of_ordLeq2[of "UNIV :: bigring set" "UNIV :: real set"] by auto
  define d :: bigring where "d = BR 0 (\<lambda>x. fn (g x) x + 1)"
  obtain x where dx: "d = g x" using surjD[OF g, of d] by blast
  have "fn d x = fn (g x) x + 1" by (simp add: d_def)
  then show False using dx by simp
qed

end
