theory Small_Range
  imports Complex_Main "HOL-Library.Function_Algebras"
begin

notation plus (infixl "+" 65)
notation minus (infixl "-" 65)
unbundle uminus_syntax
unbundle cardinal_syntax

text \<open>A set is small when its cardinality is at most the continuum.\<close>
definition csmall :: "'a set \<Rightarrow> bool" where
  "csmall A \<longleftrightarrow> |A| \<le>o |(UNIV :: real set)|"

lemma csmall_mono:
  "A \<subseteq> B \<Longrightarrow> csmall B \<Longrightarrow> csmall A"
  unfolding csmall_def using card_of_mono1 ordLeq_transitive by blast

lemma csmall_image:
  "csmall A \<Longrightarrow> csmall (f ` A)"
  unfolding csmall_def using card_of_image ordLeq_transitive by blast

lemma csmall_singleton [simp]: "csmall {x}"
  unfolding csmall_def by (simp add: card_of_singl_ordLeq)

lemma csmall_empty [simp]: "csmall {}"
  using csmall_mono[of "{}" "{undefined}"] by simp

lemma csmall_real [simp]: "csmall (I :: real set)"
  unfolding csmall_def by (rule card_of_mono1) simp

lemma csmall_Times:
  assumes "csmall A" "csmall B"
  shows "csmall (A \<times> B)"
  unfolding csmall_def
proof (rule card_of_Times_ordLeq_infinite_Field)
  show "infinite (Field (BNF_Cardinal_Order_Relation.card_of (UNIV :: real set)))"
    by (simp add: Field_card_of infinite_UNIV_char_0)
  show "|A| \<le>o |(UNIV :: real set)|" using assms(1) unfolding csmall_def .
  show "|B| \<le>o |(UNIV :: real set)|" using assms(2) unfolding csmall_def .
  show "Card_order (BNF_Cardinal_Order_Relation.card_of (UNIV :: real set))" by (rule card_of_Card_order)
qed

lemma csmall_UNION:
  fixes I :: "real set"
  assumes "\<And>i. i \<in> I \<Longrightarrow> csmall (A i)"
  shows "csmall (\<Union>i\<in>I. A i)"
  unfolding csmall_def
proof (rule card_of_UNION_ordLeq_infinite)
  show "infinite (UNIV :: real set)" by (rule infinite_UNIV_char_0)
  show "|I| \<le>o |(UNIV :: real set)|" by (rule card_of_mono1) simp
  show "\<forall>i\<in>I. |A i| \<le>o |(UNIV :: real set)|"
    using assms unfolding csmall_def by blast
qed

lemma csmall_binary:
  assumes "csmall (f ` U)" "csmall (g ` U)"
  shows "csmall ((\<lambda>x. op (f x) (g x)) ` U)"
proof -
  have "(\<lambda>x. op (f x) (g x)) ` U \<subseteq> (\<lambda>(a,b). op a b) ` (f ` U \<times> g ` U)"
    by auto
  moreover have "csmall ((\<lambda>(a,b). op a b) ` (f ` U \<times> g ` U))"
    by (rule csmall_image[OF csmall_Times[OF assms]])
  ultimately show ?thesis by (rule csmall_mono)
qed

text \<open>Canonical total-function representatives, with undefined off the domain.\<close>
definition cut :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "cut f U x = (if x\<in>U then f x else undefined)"
lemma cut_apply [simp]: "x\<in>U \<Longrightarrow> cut f U x = f x"
  by (simp add: cut_def)
lemma cut_outside [simp]: "x\<notin>U \<Longrightarrow> cut f U x = undefined"
  by (simp add: cut_def)
lemma cut_image [simp]: "cut f U ` U = f ` U"
  by (auto simp: cut_def)

definition sec :: "'x set \<Rightarrow> ('x \<Rightarrow> 'r) set" where
  "sec U = {f. (\<forall>x. x\<notin>U \<longrightarrow> f x = undefined) \<and> csmall (f ` U)}"

definition sadd :: "'x set \<Rightarrow> ('x \<Rightarrow> 'r::ring_1) \<Rightarrow> ('x \<Rightarrow> 'r) \<Rightarrow> ('x \<Rightarrow> 'r)" where
  "sadd U f g = cut (\<lambda>x. f x + g x) U"
definition smul :: "'x set \<Rightarrow> ('x \<Rightarrow> 'r::ring_1) \<Rightarrow> ('x \<Rightarrow> 'r) \<Rightarrow> ('x \<Rightarrow> 'r)" where
  "smul U f g = cut (\<lambda>x. f x * g x) U"
definition sneg :: "'x set \<Rightarrow> ('x \<Rightarrow> 'r::ring_1) \<Rightarrow> ('x \<Rightarrow> 'r)" where
  "sneg U f = cut (\<lambda>x. - f x) U"
definition szero :: "'x set \<Rightarrow> ('x \<Rightarrow> 'r::ring_1)" where
  "szero U = cut (\<lambda>x. 0) U"
definition sone :: "'x set \<Rightarrow> ('x \<Rightarrow> 'r::ring_1)" where
  "sone U = cut (\<lambda>x. 1) U"
definition srho :: "'x set \<Rightarrow> 'x set \<Rightarrow> ('x \<Rightarrow> 'r) \<Rightarrow> ('x \<Rightarrow> 'r)" where
  "srho U V = cut (\<lambda>f. cut f V) (sec U)"

lemma sec_ext:
  "f \<in> sec U \<Longrightarrow> (\<forall>x. x\<notin>U \<longrightarrow> f x = undefined)"
  by (simp add: sec_def)
lemma sec_small:
  "f \<in> sec U \<Longrightarrow> csmall (f ` U)"
  by (simp add: sec_def)
lemma sec_outside:
  "f \<in> sec U \<Longrightarrow> x \<notin> U \<Longrightarrow> f x = undefined"
  by (simp add: sec_def)
lemma sec_cut:
  assumes "f \<in> sec U" "V \<subseteq> U"
  shows "cut f V \<in> sec V"
proof -
  have "csmall (f ` V)"
    using assms sec_small by (meson csmall_mono image_mono)
  then show ?thesis by (auto simp: sec_def cut_def)
qed
lemma sec_constant:
  "cut (\<lambda>x. a) U \<in> sec U"
  unfolding sec_def by (auto simp: cut_def intro: csmall_mono[of _ "{a}"])
lemma sec_szero [simp]: "szero U \<in> sec U"
  unfolding szero_def by (rule sec_constant)
lemma sec_sone [simp]: "sone U \<in> sec U"
  unfolding sone_def by (rule sec_constant)
lemma sec_sadd [simp]:
  "f \<in> sec U \<Longrightarrow> g \<in> sec U \<Longrightarrow> sadd U f g \<in> sec U"
  unfolding sadd_def sec_def using csmall_binary[of f U g "(+)" ] by (auto simp: cut_def)
lemma sec_smul [simp]:
  "f \<in> sec U \<Longrightarrow> g \<in> sec U \<Longrightarrow> smul U f g \<in> sec U"
  unfolding smul_def sec_def using csmall_binary[of f U g "(*)" ] by (auto simp: cut_def)
lemma sec_sneg [simp]:
  "f \<in> sec U \<Longrightarrow> sneg U f \<in> sec U"
proof -
  assume "f \<in> sec U"
  then have "csmall ((\<lambda>x. - f x) ` U)"
    using csmall_image[OF sec_small[of f U], of uminus] by (simp add: image_image)
  then show ?thesis by (auto simp: sneg_def sec_def cut_def)
qed

lemma srho_apply [simp]:
  "f \<in> sec U \<Longrightarrow> srho U V f = cut f V"
  by (simp add: srho_def)



lemma cut_sec [simp]: "f\<in>sec U \<Longrightarrow> cut f U = f"
  by (auto simp: sec_def cut_def fun_eq_iff)

end
