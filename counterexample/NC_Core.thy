theory NC_Core
  imports Small_Range
begin

section \<open>A noncommutative ring with a homomorphism onto the reals\<close>

text \<open>The real algebra with basis 1, x, y, xy and relations xx = yy = yx = 0.
The element \<open>NC a b c d\<close> stands for a + b x + c y + d xy.\<close>

datatype nc = NC (n1: real) (n2: real) (n3: real) (n4: real)

instantiation nc :: ring_1
begin

definition zero_nc :: nc where "zero_nc = NC 0 0 0 0"
definition one_nc :: nc where "one_nc = NC 1 0 0 0"
definition plus_nc :: "nc \<Rightarrow> nc \<Rightarrow> nc" where
  "plus_nc p q = NC (n1 p + n1 q) (n2 p + n2 q) (n3 p + n3 q) (n4 p + n4 q)"
definition uminus_nc :: "nc \<Rightarrow> nc" where
  "uminus_nc p = NC (- n1 p) (- n2 p) (- n3 p) (- n4 p)"
definition minus_nc :: "nc \<Rightarrow> nc \<Rightarrow> nc" where
  "minus_nc p q = NC (n1 p - n1 q) (n2 p - n2 q) (n3 p - n3 q) (n4 p - n4 q)"
definition times_nc :: "nc \<Rightarrow> nc \<Rightarrow> nc" where
  "times_nc p q = NC (n1 p * n1 q) (n1 p * n2 q + n2 p * n1 q) (n1 p * n3 q + n3 p * n1 q)
     (n1 p * n4 q + n4 p * n1 q + n2 p * n3 q)"

instance
proof
  fix a b c :: nc
  show "a + b + c = a + (b + c)" by (rule nc.expand) (simp add: plus_nc_def)
  show "a + b = b + a" by (rule nc.expand) (simp add: plus_nc_def)
  show "0 + a = a" by (rule nc.expand) (simp add: plus_nc_def zero_nc_def)
  show "- a + a = 0" by (rule nc.expand) (simp add: plus_nc_def zero_nc_def uminus_nc_def)
  show "a - b = a + - b" by (rule nc.expand) (simp add: plus_nc_def minus_nc_def uminus_nc_def)
  show "a * b * c = a * (b * c)" by (rule nc.expand) (simp add: times_nc_def algebra_simps)
  show "1 * a = a" by (rule nc.expand) (simp add: times_nc_def one_nc_def)
  show "a * 1 = a" by (rule nc.expand) (simp add: times_nc_def one_nc_def)
  show "(a + b) * c = a * c + b * c"
    by (rule nc.expand) (simp add: times_nc_def plus_nc_def algebra_simps)
  show "a * (b + c) = a * b + a * c"
    by (rule nc.expand) (simp add: times_nc_def plus_nc_def algebra_simps)
  show "(0::nc) \<noteq> 1" by (simp add: zero_nc_def one_nc_def)
qed

end

lemma n1_simps [simp]:
  "n1 (p + q) = n1 p + n1 q" "n1 (p * q) = n1 p * n1 q" "n1 (- p) = - n1 p"
  "n1 (0::nc) = 0" "n1 (1::nc) = 1"
  by (simp_all add: plus_nc_def times_nc_def uminus_nc_def zero_nc_def one_nc_def)

text \<open>The two generators do not commute.\<close>
lemma nc_noncommutative: "NC 0 1 0 0 * NC 0 0 1 0 \<noteq> NC 0 0 1 0 * NC 0 1 0 0"
  by (simp add: times_nc_def)

section \<open>Smallness\<close>

lemma csmall_Un:
  assumes "csmall A" "csmall B"
  shows "csmall (A \<union> B)"
proof -
  have "A \<union> B = (\<Union>i\<in>{0, 1::real}. if i = 0 then A else B)" by auto
  moreover have "csmall (\<Union>i\<in>{0, 1::real}. if i = 0 then A else B)"
    by (rule csmall_UNION) (use assms in auto)
  ultimately show ?thesis by simp
qed

section \<open>Functions modulo small sets\<close>

text \<open>Two \<open>nc\<close>-valued functions on \<open>U\<close> are identified when they have the same real part
everywhere on \<open>U\<close> and differ at no more than continuum many points of \<open>U\<close>.\<close>

definition nrel :: "'x set \<Rightarrow> ('x \<Rightarrow> nc) \<Rightarrow> ('x \<Rightarrow> nc) \<Rightarrow> bool" where
  "nrel U g h \<longleftrightarrow> (\<forall>x\<in>U. n1 (g x) = n1 (h x)) \<and> csmall {x\<in>U. g x \<noteq> h x}"

lemma nrel_refl [simp]: "nrel U g g"
  by (simp add: nrel_def)

lemma nrel_sym: "nrel U g h \<Longrightarrow> nrel U h g"
  unfolding nrel_def by (auto elim: csmall_mono[rotated])

lemma nrel_trans:
  assumes "nrel U g h" "nrel U h k"
  shows "nrel U g k"
proof -
  have "{x\<in>U. g x \<noteq> k x} \<subseteq> {x\<in>U. g x \<noteq> h x} \<union> {x\<in>U. h x \<noteq> k x}" by auto
  moreover have "csmall ({x\<in>U. g x \<noteq> h x} \<union> {x\<in>U. h x \<noteq> k x})"
    using assms by (intro csmall_Un) (auto simp: nrel_def)
  ultimately have "csmall {x\<in>U. g x \<noteq> k x}" by (rule csmall_mono)
  then show ?thesis using assms by (auto simp: nrel_def)
qed

lemma nrel_mono:
  assumes "nrel U g h" "V \<subseteq> U"
  shows "nrel V g h"
proof -
  have "{x\<in>V. g x \<noteq> h x} \<subseteq> {x\<in>U. g x \<noteq> h x}" using assms(2) by auto
  then have "csmall {x\<in>V. g x \<noteq> h x}"
    by (rule csmall_mono) (use assms(1) in \<open>simp add: nrel_def\<close>)
  then show ?thesis using assms by (auto simp: nrel_def)
qed

lemma nrel_cut [simp]: "nrel U (cut g U) g"
  unfolding nrel_def
proof
  show "\<forall>x\<in>U. n1 (cut g U x) = n1 (g x)" by simp
  have "{x\<in>U. cut g U x \<noteq> g x} = {}" by auto
  then show "csmall {x\<in>U. cut g U x \<noteq> g x}" by (simp only: csmall_empty)
qed

lemma nrel_binary:
  assumes "nrel U g g'" "nrel U h h'"
    and op: "\<And>p q p' q'. n1 p = n1 p' \<Longrightarrow> n1 q = n1 q' \<Longrightarrow> n1 (op p q) = n1 (op p' q')"
  shows "nrel U (\<lambda>x. op (g x) (h x)) (\<lambda>x. op (g' x) (h' x))"
proof -
  have "{x\<in>U. op (g x) (h x) \<noteq> op (g' x) (h' x)} \<subseteq> {x\<in>U. g x \<noteq> g' x} \<union> {x\<in>U. h x \<noteq> h' x}"
    by auto
  moreover have "csmall ({x\<in>U. g x \<noteq> g' x} \<union> {x\<in>U. h x \<noteq> h' x})"
    using assms(1,2) by (intro csmall_Un) (auto simp: nrel_def)
  ultimately have small: "csmall {x\<in>U. op (g x) (h x) \<noteq> op (g' x) (h' x)}"
    by (rule csmall_mono)
  have "n1 (op (g x) (h x)) = n1 (op (g' x) (h' x))" if "x \<in> U" for x
    by (rule op) (use assms(1,2) that in \<open>simp_all add: nrel_def\<close>)
  then show ?thesis using small by (simp add: nrel_def)
qed

lemma nrel_add:
  "nrel U g g' \<Longrightarrow> nrel U h h' \<Longrightarrow> nrel U (\<lambda>x. g x + h x) (\<lambda>x. g' x + h' x)"
  by (rule nrel_binary) auto

lemma nrel_mul:
  "nrel U g g' \<Longrightarrow> nrel U h h' \<Longrightarrow> nrel U (\<lambda>x. g x * h x) (\<lambda>x. g' x * h' x)"
  by (rule nrel_binary) auto

lemma nrel_neg:
  assumes "nrel U g g'"
  shows "nrel U (\<lambda>x. - g x) (\<lambda>x. - g' x)"
proof -
  have "{x\<in>U. - g x \<noteq> - g' x} \<subseteq> {x\<in>U. g x \<noteq> g' x}" by auto
  then have "csmall {x\<in>U. - g x \<noteq> - g' x}"
    by (rule csmall_mono) (use assms in \<open>simp add: nrel_def\<close>)
  then show ?thesis using assms by (auto simp: nrel_def)
qed

text \<open>Equivalence classes consist of canonical representatives, equal to \<open>undefined\<close> off \<open>U\<close>.\<close>

definition ncls :: "'x set \<Rightarrow> ('x \<Rightarrow> nc) \<Rightarrow> ('x \<Rightarrow> nc) set" where
  "ncls U g = {h. (\<forall>x. x \<notin> U \<longrightarrow> h x = undefined) \<and> nrel U g h}"

definition nsec :: "'x set \<Rightarrow> ('x \<Rightarrow> nc) set set" where
  "nsec U = range (ncls U)"

definition nrep :: "('x \<Rightarrow> nc) set \<Rightarrow> ('x \<Rightarrow> nc)" where
  "nrep A = (SOME h. h \<in> A)"

lemma cut_in_ncls: "cut g U \<in> ncls U g"
  by (simp add: ncls_def nrel_sym)

lemma ncls_eq_iff: "ncls U g = ncls U h \<longleftrightarrow> nrel U g h"
proof
  assume "ncls U g = ncls U h"
  then have "cut h U \<in> ncls U g" using cut_in_ncls[of h U] by simp
  then have "nrel U g (cut h U)" by (simp add: ncls_def)
  then show "nrel U g h" using nrel_cut nrel_trans by blast
next
  assume r: "nrel U g h"
  show "ncls U g = ncls U h"
    unfolding ncls_def using r nrel_sym nrel_trans by blast
qed

lemma nrep_in: "nrep (ncls U g) \<in> ncls U g"
  unfolding nrep_def by (rule someI[of _ "cut g U"]) (rule cut_in_ncls)

lemma nrel_nrep: "nrel U g (nrep (ncls U g))"
  using nrep_in[of U g] by (simp add: ncls_def)

lemma ncls_nrep [simp]: "ncls U (nrep (ncls U g)) = ncls U g"
  using nrel_nrep[of U g] ncls_eq_iff nrel_sym by blast

lemma ncls_in_nsec [simp]: "ncls U g \<in> nsec U"
  by (simp add: nsec_def)

lemma nsecE:
  assumes "A \<in> nsec U"
  obtains g where "A = ncls U g"
  using assms by (auto simp: nsec_def)

lemma nsec_empty: "nsec {} = {{\<lambda>x. undefined}}"
proof -
  have "ncls {} g = {\<lambda>x. undefined}" for g :: "'a \<Rightarrow> nc"
    by (auto simp: ncls_def nrel_def)
  then show ?thesis by (auto simp: nsec_def)
qed

section \<open>The presheaf operations\<close>

definition nadd :: "'x set \<Rightarrow> ('x \<Rightarrow> nc) set \<Rightarrow> ('x \<Rightarrow> nc) set \<Rightarrow> ('x \<Rightarrow> nc) set" where
  "nadd U A B = ncls U (\<lambda>x. nrep A x + nrep B x)"
definition nmul :: "'x set \<Rightarrow> ('x \<Rightarrow> nc) set \<Rightarrow> ('x \<Rightarrow> nc) set \<Rightarrow> ('x \<Rightarrow> nc) set" where
  "nmul U A B = ncls U (\<lambda>x. nrep A x * nrep B x)"
definition nneg :: "'x set \<Rightarrow> ('x \<Rightarrow> nc) set \<Rightarrow> ('x \<Rightarrow> nc) set" where
  "nneg U A = ncls U (\<lambda>x. - nrep A x)"
definition nzero :: "'x set \<Rightarrow> ('x \<Rightarrow> nc) set" where
  "nzero U = ncls U (\<lambda>x. 0)"
definition nunit :: "'x set \<Rightarrow> ('x \<Rightarrow> nc) set" where
  "nunit U = ncls U (\<lambda>x. 1)"
definition nrho :: "'x set \<Rightarrow> 'x set \<Rightarrow> ('x \<Rightarrow> nc) set \<Rightarrow> ('x \<Rightarrow> nc) set" where
  "nrho U V = cut (\<lambda>A. ncls V (nrep A)) (nsec U)"

lemma nadd_ncls [simp]: "nadd U (ncls U g) (ncls U h) = ncls U (\<lambda>x. g x + h x)"
  unfolding nadd_def ncls_eq_iff by (intro nrel_add nrel_sym[OF nrel_nrep])

lemma nmul_ncls [simp]: "nmul U (ncls U g) (ncls U h) = ncls U (\<lambda>x. g x * h x)"
  unfolding nmul_def ncls_eq_iff by (intro nrel_mul nrel_sym[OF nrel_nrep])

lemma nneg_ncls [simp]: "nneg U (ncls U g) = ncls U (\<lambda>x. - g x)"
  unfolding nneg_def ncls_eq_iff by (intro nrel_neg nrel_sym[OF nrel_nrep])

lemma nrho_ncls [simp]:
  assumes "V \<subseteq> U"
  shows "nrho U V (ncls U g) = ncls V g"
proof -
  have "nrel V (nrep (ncls U g)) g"
    using nrel_mono[OF nrel_sym[OF nrel_nrep] assms] .
  then show ?thesis by (simp add: nrho_def ncls_eq_iff)
qed

lemma nrho_outside: "A \<notin> nsec U \<Longrightarrow> nrho U V A = undefined"
  by (simp add: nrho_def)

lemma nrho_closed: "A \<in> nsec U \<Longrightarrow> nrho U V A \<in> nsec V"
  by (simp add: nrho_def)

subsection \<open>Ring laws\<close>

lemma nadd_closed: "A \<in> nsec U \<Longrightarrow> B \<in> nsec U \<Longrightarrow> nadd U A B \<in> nsec U"
  by (simp add: nadd_def)
lemma nmul_closed: "A \<in> nsec U \<Longrightarrow> B \<in> nsec U \<Longrightarrow> nmul U A B \<in> nsec U"
  by (simp add: nmul_def)
lemma nneg_closed: "A \<in> nsec U \<Longrightarrow> nneg U A \<in> nsec U"
  by (simp add: nneg_def)
lemma nzero_closed: "nzero U \<in> nsec U"
  by (simp add: nzero_def)
lemma nunit_closed: "nunit U \<in> nsec U"
  by (simp add: nunit_def)

lemma nadd_assoc:
  "A \<in> nsec U \<Longrightarrow> B \<in> nsec U \<Longrightarrow> C \<in> nsec U \<Longrightarrow> nadd U (nadd U A B) C = nadd U A (nadd U B C)"
  by (elim nsecE) (simp add: add.assoc)
lemma nadd_comm: "A \<in> nsec U \<Longrightarrow> B \<in> nsec U \<Longrightarrow> nadd U A B = nadd U B A"
  by (elim nsecE) (simp add: add.commute)
lemma nadd_zero_left: "A \<in> nsec U \<Longrightarrow> nadd U (nzero U) A = A"
  by (elim nsecE) (simp add: nzero_def)
lemma nadd_zero_right: "A \<in> nsec U \<Longrightarrow> nadd U A (nzero U) = A"
  by (elim nsecE) (simp add: nzero_def)
lemma nadd_neg_right: "A \<in> nsec U \<Longrightarrow> nadd U A (nneg U A) = nzero U"
  by (elim nsecE) (simp add: nzero_def)
lemma nadd_neg_left: "A \<in> nsec U \<Longrightarrow> nadd U (nneg U A) A = nzero U"
  by (elim nsecE) (simp add: nzero_def)
lemma nmul_assoc:
  "A \<in> nsec U \<Longrightarrow> B \<in> nsec U \<Longrightarrow> C \<in> nsec U \<Longrightarrow> nmul U (nmul U A B) C = nmul U A (nmul U B C)"
  by (elim nsecE) (simp add: mult.assoc)
lemma nmul_unit_left: "A \<in> nsec U \<Longrightarrow> nmul U (nunit U) A = A"
  by (elim nsecE) (simp add: nunit_def)
lemma nmul_unit_right: "A \<in> nsec U \<Longrightarrow> nmul U A (nunit U) = A"
  by (elim nsecE) (simp add: nunit_def)
lemma nmul_distrib_left:
  "A \<in> nsec U \<Longrightarrow> B \<in> nsec U \<Longrightarrow> C \<in> nsec U \<Longrightarrow>
    nmul U A (nadd U B C) = nadd U (nmul U A B) (nmul U A C)"
  by (elim nsecE) (simp add: distrib_left)
lemma nmul_distrib_right:
  "A \<in> nsec U \<Longrightarrow> B \<in> nsec U \<Longrightarrow> C \<in> nsec U \<Longrightarrow>
    nmul U (nadd U B C) A = nadd U (nmul U B A) (nmul U C A)"
  by (elim nsecE) (simp add: distrib_right)

subsection \<open>Restriction laws\<close>

lemma nrho_add:
  "V \<subseteq> U \<Longrightarrow> A \<in> nsec U \<Longrightarrow> B \<in> nsec U \<Longrightarrow>
    nrho U V (nadd U A B) = nadd V (nrho U V A) (nrho U V B)"
  by (elim nsecE) simp
lemma nrho_mul:
  "V \<subseteq> U \<Longrightarrow> A \<in> nsec U \<Longrightarrow> B \<in> nsec U \<Longrightarrow>
    nrho U V (nmul U A B) = nmul V (nrho U V A) (nrho U V B)"
  by (elim nsecE) simp
lemma nrho_zero: "V \<subseteq> U \<Longrightarrow> nrho U V (nzero U) = nzero V"
  by (simp add: nzero_def)
lemma nrho_unit: "V \<subseteq> U \<Longrightarrow> nrho U V (nunit U) = nunit V"
  by (simp add: nunit_def)
lemma nrho_id: "A \<in> nsec U \<Longrightarrow> nrho U U A = A"
  by (elim nsecE) simp
lemma nrho_comp:
  "V \<subseteq> U \<Longrightarrow> W \<subseteq> V \<Longrightarrow> A \<in> nsec U \<Longrightarrow> nrho U W A = nrho V W (nrho U V A)"
  by (elim nsecE) simp

section \<open>Locality and gluing for covers with at most continuum many members\<close>

lemma n_locality:
  fixes I :: "real set"
  assumes cov: "U \<subseteq> (\<Union>i\<in>I. V i)"
    and sub: "\<And>i. i \<in> I \<Longrightarrow> V i \<subseteq> U"
    and f: "f \<in> nsec U"
    and zero: "\<And>i. i \<in> I \<Longrightarrow> nrho U (V i) f = nzero (V i)"
  shows "f = nzero U"
proof -
  obtain g where g: "f = ncls U g" using f by (rule nsecE)
  have r: "nrel (V i) g (\<lambda>x. 0)" if "i \<in> I" for i
    using zero[OF that] sub[OF that] by (simp add: g nzero_def ncls_eq_iff)
  have "{x\<in>U. g x \<noteq> 0} \<subseteq> (\<Union>i\<in>I. {x\<in>V i. g x \<noteq> 0})" using cov by auto
  moreover have "csmall (\<Union>i\<in>I. {x\<in>V i. g x \<noteq> 0})"
    by (rule csmall_UNION) (use r in \<open>simp add: nrel_def\<close>)
  ultimately have "csmall {x\<in>U. g x \<noteq> 0}" by (rule csmall_mono)
  moreover have "n1 (g x) = 0" if xU: "x \<in> U" for x
  proof -
    obtain i where "i \<in> I" "x \<in> V i" using cov xU by blast
    then show ?thesis using r[of i] by (simp add: nrel_def)
  qed
  ultimately have "nrel U g (\<lambda>x. 0)" by (simp add: nrel_def)
  then show ?thesis by (simp add: g nzero_def ncls_eq_iff)
qed

lemma n_gluing:
  fixes I :: "real set"
  assumes cov: "U \<subseteq> (\<Union>i\<in>I. V i)"
    and sections: "\<And>i. i \<in> I \<Longrightarrow> V i \<subseteq> U \<and> s i \<in> nsec (V i)"
    and compat: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
      nrho (V i) (V i \<inter> V j) (s i) = nrho (V j) (V i \<inter> V j) (s j)"
  shows "\<exists>t. t \<in> nsec U \<and> (\<forall>i. i \<in> I \<longrightarrow> nrho U (V i) t = s i)"
proof -
  define g where "g i = nrep (s i)" for i
  have s: "s i = ncls (V i) (g i)" if iI: "i \<in> I" for i
  proof -
    obtain h where "s i = ncls (V i) h" using sections[OF iI] by (auto elim: nsecE)
    then show ?thesis by (simp add: g_def)
  qed
  have r: "nrel (V i \<inter> V j) (g i) (g j)" if "i \<in> I" "j \<in> I" for i j
    using compat[OF that] by (simp add: s[OF that(1)] s[OF that(2)] ncls_eq_iff)
  define D where "D = (\<Union>i\<in>I. \<Union>j\<in>I. {x\<in>V i \<inter> V j. g i x \<noteq> g j x})"
  have D: "csmall D"
    unfolding D_def by (intro csmall_UNION) (use r in \<open>simp add: nrel_def\<close>)
  define pick where "pick x = (SOME i. i \<in> I \<and> x \<in> V i)" for x
  have pick: "pick x \<in> I \<and> x \<in> V (pick x)" if "x \<in> U" for x
  proof -
    have "\<exists>i. i \<in> I \<and> x \<in> V i" using cov that by blast
    then show ?thesis unfolding pick_def by (rule someI_ex)
  qed
  define t where "t x = g (pick x) x" for x
  have "nrho U (V i) (ncls U t) = s i" if i: "i \<in> I" for i
  proof -
    have sub: "V i \<subseteq> U" using sections[OF i] by simp
    have "n1 (t x) = n1 (g i x)" if "x \<in> V i" for x
    proof -
      have p: "pick x \<in> I" "x \<in> V (pick x)" using pick sub that by auto
      show ?thesis using r[OF p(1) i] p(2) that by (simp add: nrel_def t_def)
    qed
    moreover have "{x\<in>V i. t x \<noteq> g i x} \<subseteq> D"
    proof
      fix x assume "x \<in> {x\<in>V i. t x \<noteq> g i x}"
      then have x: "x \<in> V i" "g (pick x) x \<noteq> g i x" by (auto simp: t_def)
      have p: "pick x \<in> I" "x \<in> V (pick x)" using pick sub x(1) by auto
      show "x \<in> D" unfolding D_def using p i x by blast
    qed
    then have "csmall {x\<in>V i. t x \<noteq> g i x}" by (rule csmall_mono) (rule D)
    ultimately have "nrel (V i) t (g i)" by (simp add: nrel_def)
    then show ?thesis using sub by (simp add: s[OF i] ncls_eq_iff)
  qed
  then show ?thesis by (intro exI[of _ "ncls U t"]) simp
qed

section \<open>Sections over a point form a field\<close>

lemma nrel_point: "nrel {a} g h \<longleftrightarrow> n1 (g a) = n1 (h a)"
proof -
  have "csmall {x\<in>{a}. g x \<noteq> h x}"
    by (rule csmall_mono[of _ "{a}"]) auto
  then show ?thesis by (simp add: nrel_def)
qed

lemma nmul_comm_point: "A \<in> nsec {a} \<Longrightarrow> B \<in> nsec {a} \<Longrightarrow> nmul {a} A B = nmul {a} B A"
  by (elim nsecE) (simp add: ncls_eq_iff nrel_point mult.commute)

lemma nzero_ne_nunit_point: "nzero {a} \<noteq> nunit {a}"
  by (simp add: nzero_def nunit_def ncls_eq_iff nrel_point)

lemma ninverse_point:
  assumes "A \<in> nsec {a}" "A \<noteq> nzero {a}"
  shows "\<exists>B. B \<in> nsec {a} \<and> nmul {a} A B = nunit {a} \<and> nmul {a} B A = nunit {a}"
proof -
  obtain g where g: "A = ncls {a} g" using assms(1) by (rule nsecE)
  have ne: "n1 (g a) \<noteq> 0" using assms(2) by (simp add: g nzero_def ncls_eq_iff nrel_point)
  let ?B = "ncls {a} (\<lambda>x. NC (inverse (n1 (g a))) 0 0 0)"
  have "nmul {a} A ?B = nunit {a}" "nmul {a} ?B A = nunit {a}"
    using ne by (simp_all add: g nunit_def ncls_eq_iff nrel_point)
  then show ?thesis by (intro exI[of _ ?B]) simp
qed

section \<open>Global sections do not commute\<close>

lemma nmul_noncommutative:
  assumes "\<not> csmall (UNIV :: 'x set)"
  shows "nmul UNIV (ncls UNIV (\<lambda>x::'x. NC 0 1 0 0)) (ncls UNIV (\<lambda>x. NC 0 0 1 0)) \<noteq>
         nmul UNIV (ncls UNIV (\<lambda>x. NC 0 0 1 0)) (ncls UNIV (\<lambda>x. NC 0 1 0 0))"
proof -
  have "{x\<in>(UNIV :: 'x set). NC 0 1 0 0 * NC 0 0 1 0 \<noteq> NC 0 0 1 0 * NC 0 1 0 0} = UNIV"
    using nc_noncommutative by auto
  then show ?thesis using assms by (simp add: ncls_eq_iff nrel_def)
qed

end
