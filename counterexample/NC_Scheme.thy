theory NC_Scheme
  imports NC_Counterexample Point_Schemes
begin

text \<open>The theory \<open>Point_Schemes\<close> shows, for the unmodified AFP locales, that a
\<open>sheaf_of_rings\<close> on a space with open points whose rings of sections over the points are
fields is a \<open>scheme\<close>. It applies to the presheaf \<open>nsec\<close>.\<close>

lemma nc_scheme:
  "scheme (UNIV :: 'x set) (\<lambda>U. True) (nsec :: 'x set \<Rightarrow> ('x \<Rightarrow> nc) set set)
      nrho {\<lambda>x. undefined} nadd nmul nzero nunit (UNIV :: ('x \<Rightarrow> nc) set set)"
proof (rule sheaf_of_rings.open_points_scheme_field[OF nc_sheaf])
  fix a :: 'x
  show "True" ..
  show "Comm_Ring.comm_ring (nsec {a} :: ('x \<Rightarrow> nc) set set)
      (nadd {a}) (nmul {a}) (nzero {a}) (nunit {a})"
    by (rule nc_point_comm_ring)
  show "(nzero {a} :: ('x \<Rightarrow> nc) set) \<noteq> nunit {a}"
    by (rule nzero_ne_nunit_point)
next
  fix a :: 'x and s :: "('x \<Rightarrow> nc) set"
  assume "s \<in> nsec {a}" "s \<noteq> nzero {a}"
  from ninverse_point[OF this]
  show "\<exists>t\<in>nsec {a}. nmul {a} s t = nunit {a}" by blast
qed

text \<open>An object satisfying the unmodified AFP locale \<open>scheme\<close> whose ring of global sections
is not commutative.\<close>

theorem afp_scheme_with_noncommutative_global_sections:
  "scheme (UNIV :: coeff set) (\<lambda>U. True)
       (nsec :: coeff set \<Rightarrow> (coeff \<Rightarrow> nc) set set)
       nrho {\<lambda>x. undefined} nadd nmul nzero nunit (UNIV :: (coeff \<Rightarrow> nc) set set)
   \<and> (\<exists>u \<in> (nsec UNIV :: (coeff \<Rightarrow> nc) set set). \<exists>v \<in> nsec UNIV.
        nmul UNIV u v \<noteq> nmul UNIV v u)"
  by (rule conjI[OF nc_scheme nc_global_noncommutative])

text \<open>The construction is hidden in the proof: the AFP scheme predicate does not imply
commutativity of global sections. Only the ambient carrier types are fixed.\<close>

theorem exists_scheme_with_noncommutative_global_sections:
  "\<exists>(S :: coeff set) is_open (F :: coeff set \<Rightarrow> (coeff \<Rightarrow> nc) set set)
      rho b add mult zero one (A :: (coeff \<Rightarrow> nc) set set).
    scheme S is_open F rho b add mult zero one A
    \<and> (\<exists>u \<in> F S. \<exists>v \<in> F S. mult S u v \<noteq> mult S v u)"
  using afp_scheme_with_noncommutative_global_sections by blast

end
