theory NC_Counterexample
  imports Counterexample NC_Core
begin

text \<open>The presheaf \<open>nsec\<close> of \<open>nc\<close>-valued functions modulo small sets, on a discrete space,
checked against the unmodified AFP locales.\<close>

lemma nsections_ring:
  "Ring_Theory.ring (nsec U :: ('x \<Rightarrow> nc) set set) (nadd U) (nmul U) (nzero U) (nunit U)"
proof -
  have am: "Group_Theory.monoid (nsec U :: ('x \<Rightarrow> nc) set set) (nadd U) (nzero U)"
  proof (unfold_locales)
    show "\<And>a b. a\<in>nsec U \<Longrightarrow> b\<in>nsec U \<Longrightarrow> nadd U a b\<in>(nsec U :: ('x \<Rightarrow> nc) set set)"
      by (rule nadd_closed)
    show "nzero U\<in>(nsec U :: ('x \<Rightarrow> nc) set set)" by (rule nzero_closed)
    show "\<And>a b c. a\<in>nsec U \<Longrightarrow> b\<in>nsec U \<Longrightarrow> c\<in>nsec U \<Longrightarrow>
      nadd U (nadd U a b) c = (nadd U a (nadd U b c) :: ('x \<Rightarrow> nc) set)"
      by (rule nadd_assoc)
    show "\<And>a. a\<in>nsec U \<Longrightarrow> nadd U (nzero U) a = (a :: ('x \<Rightarrow> nc) set)"
      by (rule nadd_zero_left)
    show "\<And>a. a\<in>nsec U \<Longrightarrow> nadd U a (nzero U) = (a :: ('x \<Rightarrow> nc) set)"
      by (rule nadd_zero_right)
  qed
  interpret am: Group_Theory.monoid "nsec U :: ('x \<Rightarrow> nc) set set" "nadd U" "nzero U"
    by fact
  have inv: "am.invertible f" if "f \<in> nsec U" for f
  proof (rule am.invertibleI[where v="nneg U f"])
    show "nadd U f (nneg U f) = nzero U" by (rule nadd_neg_right[OF that])
    show "nadd U (nneg U f) f = nzero U" by (rule nadd_neg_left[OF that])
    show "f\<in>nsec U" by fact
    show "nneg U f\<in>nsec U" by (rule nneg_closed[OF that])
  qed
  have ag: "Group_Theory.abelian_group (nsec U :: ('x \<Rightarrow> nc) set set) (nadd U) (nzero U)"
    by (intro Group_Theory.abelian_group.intro Group_Theory.group.intro
        Group_Theory.group_axioms.intro Group_Theory.commutative_monoid.intro
        Group_Theory.commutative_monoid_axioms.intro am)
       (erule inv | erule (1) nadd_comm)+
  have mm: "Group_Theory.monoid (nsec U :: ('x \<Rightarrow> nc) set set) (nmul U) (nunit U)"
  proof (unfold_locales)
    show "\<And>a b. a\<in>nsec U \<Longrightarrow> b\<in>nsec U \<Longrightarrow> nmul U a b\<in>(nsec U :: ('x \<Rightarrow> nc) set set)"
      by (rule nmul_closed)
    show "nunit U\<in>(nsec U :: ('x \<Rightarrow> nc) set set)" by (rule nunit_closed)
    show "\<And>a b c. a\<in>nsec U \<Longrightarrow> b\<in>nsec U \<Longrightarrow> c\<in>nsec U \<Longrightarrow>
      nmul U (nmul U a b) c = (nmul U a (nmul U b c) :: ('x \<Rightarrow> nc) set)"
      by (rule nmul_assoc)
    show "\<And>a. a\<in>nsec U \<Longrightarrow> nmul U (nunit U) a = (a :: ('x \<Rightarrow> nc) set)"
      by (rule nmul_unit_left)
    show "\<And>a. a\<in>nsec U \<Longrightarrow> nmul U a (nunit U) = (a :: ('x \<Rightarrow> nc) set)"
      by (rule nmul_unit_right)
  qed
  show ?thesis
    by (intro Ring_Theory.ring.intro Ring_Theory.ring_axioms.intro ag mm)
       (erule (2) nmul_distrib_left | erule (2) nmul_distrib_right)+
qed

lemma nrho_map:
  "Set_Theory.map (nrho U V :: ('x \<Rightarrow> nc) set \<Rightarrow> ('x \<Rightarrow> nc) set) (nsec U) (nsec V)"
  by (auto simp: Set_Theory.map_def nrho_def PiE_def extensional_def cut_def)

lemma nrho_hom:
  assumes "V \<subseteq> U"
  shows "Ring_Theory.ring_homomorphism (nrho U V :: ('x \<Rightarrow> nc) set \<Rightarrow> ('x \<Rightarrow> nc) set)
      (nsec U) (nadd U) (nmul U) (nzero U) (nunit U)
      (nsec V) (nadd V) (nmul V) (nzero V) (nunit V)"
proof -
  interpret src: Ring_Theory.ring "nsec U :: ('x \<Rightarrow> nc) set set" "nadd U" "nmul U" "nzero U" "nunit U"
    by (rule nsections_ring)
  interpret tgt: Ring_Theory.ring "nsec V :: ('x \<Rightarrow> nc) set set" "nadd V" "nmul V" "nzero V" "nunit V"
    by (rule nsections_ring)
  have hm: "Set_Theory.map (nrho U V :: ('x \<Rightarrow> nc) set \<Rightarrow> ('x \<Rightarrow> nc) set) (nsec U) (nsec V)"
    by (rule nrho_map)
  have ha: "nrho U V (nadd U f g) = nadd V (nrho U V f) (nrho U V g)"
    if "f\<in>nsec U" "g\<in>nsec U" for f g :: "('x \<Rightarrow> nc) set"
    by (rule nrho_add[OF assms that])
  have hz: "nrho U V (nzero U) = (nzero V :: ('x \<Rightarrow> nc) set)"
    by (rule nrho_zero[OF assms])
  have ht: "nrho U V (nmul U f g) = nmul V (nrho U V f) (nrho U V g)"
    if "f\<in>nsec U" "g\<in>nsec U" for f g :: "('x \<Rightarrow> nc) set"
    by (rule nrho_mul[OF assms that])
  have ho: "nrho U V (nunit U) = (nunit V :: ('x \<Rightarrow> nc) set)"
    by (rule nrho_unit[OF assms])
  show ?thesis
    using hm src.ring_axioms tgt.ring_axioms
      src.additive.group_axioms tgt.additive.group_axioms
      src.additive.monoid_axioms tgt.additive.monoid_axioms
      src.multiplicative.monoid_axioms tgt.multiplicative.monoid_axioms ha hz ht ho
    unfolding Ring_Theory.ring_homomorphism_def Group_Theory.group_homomorphism_def
      Group_Theory.monoid_homomorphism_def Group_Theory.monoid_homomorphism_axioms_def
    by blast
qed

lemma nc_presheaf:
  "presheaf_of_rings (UNIV :: 'x set) (\<lambda>U. True) (nsec :: 'x set \<Rightarrow> ('x \<Rightarrow> nc) set set)
      nrho {\<lambda>x. undefined} nadd nmul nzero nunit"
proof (intro presheaf_of_rings.intro presheaf_of_rings_axioms.intro)
  show "Topological_Space.topological_space (UNIV :: 'x set) (\<lambda>U. True)"
    by unfold_locales auto
  show "\<And>U V. V \<subseteq> U \<Longrightarrow>
       ring_homomorphism (nrho U V :: ('x \<Rightarrow> nc) set \<Rightarrow> ('x \<Rightarrow> nc) set)
       (nsec U) (nadd U) (nmul U) (nzero U) (nunit U)
       (nsec V) (nadd V) (nmul V) (nzero V) (nunit V)"
    by (rule nrho_hom)
  show "nsec {} = {{\<lambda>x::'x. undefined::nc}}" by (rule nsec_empty)
  show "\<And>U f. f \<in> nsec U \<Longrightarrow> nrho U U f = (f :: ('x \<Rightarrow> nc) set)"
    by (rule nrho_id)
  show "\<And>U V W f. V \<subseteq> U \<Longrightarrow> W \<subseteq> V \<Longrightarrow> f \<in> nsec U \<Longrightarrow>
        nrho U W f = (nrho V W \<circ> nrho U V) (f :: ('x \<Rightarrow> nc) set)"
    by (simp only: comp_apply) (rule nrho_comp)
qed

lemma nc_sheaf:
  "sheaf_of_rings (UNIV :: 'x set) (\<lambda>U. True) (nsec :: 'x set \<Rightarrow> ('x \<Rightarrow> nc) set set)
      nrho {\<lambda>x. undefined} nadd nmul nzero nunit"
proof (intro sheaf_of_rings.intro sheaf_of_rings_axioms.intro nc_presheaf)
  fix U I V f
  assume cover: "open_cover_of_open_subset (UNIV :: 'x set) (\<lambda>U. True) U I V"
    and sub: "\<And>i. i\<in>I \<Longrightarrow> V i \<subseteq> U"
    and f: "f \<in> (nsec U :: ('x \<Rightarrow> nc) set set)"
    and zero: "\<And>i. i\<in>I \<Longrightarrow> nrho U (V i) f = nzero (V i)"
  have covers: "U \<subseteq> (\<Union>i\<in>I. V i)"
    using cover by (simp add: open_cover_of_open_subset_def open_cover_of_subset_def
      cover_of_subset_def)
  show "f = nzero U"
    by (rule n_locality[OF covers sub f zero])
next
  fix U I V s
  assume cover: "open_cover_of_open_subset (UNIV :: 'x set) (\<lambda>U. True) U I V"
    and sections: "\<forall>i. i\<in>I \<longrightarrow> V i \<subseteq> U \<and> s i \<in> (nsec (V i) :: ('x \<Rightarrow> nc) set set)"
    and compat: "\<And>i j. i\<in>I \<Longrightarrow> j\<in>I \<Longrightarrow>
      nrho (V i) (V i \<inter> V j) (s i) = nrho (V j) (V i \<inter> V j) (s j)"
  have covers: "U \<subseteq> (\<Union>i\<in>I. V i)"
    using cover by (simp add: open_cover_of_open_subset_def open_cover_of_subset_def
      cover_of_subset_def)
  show "\<exists>t. t \<in> (nsec U :: ('x \<Rightarrow> nc) set set) \<and> (\<forall>i. i\<in>I \<longrightarrow> nrho U (V i) t = s i)"
    by (rule n_gluing[OF covers _ compat]) (use sections in auto)
qed

text \<open>Over every point the ring of sections is a commutative ring in which every nonzero
element is invertible, that is, a field.\<close>

lemma nc_point_comm_ring:
  "Comm_Ring.comm_ring (nsec {a} :: ('x \<Rightarrow> nc) set set)
      (nadd {a}) (nmul {a}) (nzero {a}) (nunit {a})"
  by (intro Comm_Ring.comm_ring.intro nsections_ring Comm_Ring.comm_ring_axioms.intro)
     (rule nmul_comm_point)

lemma nc_point_field:
  "Comm_Ring.comm_ring (nsec {a} :: ('x \<Rightarrow> nc) set set)
          (nadd {a}) (nmul {a}) (nzero {a}) (nunit {a})
        \<and> (nzero {a} :: ('x \<Rightarrow> nc) set) \<noteq> nunit {a}
        \<and> (\<forall>u \<in> (nsec {a} :: ('x \<Rightarrow> nc) set set). u \<noteq> nzero {a} \<longrightarrow>
              (\<exists>v \<in> nsec {a}. nmul {a} u v = nunit {a} \<and> nmul {a} v u = nunit {a}))"
proof (intro conjI ballI impI)
  show "Comm_Ring.comm_ring (nsec {a} :: ('x \<Rightarrow> nc) set set)
          (nadd {a}) (nmul {a}) (nzero {a}) (nunit {a})"
    by (rule nc_point_comm_ring)
  show "(nzero {a} :: ('x \<Rightarrow> nc) set) \<noteq> nunit {a}"
    by (rule nzero_ne_nunit_point)
  fix u :: "('x \<Rightarrow> nc) set"
  assume "u \<in> nsec {a}" "u \<noteq> nzero {a}"
  from ninverse_point[OF this]
  show "\<exists>v \<in> nsec {a}. nmul {a} u v = nunit {a} \<and> nmul {a} v u = nunit {a}"
    by (elim exE conjE) (rule bexI, rule conjI)
qed

lemma nc_global_noncommutative:
  "\<exists>u \<in> (nsec UNIV :: (coeff \<Rightarrow> nc) set set). \<exists>v \<in> nsec UNIV.
        nmul UNIV u v \<noteq> nmul UNIV v u"
proof (intro bexI)
  show "nmul UNIV (ncls UNIV (\<lambda>x::coeff. NC 0 1 0 0)) (ncls UNIV (\<lambda>x. NC 0 0 1 0)) \<noteq>
         nmul UNIV (ncls UNIV (\<lambda>x. NC 0 0 1 0)) (ncls UNIV (\<lambda>x. NC 0 1 0 0))"
    by (rule nmul_noncommutative[OF coeff_not_csmall])
qed (rule ncls_in_nsec)+

text \<open>The ring of global sections is not commutative when the space has more than
continuum many points. The statement uses the unmodified AFP predicate \<open>sheaf_of_rings\<close>.\<close>

theorem afp_sheaf_with_noncommutative_global_sections:
  "sheaf_of_rings (UNIV :: coeff set) (\<lambda>U. True)
       (nsec :: coeff set \<Rightarrow> (coeff \<Rightarrow> nc) set set)
       nrho {\<lambda>x. undefined} nadd nmul nzero nunit
   \<and> (\<forall>a::coeff.
        Comm_Ring.comm_ring (nsec {a} :: (coeff \<Rightarrow> nc) set set)
          (nadd {a}) (nmul {a}) (nzero {a}) (nunit {a})
        \<and> (nzero {a} :: (coeff \<Rightarrow> nc) set) \<noteq> nunit {a}
        \<and> (\<forall>u \<in> (nsec {a} :: (coeff \<Rightarrow> nc) set set). u \<noteq> nzero {a} \<longrightarrow>
              (\<exists>v \<in> nsec {a}. nmul {a} u v = nunit {a} \<and> nmul {a} v u = nunit {a})))
   \<and> (\<exists>u \<in> (nsec UNIV :: (coeff \<Rightarrow> nc) set set). \<exists>v \<in> nsec UNIV.
        nmul UNIV u v \<noteq> nmul UNIV v u)"
  by (rule conjI[OF nc_sheaf conjI[OF allI[OF nc_point_field] nc_global_noncommutative]])

end
