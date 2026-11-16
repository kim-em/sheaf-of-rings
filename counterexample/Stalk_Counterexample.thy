theory Stalk_Counterexample
  imports Counterexample
begin

text \<open>Hartshorne, Proposition II.1.1: a morphism of sheaves is an isomorphism if and only if
it induces an isomorphism on every stalk. This theory shows that the statement fails for the
AFP predicate \<open>sheaf_of_rings\<close>: the inclusion of the bounded-range presheaf into the sheaf of
all functions is a morphism of AFP sheaves which is an isomorphism on every stalk, but it is
not an isomorphism.\<close>

section \<open>The sheaf of all functions\<close>

definition fsec :: "'x set \<Rightarrow> ('x \<Rightarrow> 'r) set" where
  "fsec U = {f. \<forall>x. x\<notin>U \<longrightarrow> f x = undefined}"

definition frho :: "'x set \<Rightarrow> 'x set \<Rightarrow> ('x \<Rightarrow> 'r) \<Rightarrow> ('x \<Rightarrow> 'r)" where
  "frho U V = cut (\<lambda>f. cut f V) (fsec U)"

lemma fsec_outside: "f \<in> fsec U \<Longrightarrow> x \<notin> U \<Longrightarrow> f x = undefined"
  by (simp add: fsec_def)
lemma fsec_cut [simp]: "cut f U \<in> fsec U"
  by (simp add: fsec_def cut_def)
lemma fsec_sadd [simp]: "sadd U f g \<in> fsec U"
  by (simp add: sadd_def)
lemma fsec_smul [simp]: "smul U f g \<in> fsec U"
  by (simp add: smul_def)
lemma fsec_sneg [simp]: "sneg U f \<in> fsec U"
  by (simp add: sneg_def)
lemma fsec_szero [simp]: "szero U \<in> fsec U"
  by (simp add: szero_def)
lemma fsec_sone [simp]: "sone U \<in> fsec U"
  by (simp add: sone_def)
lemma frho_apply [simp]: "f \<in> fsec U \<Longrightarrow> frho U V f = cut f V"
  by (simp add: frho_def)
lemma cut_fsec [simp]: "f \<in> fsec U \<Longrightarrow> cut f U = f"
  by (auto simp: fsec_def cut_def fun_eq_iff)
lemma sec_subset_fsec: "sec U \<subseteq> fsec U"
  by (auto simp: sec_def fsec_def)
lemma sec_in_fsec: "f \<in> sec U \<Longrightarrow> f \<in> fsec U"
  using sec_subset_fsec by blast

lemma fsections_ring:
  "Ring_Theory.ring (fsec U :: ('x \<Rightarrow> 'r::ring_1) set)
    (sadd U) (smul U) (szero U) (sone U)"
proof -
  have am: "Group_Theory.monoid (fsec U :: ('x \<Rightarrow> 'r) set) (sadd U) (szero U)"
  proof (unfold_locales)
    show "\<And>a b. a\<in>fsec U \<Longrightarrow> b\<in>fsec U \<Longrightarrow> sadd U a b\<in>(fsec U :: ('x\<Rightarrow>'r)set)"
      by simp
    show "szero U\<in>(fsec U :: ('x\<Rightarrow>'r)set)" by simp
    show "\<And>a b c. a\<in>fsec U \<Longrightarrow> b\<in>fsec U \<Longrightarrow> c\<in>fsec U \<Longrightarrow>
      sadd U (sadd U a b) c = (sadd U a (sadd U b c) :: 'x\<Rightarrow>'r)"
      by (auto simp: sadd_def cut_def fun_eq_iff add.assoc)
    show "\<And>a. a\<in>fsec U \<Longrightarrow> sadd U (szero U) a = (a :: 'x\<Rightarrow>'r)"
      by (auto simp: sadd_def szero_def cut_def fun_eq_iff dest: fsec_outside)
    show "\<And>a. a\<in>fsec U \<Longrightarrow> sadd U a (szero U) = (a :: 'x\<Rightarrow>'r)"
      by (auto simp: sadd_def szero_def cut_def fun_eq_iff dest: fsec_outside)
  qed
  interpret am: Group_Theory.monoid "fsec U :: ('x \<Rightarrow> 'r) set" "sadd U" "szero U"
    by fact
  have inv: "am.invertible f" if "f \<in> fsec U" for f
  proof (rule am.invertibleI[where v="sneg U f"])
    show "sadd U f (sneg U f) = szero U"
      by (auto simp: sadd_def sneg_def szero_def cut_def fun_eq_iff)
    show "sadd U (sneg U f) f = szero U"
      by (auto simp: sadd_def sneg_def szero_def cut_def fun_eq_iff)
    show "f\<in>fsec U" by fact
    show "sneg U f\<in>fsec U" by simp
  qed
  have ag: "Group_Theory.abelian_group (fsec U :: ('x \<Rightarrow> 'r) set) (sadd U) (szero U)"
    by (intro Group_Theory.abelian_group.intro Group_Theory.group.intro
        Group_Theory.group_axioms.intro Group_Theory.commutative_monoid.intro
        Group_Theory.commutative_monoid_axioms.intro am)
       (use inv in \<open>auto simp: sadd_def cut_def fun_eq_iff add.commute\<close>)
  have mm: "Group_Theory.monoid (fsec U :: ('x \<Rightarrow> 'r) set) (smul U) (sone U)"
  proof (unfold_locales)
    show "\<And>a b. a\<in>fsec U \<Longrightarrow> b\<in>fsec U \<Longrightarrow> smul U a b\<in>(fsec U :: ('x\<Rightarrow>'r)set)"
      by simp
    show "sone U\<in>(fsec U :: ('x\<Rightarrow>'r)set)" by simp
    show "\<And>a b c. a\<in>fsec U \<Longrightarrow> b\<in>fsec U \<Longrightarrow> c\<in>fsec U \<Longrightarrow>
      smul U (smul U a b) c = (smul U a (smul U b c) :: 'x\<Rightarrow>'r)"
      by (auto simp: smul_def cut_def fun_eq_iff mult.assoc)
    show "\<And>a. a\<in>fsec U \<Longrightarrow> smul U (sone U) a = (a :: 'x\<Rightarrow>'r)"
      by (auto simp: smul_def sone_def cut_def fun_eq_iff dest: fsec_outside)
    show "\<And>a. a\<in>fsec U \<Longrightarrow> smul U a (sone U) = (a :: 'x\<Rightarrow>'r)"
      by (auto simp: smul_def sone_def cut_def fun_eq_iff dest: fsec_outside)
  qed
  show ?thesis
    by (intro Ring_Theory.ring.intro Ring_Theory.ring_axioms.intro ag mm)
       (auto simp: sadd_def smul_def cut_def fun_eq_iff algebra_simps)
qed

lemma frho_map:
  assumes "V \<subseteq> U"
  shows "Set_Theory.map (frho U V :: ('x \<Rightarrow> 'r) \<Rightarrow> ('x \<Rightarrow> 'r)) (fsec U) (fsec V)"
  by (auto simp: Set_Theory.map_def frho_def PiE_def extensional_def cut_def fsec_def)

lemma frho_hom:
  assumes "V \<subseteq> U"
  shows "Ring_Theory.ring_homomorphism (frho U V :: ('x \<Rightarrow> 'r::ring_1) \<Rightarrow> ('x \<Rightarrow> 'r))
      (fsec U) (sadd U) (smul U) (szero U) (sone U)
      (fsec V) (sadd V) (smul V) (szero V) (sone V)"
proof -
  interpret src: Ring_Theory.ring "fsec U :: ('x \<Rightarrow> 'r) set" "sadd U" "smul U" "szero U" "sone U"
    by (rule fsections_ring)
  interpret tgt: Ring_Theory.ring "fsec V :: ('x \<Rightarrow> 'r) set" "sadd V" "smul V" "szero V" "sone V"
    by (rule fsections_ring)
  have hm: "Set_Theory.map (frho U V :: ('x\<Rightarrow>'r)\<Rightarrow>('x\<Rightarrow>'r)) (fsec U) (fsec V)"
    by (rule frho_map[OF assms])
  have ha: "frho U V (sadd U f g) = sadd V (frho U V f) (frho U V g)"
    if "f\<in>fsec U" "g\<in>fsec U" for f g :: "'x\<Rightarrow>'r"
    using assms that
    by (simp only: frho_apply[OF fsec_sadd] frho_apply[OF that(1)] frho_apply[OF that(2)])
       (auto simp: sadd_def cut_def fun_eq_iff)
  have hz: "frho U V (szero U) = (szero V :: 'x\<Rightarrow>'r)"
    using assms by (simp only: frho_apply[OF fsec_szero])
      (auto simp: szero_def cut_def fun_eq_iff)
  have ht: "frho U V (smul U f g) = smul V (frho U V f) (frho U V g)"
    if "f\<in>fsec U" "g\<in>fsec U" for f g :: "'x\<Rightarrow>'r"
    using assms that
    by (simp only: frho_apply[OF fsec_smul] frho_apply[OF that(1)] frho_apply[OF that(2)])
       (auto simp: smul_def cut_def fun_eq_iff)
  have ho: "frho U V (sone U) = (sone V :: 'x\<Rightarrow>'r)"
    using assms by (simp only: frho_apply[OF fsec_sone])
      (auto simp: sone_def cut_def fun_eq_iff)
  show ?thesis
    using hm src.ring_axioms tgt.ring_axioms
      src.additive.group_axioms tgt.additive.group_axioms
      src.additive.monoid_axioms tgt.additive.monoid_axioms
      src.multiplicative.monoid_axioms tgt.multiplicative.monoid_axioms ha hz ht ho
    unfolding Ring_Theory.ring_homomorphism_def Group_Theory.group_homomorphism_def
      Group_Theory.monoid_homomorphism_def Group_Theory.monoid_homomorphism_axioms_def
    by blast
qed

lemma fsec_empty: "fsec {} = {\<lambda>x. undefined}"
  by (auto simp: fsec_def fun_eq_iff)

lemma all_functions_presheaf:
  "presheaf_of_rings (UNIV :: 'x set) (\<lambda>U. True) (fsec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r::ring_1) set)
      frho (\<lambda>x. undefined) sadd smul szero sone"
proof (intro presheaf_of_rings.intro presheaf_of_rings_axioms.intro)
  show "Topological_Space.topological_space (UNIV :: 'x set) (\<lambda>U. True)"
    by unfold_locales auto
  show "\<And>U V. V \<subseteq> U \<Longrightarrow>
       ring_homomorphism (frho U V :: ('x \<Rightarrow> 'r) \<Rightarrow> ('x \<Rightarrow> 'r))
       (fsec U) (sadd U) (smul U) (szero U) (sone U)
       (fsec V) (sadd V) (smul V) (szero V) (sone V)"
    by (rule frho_hom)
  show "fsec {} = {\<lambda>x::'x. undefined::'r}" by (rule fsec_empty)
  show "\<And>U f. f \<in> fsec U \<Longrightarrow> frho U U f = (f :: 'x \<Rightarrow> 'r)"
    by simp
  show "\<And>U V W f. V \<subseteq> U \<Longrightarrow> W \<subseteq> V \<Longrightarrow> f \<in> fsec U \<Longrightarrow>
        frho U W f = (frho V W \<circ> frho U V) (f :: 'x \<Rightarrow> 'r)"
    by (auto simp: cut_def fun_eq_iff)
qed

text \<open>The presheaf of all functions satisfies the AFP predicate (it is a genuine sheaf).\<close>

lemma all_functions_sheaf:
  "sheaf_of_rings (UNIV :: 'x set) (\<lambda>U. True) (fsec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r::ring_1) set)
      frho (\<lambda>x. undefined) sadd smul szero sone"
proof (intro sheaf_of_rings.intro sheaf_of_rings_axioms.intro all_functions_presheaf)
  fix U I V f
  assume cover: "open_cover_of_open_subset (UNIV :: 'x set) (\<lambda>U. True) U I V"
    and sub: "\<And>i. i\<in>I \<Longrightarrow> V i \<subseteq> U"
    and f: "f \<in> (fsec U :: ('x \<Rightarrow> 'r) set)"
    and zero: "\<And>i. i\<in>I \<Longrightarrow> frho U (V i) f = szero (V i)"
  have covers: "U \<subseteq> (\<Union>i\<in>I. V i)"
    using cover by (simp add: open_cover_of_open_subset_def open_cover_of_subset_def
      cover_of_subset_def)
  show "f = szero U"
  proof (rule ext)
    fix x
    show "f x = szero U x"
    proof (cases "x \<in> U")
      case True
      then obtain i where i: "i\<in>I" "x\<in>V i" using covers by blast
      have "(frho U (V i) f) x = szero (V i) x" using zero[OF i(1)] by simp
      then show ?thesis using f i True by (simp add: szero_def)
    next
      case False
      then show ?thesis using f fsec_outside by (simp add: szero_def cut_def)
    qed
  qed
next
  fix U I V s
  assume cover: "open_cover_of_open_subset (UNIV :: 'x set) (\<lambda>U. True) U I V"
    and sections: "\<forall>i. i\<in>I \<longrightarrow> V i \<subseteq> U \<and> s i \<in> (fsec (V i) :: ('x \<Rightarrow> 'r) set)"
    and compat: "\<And>i j. i\<in>I \<Longrightarrow> j\<in>I \<Longrightarrow>
      frho (V i) (V i \<inter> V j) (s i) = frho (V j) (V i \<inter> V j) (s j)"
  have covers: "U \<subseteq> (\<Union>i\<in>I. V i)"
    using cover by (simp add: open_cover_of_open_subset_def open_cover_of_subset_def
      cover_of_subset_def)
  define pick_index where "pick_index x = (SOME i. i\<in>I \<and> x\<in>V i)" for x
  have pick_index: "pick_index x \<in> I \<and> x \<in> V (pick_index x)" if "x\<in>U" for x
  proof -
    have ex: "\<exists>i. i\<in>I \<and> x\<in>V i" using covers that by blast
    show ?thesis unfolding pick_index_def by (rule someI_ex[OF ex])
  qed
  define t where "t = cut (\<lambda>x. s (pick_index x) x) U"
  have t: "t \<in> (fsec U :: ('x \<Rightarrow> 'r) set)"
    unfolding t_def by simp
  have cuts: "frho U (V i) t = s i" if "i\<in>I" for i
  proof (rule ext)
    fix x
    have si: "s i \<in> fsec (V i)" and sub: "V i \<subseteq> U" using sections that by auto
    show "frho U (V i) t x = s i x"
    proof (cases "x\<in>V i")
      case True
      then have xu: "x\<in>U" using sub by blast
      have ci: "pick_index x\<in>I" and xc: "x\<in>V (pick_index x)" using pick_index[OF xu] by auto
      have sc: "s (pick_index x)\<in>fsec (V (pick_index x))" using sections ci by auto
      have "(frho (V i) (V i \<inter> V (pick_index x)) (s i)) x =
            (frho (V (pick_index x)) (V i \<inter> V (pick_index x)) (s (pick_index x))) x"
        using compat[OF that ci] by simp
      then have "s i x = s (pick_index x) x" using si sc True xc by simp
      then show ?thesis using t True xu by (simp add: t_def)
    next
      case False
      then show ?thesis using fsec_outside[OF si False] t by (simp add: cut_def)
    qed
  qed
  show "\<exists>t. t \<in> (fsec U :: ('x \<Rightarrow> 'r) set) \<and> (\<forall>i. i\<in>I \<longrightarrow> frho U (V i) t = s i)"
    using t cuts by blast
qed

section \<open>The inclusion of bounded-range sections\<close>

lemma inclusion_hom:
  "Ring_Theory.ring_homomorphism (identity (sec U :: ('x \<Rightarrow> 'r::ring_1) set))
      (sec U) (sadd U) (smul U) (szero U) (sone U)
      (fsec U) (sadd U) (smul U) (szero U) (sone U)"
proof -
  interpret src: Ring_Theory.ring "sec U :: ('x \<Rightarrow> 'r) set" "sadd U" "smul U" "szero U" "sone U"
    by (rule sections_ring)
  interpret tgt: Ring_Theory.ring "fsec U :: ('x \<Rightarrow> 'r) set" "sadd U" "smul U" "szero U" "sone U"
    by (rule fsections_ring)
  have hm: "Set_Theory.map (identity (sec U :: ('x \<Rightarrow> 'r) set)) (sec U) (fsec U)"
    using sec_subset_fsec by (auto simp: Set_Theory.map_def)
  have ha: "identity (sec U) (sadd U f g) = sadd U (identity (sec U) f) (identity (sec U) g)"
    if "f\<in>sec U" "g\<in>sec U" for f g :: "'x\<Rightarrow>'r"
    using that by simp
  have hz: "identity (sec U) (szero U) = (szero U :: 'x\<Rightarrow>'r)"
    by simp
  have ht: "identity (sec U) (smul U f g) = smul U (identity (sec U) f) (identity (sec U) g)"
    if "f\<in>sec U" "g\<in>sec U" for f g :: "'x\<Rightarrow>'r"
    using that by simp
  have ho: "identity (sec U) (sone U) = (sone U :: 'x\<Rightarrow>'r)"
    by simp
  show ?thesis
    using hm src.ring_axioms tgt.ring_axioms
      src.additive.group_axioms tgt.additive.group_axioms
      src.additive.monoid_axioms tgt.additive.monoid_axioms
      src.multiplicative.monoid_axioms tgt.multiplicative.monoid_axioms ha hz ht ho
    unfolding Ring_Theory.ring_homomorphism_def Group_Theory.group_homomorphism_def
      Group_Theory.monoid_homomorphism_def Group_Theory.monoid_homomorphism_axioms_def
    by blast
qed

lemma inclusion_morphism_presheaves:
  "morphism_presheaves_of_rings (UNIV :: 'x set) (\<lambda>U. True)
      (sec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r::ring_1) set) srho (\<lambda>x. undefined) sadd smul szero sone
      fsec frho (\<lambda>x. undefined) sadd smul szero sone
      (\<lambda>U. identity (sec U))"
proof (intro morphism_presheaves_of_rings.intro morphism_presheaves_of_rings_axioms.intro
    bounded_range_presheaf all_functions_presheaf)
  show "\<And>U. ring_homomorphism (identity (sec U :: ('x \<Rightarrow> 'r) set))
      (sec U) (sadd U) (smul U) (szero U) (sone U)
      (fsec U) (sadd U) (smul U) (szero U) (sone U)"
    by (rule inclusion_hom)
  show "\<And>U V f. V \<subseteq> U \<Longrightarrow> f \<in> (sec U :: ('x \<Rightarrow> 'r) set) \<Longrightarrow>
      (frho U V \<circ> identity (sec U)) f = (identity (sec V) \<circ> srho U V) f"
    by (simp add: sec_in_fsec sec_cut)
qed

lemma inclusion_morphism:
  "morphism_sheaves_of_rings (UNIV :: 'x set) (\<lambda>U. True)
      (sec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r::ring_1) set) srho (\<lambda>x. undefined) sadd smul szero sone
      fsec frho (\<lambda>x. undefined) sadd smul szero sone
      (\<lambda>U. identity (sec U))"
  by (intro morphism_sheaves_of_rings.intro inclusion_morphism_presheaves)

text \<open>The inclusion is not an isomorphism: an inverse would send the identity function,
which has more than continuum many values, to a bounded-range global section.\<close>

lemma identity_not_bounded: "(id :: coeff \<Rightarrow> coeff) \<notin> sec UNIV"
proof
  assume "(id :: coeff \<Rightarrow> coeff) \<in> sec UNIV"
  then have "csmall (UNIV :: coeff set)" using sec_small by fastforce
  then show False using coeff_not_csmall by blast
qed

lemma inclusion_not_surjective:
  "(id :: coeff \<Rightarrow> coeff) \<in> fsec UNIV \<and>
   (id :: coeff \<Rightarrow> coeff) \<notin> identity (sec UNIV) ` sec UNIV"
  using identity_not_bounded by (auto simp: fsec_def)

lemma inclusion_not_iso:
  "\<not> iso_sheaves_of_rings (UNIV :: coeff set) (\<lambda>U. True)
      (sec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) srho (\<lambda>x. undefined) sadd smul szero sone
      fsec frho (\<lambda>x. undefined) sadd smul szero sone
      (\<lambda>U. identity (sec U))"
proof
  assume "iso_sheaves_of_rings (UNIV :: coeff set) (\<lambda>U. True)
      (sec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) srho (\<lambda>x. undefined) sadd smul szero sone
      fsec frho (\<lambda>x. undefined) sadd smul szero sone
      (\<lambda>U. identity (sec U))"
  then obtain \<psi> where mor: "morphism_presheaves_of_rings (UNIV :: coeff set) (\<lambda>U. True)
      (fsec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) frho (\<lambda>x. undefined) sadd smul szero sone
      sec srho (\<lambda>x. undefined) sadd smul szero sone \<psi>"
    and inv: "\<forall>U. True \<longrightarrow> (\<forall>f \<in> (fsec U :: (coeff \<Rightarrow> coeff) set).
        (identity (sec U) \<circ> \<psi> U) f = f) \<and>
      (\<forall>f \<in> (sec U :: (coeff \<Rightarrow> coeff) set). (\<psi> U \<circ> identity (sec U)) f = f)"
    unfolding iso_sheaves_of_rings_def iso_presheaves_of_rings_def
      iso_presheaves_of_rings_axioms_def by blast
  have idf: "(id :: coeff \<Rightarrow> coeff) \<in> fsec UNIV" by (simp add: fsec_def)
  have "Set_Theory.map (\<psi> UNIV) (fsec UNIV :: (coeff \<Rightarrow> coeff) set) (sec UNIV)"
    by (rule morphism_presheaves_of_rings.fam_morphisms_are_maps[OF mor]) simp
  then have in_sec: "\<psi> UNIV id \<in> (sec UNIV :: (coeff \<Rightarrow> coeff) set)"
    using idf by (simp add: map.map_closed)
  have "(identity (sec UNIV) \<circ> \<psi> UNIV) (id :: coeff \<Rightarrow> coeff) = id"
    using inv idf by blast
  then have "\<psi> UNIV id = (id :: coeff \<Rightarrow> coeff)" using in_sec by simp
  then show False using in_sec identity_not_bounded by simp
qed

section \<open>Stalks at an open point\<close>

text \<open>If \<open>{x}\<close> is open and the sections over \<open>{x}\<close> are a copy of a ring \<open>'c\<close>, then the
AFP stalk at \<open>x\<close> consists of the classes of those sections.\<close>

lemma (in direct_lim) class_self:
  assumes "U \<in> I" "s \<in> \<FF> U"
  shows "(U, s) \<in> class_of U s"
  using assms by (simp add: class_of_def equivalence.Class_self rel_is_equivalence)

locale pstalk = stalk +
  fixes cst :: "'c::ring_1 \<Rightarrow> 'b"
  assumes open_pt: "is_open {x}"
    and sec_pt: "\<FF> {x} = range cst"
    and cst_inj: "\<And>c d. cst c = cst d \<Longrightarrow> c = d"
    and cst_add: "\<And>c d. add_str {x} (cst c) (cst d) = cst (c + d)"
    and cst_mult: "\<And>c d. mult_str {x} (cst c) (cst d) = cst (c * d)"
    and cst_zero: "zero_str {x} = cst 0"
    and cst_one: "one_str {x} = cst 1"
begin

lemma pt_in: "{x} \<in> I"
  using index open_pt by simp

lemma cst_in: "cst c \<in> \<FF> {x}"
  using sec_pt by simp

lemma rho_pt_id: "s \<in> \<FF> {x} \<Longrightarrow> \<rho> {x} {x} s = s"
  using identity_map open_pt by simp

definition germ :: "'c \<Rightarrow> ('a set \<times> 'b) set" where
  "germ c = class_of {x} (cst c)"

lemma germ_in: "germ c \<in> carrier_stalk"
  using class_of_in_stalk[of "{x}" "cst c"] neighborhoods_eq pt_in cst_in
  by (simp add: germ_def)

lemma germ_inj:
  assumes "germ c = germ d"
  shows "c = d"
proof -
  have m: "({x}, cst c) \<in> Sigma I \<FF>" "({x}, cst d) \<in> Sigma I \<FF>"
    using pt_in cst_in by auto
  have eq: "class_of {x} (cst c) = class_of {x} (cst d)"
    using assms by (simp add: germ_def)
  obtain W where W: "W \<in> I" "W \<subseteq> {x} \<inter> {x}" "\<rho> {x} W (cst c) = \<rho> {x} W (cst d)"
    using class_of_eqD[OF eq m] by blast
  have "W = {x}" using W(1,2) index by auto
  then have "cst c = cst d" using W(3) rho_pt_id cst_in by simp
  then show ?thesis by (rule cst_inj)
qed

lemma class_eq_pt:
  assumes "U \<in> I" "s \<in> \<FF> U"
  shows "\<rho> U {x} s \<in> \<FF> {x}" and "class_of U s = class_of {x} (\<rho> U {x} s)"
proof -
  have op: "is_open U" using assms(1) by (rule subset_of_opens)
  have xU: "{x} \<subseteq> U" using assms(1) index by auto
  have "Set_Theory.map (\<rho> U {x}) (\<FF> U) (\<FF> {x})"
    by (rule is_map_from_is_homomorphism[OF op open_pt xU])
  then show r: "\<rho> U {x} s \<in> \<FF> {x}"
    using assms(2) by (simp add: map.map_closed)
  show "class_of U s = class_of {x} (\<rho> U {x} s)"
  proof (rule class_of_eqI[where W="{x}"])
    show "(U, s) \<in> Sigma I \<FF>" using assms by simp
    show "({x}, \<rho> U {x} s) \<in> Sigma I \<FF>" using pt_in r by simp
    show "{x} \<in> I" by (rule pt_in)
    show "{x} \<subseteq> U \<inter> {x}" using xU by simp
    show "\<rho> U {x} s = \<rho> {x} {x} (\<rho> U {x} s)" using rho_pt_id[OF r] by simp
  qed
qed

lemma class_eq_germ:
  assumes "U \<in> I" "s \<in> \<FF> U"
  obtains c where "class_of U s = germ c" "\<rho> U {x} s = cst c"
  using class_eq_pt[OF assms] sec_pt unfolding germ_def by auto

lemma germ_surj:
  assumes "X \<in> carrier_stalk"
  obtains c where "X = germ c"
proof -
  have "X \<in> carrier_direct_lim"
    using assms by (simp add: carrier_stalk_def neighborhoods_eq)
  then obtain U s where Us: "U \<in> I" "s \<in> \<FF> U" "X = class_of U s"
    by (blast elim: carrier_direct_limE)
  obtain c where "class_of U s = germ c"
    using class_eq_germ[OF Us(1,2)] by blast
  with Us(3) have "X = germ c" by simp
  then show ?thesis by (rule that)
qed

lemma add_germ: "add_stalk (germ c) (germ d) = germ (c + d)"
proof -
  have m: "({x}, cst c) \<in> Sigma I \<FF>" "({x}, cst d) \<in> Sigma I \<FF>"
    using pt_in cst_in by auto
  have "add_rel (class_of {x} (cst c)) (class_of {x} (cst d)) =
      class_of {x} (add_str {x} (\<rho> {x} {x} (cst c)) (\<rho> {x} {x} (cst d)))"
    by (rule add_rel_class_of[OF m pt_in]) auto
  then show ?thesis
    by (simp add: add_stalk_def germ_def rho_pt_id cst_in cst_add)
qed

lemma mult_germ: "mult_stalk (germ c) (germ d) = germ (c * d)"
proof -
  have m: "({x}, cst c) \<in> Sigma I \<FF>" "({x}, cst d) \<in> Sigma I \<FF>"
    using pt_in cst_in by auto
  have "mult_rel (class_of {x} (cst c)) (class_of {x} (cst d)) =
      class_of {x} (mult_str {x} (\<rho> {x} {x} (cst c)) (\<rho> {x} {x} (cst d)))"
    by (rule mult_rel_class_of[OF m pt_in]) auto
  then show ?thesis
    by (simp add: mult_stalk_def germ_def rho_pt_id cst_in cst_mult)
qed

lemma zero_germ:
  assumes "U \<in> I"
  shows "zero_stalk U = germ 0"
  unfolding zero_stalk_def germ_def
  using class_of_0_eq[OF assms pt_in] cst_zero by simp

lemma one_germ:
  assumes "U \<in> I"
  shows "one_stalk U = germ 1"
  unfolding one_stalk_def germ_def
  using class_of_1_eq[OF assms pt_in] cst_one by simp

end

text \<open>Two presheaves on the same space with the same ring of sections over an open point
have isomorphic stalks there.\<close>

locale pstalk_pair =
  A: pstalk S is_open F1 \<rho>1 b1 add1 mult1 zero1 one1 I x cst1 +
  B: pstalk S is_open F2 \<rho>2 b2 add2 mult2 zero2 one2 I x cst2
  for S is_open F1 \<rho>1 b1 add1 mult1 zero1 one1 I x and cst1 :: "'c::ring_1 \<Rightarrow> 'b"
    and F2 \<rho>2 b2 add2 mult2 zero2 one2 and cst2 :: "'c \<Rightarrow> 'd"
begin

definition stalk_map :: "('a set \<times> 'b) set \<Rightarrow> ('a set \<times> 'd) set" where
  "stalk_map X = (if X \<in> A.carrier_stalk then B.germ (THE c. X = A.germ c) else undefined)"

lemma stalk_map_germ [simp]: "stalk_map (A.germ c) = B.germ c"
proof -
  have "(THE c'. A.germ c = A.germ c') = c"
    by (rule the_equality) (auto dest: A.germ_inj)
  then show ?thesis by (simp add: stalk_map_def A.germ_in)
qed

lemma stalk_map_class:
  assumes "U \<in> I" "s \<in> F1 U" "t \<in> F2 U"
    and "\<And>c. \<rho>1 U {x} s = cst1 c \<Longrightarrow> \<rho>2 U {x} t = cst2 c"
  shows "stalk_map (A.class_of U s) = B.class_of U t"
proof -
  obtain c where c: "A.class_of U s = A.germ c" "\<rho>1 U {x} s = cst1 c"
    using A.class_eq_germ[OF assms(1,2)] by blast
  have "\<rho>2 U {x} t = cst2 c" using assms(4) c(2) by blast
  moreover have "B.class_of U t = B.class_of {x} (\<rho>2 U {x} t)"
    by (rule B.class_eq_pt(2)[OF assms(1,3)])
  ultimately show ?thesis by (simp add: c(1) B.germ_def)
qed

lemma stalk_map_iso:
  assumes "U \<in> I"
  shows "ring_isomorphism stalk_map
      A.carrier_stalk A.add_stalk A.mult_stalk (A.zero_stalk U) (A.one_stalk U)
      B.carrier_stalk B.add_stalk B.mult_stalk (B.zero_stalk U) (B.one_stalk U)"
proof -
  have op: "is_open U" "x \<in> U" using assms A.index by auto
  interpret RA: ring A.carrier_stalk A.add_stalk A.mult_stalk "A.zero_stalk U" "A.one_stalk U"
    using A.stalk_is_ring[OF op] .
  interpret RB: ring B.carrier_stalk B.add_stalk B.mult_stalk "B.zero_stalk U" "B.one_stalk U"
    using B.stalk_is_ring[OF op] .
  have mp: "Set_Theory.map stalk_map A.carrier_stalk B.carrier_stalk"
    by (auto simp: Set_Theory.map_def PiE_def extensional_def stalk_map_def B.germ_in)
  have ha: "stalk_map (A.add_stalk X Y) = B.add_stalk (stalk_map X) (stalk_map Y)"
    if XY: "X \<in> A.carrier_stalk" "Y \<in> A.carrier_stalk" for X Y
  proof -
    obtain c where "X = A.germ c" using A.germ_surj[OF XY(1)] by blast
    moreover obtain d where "Y = A.germ d" using A.germ_surj[OF XY(2)] by blast
    ultimately have "X = A.germ c" "Y = A.germ d" by auto
    then show ?thesis by (simp add: A.add_germ B.add_germ)
  qed
  have ht: "stalk_map (A.mult_stalk X Y) = B.mult_stalk (stalk_map X) (stalk_map Y)"
    if XY: "X \<in> A.carrier_stalk" "Y \<in> A.carrier_stalk" for X Y
  proof -
    obtain c where "X = A.germ c" using A.germ_surj[OF XY(1)] by blast
    moreover obtain d where "Y = A.germ d" using A.germ_surj[OF XY(2)] by blast
    ultimately have "X = A.germ c" "Y = A.germ d" by auto
    then show ?thesis by (simp add: A.mult_germ B.mult_germ)
  qed
  have hz: "stalk_map (A.zero_stalk U) = B.zero_stalk U"
    by (simp add: A.zero_germ[OF assms] B.zero_germ[OF assms])
  have ho: "stalk_map (A.one_stalk U) = B.one_stalk U"
    by (simp add: A.one_germ[OF assms] B.one_germ[OF assms])
  have hom: "ring_homomorphism stalk_map
      A.carrier_stalk A.add_stalk A.mult_stalk (A.zero_stalk U) (A.one_stalk U)
      B.carrier_stalk B.add_stalk B.mult_stalk (B.zero_stalk U) (B.one_stalk U)"
    using mp RA.ring_axioms RB.ring_axioms
      RA.additive.group_axioms RB.additive.group_axioms
      RA.additive.monoid_axioms RB.additive.monoid_axioms
      RA.multiplicative.monoid_axioms RB.multiplicative.monoid_axioms ha hz ht ho
    unfolding Ring_Theory.ring_homomorphism_def Group_Theory.group_homomorphism_def
      Group_Theory.monoid_homomorphism_def Group_Theory.monoid_homomorphism_axioms_def
    by blast
  have bij: "bij_betw stalk_map A.carrier_stalk B.carrier_stalk"
    unfolding bij_betw_def
  proof
    show "inj_on stalk_map A.carrier_stalk"
    proof (rule inj_onI)
      fix X Y assume XY: "X \<in> A.carrier_stalk" "Y \<in> A.carrier_stalk"
        and eq: "stalk_map X = stalk_map Y"
      obtain c where c: "X = A.germ c" using A.germ_surj[OF XY(1)] by blast
      obtain d where d: "Y = A.germ d" using A.germ_surj[OF XY(2)] by blast
      note cd = c d
      then have "c = d" using eq B.germ_inj by simp
      then show "X = Y" using cd by simp
    qed
    show "stalk_map ` A.carrier_stalk = B.carrier_stalk"
    proof
      show "stalk_map ` A.carrier_stalk \<subseteq> B.carrier_stalk"
        using mp by (auto simp: Set_Theory.map_def)
      show "B.carrier_stalk \<subseteq> stalk_map ` A.carrier_stalk"
      proof
        fix Y assume "Y \<in> B.carrier_stalk"
        then obtain c where "Y = B.germ c" by (blast elim: B.germ_surj)
        then have "Y = stalk_map (A.germ c)" by simp
        then show "Y \<in> stalk_map ` A.carrier_stalk" using A.germ_in by blast
      qed
    qed
  qed
  show ?thesis
    by (intro ring_isomorphism.intro bijective_map.intro bijective.intro hom mp bij)
qed

end

section \<open>The two concrete stalks\<close>

abbreviation pcst :: "'x \<Rightarrow> 'r \<Rightarrow> ('x \<Rightarrow> 'r)" where
  "pcst x c \<equiv> cut (\<lambda>_. c) {x}"

lemma sec_pt_eq: "(sec {x} :: ('x \<Rightarrow> 'r) set) = range (pcst x)"
proof
  show "(sec {x} :: ('x \<Rightarrow> 'r) set) \<subseteq> range (pcst x)"
  proof
    fix f :: "'x \<Rightarrow> 'r" assume "f \<in> sec {x}"
    then have "f = pcst x (f x)" by (auto simp: fun_eq_iff cut_def sec_def)
    then show "f \<in> range (pcst x)" by (rule range_eqI)
  qed
  show "range (pcst x) \<subseteq> (sec {x} :: ('x \<Rightarrow> 'r) set)"
    using sec_constant by auto
qed

lemma fsec_pt_eq: "(fsec {x} :: ('x \<Rightarrow> 'r) set) = range (pcst x)"
proof
  show "(fsec {x} :: ('x \<Rightarrow> 'r) set) \<subseteq> range (pcst x)"
  proof
    fix f :: "'x \<Rightarrow> 'r" assume "f \<in> fsec {x}"
    then have "f = pcst x (f x)" by (auto simp: fun_eq_iff cut_def fsec_def)
    then show "f \<in> range (pcst x)" by (rule range_eqI)
  qed
  show "range (pcst x) \<subseteq> (fsec {x} :: ('x \<Rightarrow> 'r) set)"
    by auto
qed

lemma pcst_inj: "pcst x c = pcst x d \<Longrightarrow> c = d"
  by (drule fun_cong[of _ _ x]) simp

lemma pcst_add: "sadd {x} (pcst x c) (pcst x d) = pcst x (c + d)"
  by (auto simp: sadd_def cut_def fun_eq_iff)
lemma pcst_mult: "smul {x} (pcst x c) (pcst x d) = pcst x (c * d)"
  by (auto simp: smul_def cut_def fun_eq_iff)
lemma pcst_zero: "szero {x} = pcst x 0"
  by (simp add: szero_def)
lemma pcst_one: "sone {x} = pcst x 1"
  by (simp add: sone_def)

lemma bounded_pstalk:
  "pstalk (UNIV :: 'x set) (\<lambda>U. True) (sec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r::ring_1) set)
      srho (\<lambda>x. undefined) sadd smul szero sone {U. x \<in> U} x (pcst x)"
  apply (intro pstalk.intro stalk.intro direct_lim.intro bounded_range_sheaf
      direct_lim_axioms.intro stalk_axioms.intro pstalk_axioms.intro)
  subgoal by simp
  subgoal for U V by (rule bexI[of _ "U \<inter> V"]) auto
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (rule sec_pt_eq)
  subgoal by (rule pcst_inj)
  subgoal by (rule pcst_add)
  subgoal by (rule pcst_mult)
  subgoal by (rule pcst_zero)
  subgoal by (rule pcst_one)
  done

lemma all_functions_pstalk:
  "pstalk (UNIV :: 'x set) (\<lambda>U. True) (fsec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r::ring_1) set)
      frho (\<lambda>x. undefined) sadd smul szero sone {U. x \<in> U} x (pcst x)"
  apply (intro pstalk.intro stalk.intro direct_lim.intro all_functions_sheaf
      direct_lim_axioms.intro stalk_axioms.intro pstalk_axioms.intro)
  subgoal by simp
  subgoal for U V by (rule bexI[of _ "U \<inter> V"]) auto
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (rule fsec_pt_eq)
  subgoal by (rule pcst_inj)
  subgoal by (rule pcst_add)
  subgoal by (rule pcst_mult)
  subgoal by (rule pcst_zero)
  subgoal by (rule pcst_one)
  done

section \<open>The same statement with the AFP's own induced maps on stalks\<close>

text \<open>The inclusion, together with the identity map of the space, is a morphism of ringed
spaces in the sense of the AFP entry, from the space with all functions to the space with
bounded-range functions.\<close>

lemma identity_UNIV: "identity (UNIV :: 'a set) = (\<lambda>x. x)"
  by (auto simp: restrict_def)

lemma identity_UNIV_vimage: "identity (UNIV :: 'a set) -` V = V"
  by (simp add: identity_UNIV)

lemma identity_continuous:
  "continuous_map (UNIV :: 'x set) (\<lambda>U. True) (UNIV :: 'x set) (\<lambda>U. True) (identity UNIV)"
  by unfold_locales auto

lemma im_identity_eqs:
  "im_sheaf.im_sheaf (UNIV :: 'x set) (fsec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r::ring_1) set) (identity UNIV) = fsec"
  "im_sheaf.im_sheaf_morphisms (UNIV :: 'x set)
      (frho :: 'x set \<Rightarrow> 'x set \<Rightarrow> ('x \<Rightarrow> 'r) \<Rightarrow> ('x \<Rightarrow> 'r)) (identity UNIV) = frho"
  "im_sheaf.add_im_sheaf (UNIV :: 'x set)
      (sadd :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r) \<Rightarrow> ('x \<Rightarrow> 'r) \<Rightarrow> ('x \<Rightarrow> 'r)) (identity UNIV) = sadd"
  "im_sheaf.mult_im_sheaf (UNIV :: 'x set)
      (smul :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r) \<Rightarrow> ('x \<Rightarrow> 'r) \<Rightarrow> ('x \<Rightarrow> 'r)) (identity UNIV) = smul"
  "im_sheaf.zero_im_sheaf (UNIV :: 'x set)
      (szero :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r)) (identity UNIV) = szero"
  "im_sheaf.one_im_sheaf (UNIV :: 'x set)
      (sone :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r)) (identity UNIV) = sone"
proof -
  interpret im: im_sheaf "UNIV :: 'x set" "\<lambda>U. True" "fsec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r) set"
    frho "\<lambda>x. undefined" sadd smul szero sone "UNIV :: 'x set" "\<lambda>U. True" "identity UNIV"
    by (intro im_sheaf.intro all_functions_sheaf identity_continuous)
  show "im.im_sheaf = fsec" "im.im_sheaf_morphisms = frho" "im.add_im_sheaf = sadd"
    "im.mult_im_sheaf = smul" "im.zero_im_sheaf = szero" "im.one_im_sheaf = sone"
    by (simp_all add: fun_eq_iff im.im_sheaf_def im.im_sheaf_morphisms_def im.add_im_sheaf_def
        im.mult_im_sheaf_def im.zero_im_sheaf_def im.one_im_sheaf_def identity_UNIV_vimage)
qed

lemma inclusion_morphism_ringed_spaces:
  "morphism_ringed_spaces (UNIV :: 'x set) (\<lambda>U. True)
      (fsec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r::ring_1) set) frho (\<lambda>x. undefined) sadd smul szero sone
      (UNIV :: 'x set) (\<lambda>U. True)
      (sec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r) set) srho (\<lambda>x. undefined) sadd smul szero sone
      (identity UNIV) (\<lambda>U. identity (sec U))"
  by (intro morphism_ringed_spaces.intro morphism_ringed_spaces_axioms.intro im_sheaf.intro
      all_functions_sheaf identity_continuous ringed_space.intro bounded_range_sheaf)
     (simp add: im_identity_eqs inclusion_morphism)

context
  fixes x :: "'x" and dummy :: "'r::ring_1"
begin

interpretation P: pstalk_pair "UNIV :: 'x set" "\<lambda>U. True"
  "sec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r) set" srho "\<lambda>x. undefined" sadd smul szero sone
  "{U. x \<in> U}" x "pcst x"
  "fsec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r) set" frho "\<lambda>x. undefined" sadd smul szero sone "pcst x"
  by (intro pstalk_pair.intro bounded_pstalk all_functions_pstalk)

lemma inclusion_stalk_iso:
  "\<exists>\<psi>. (\<forall>V. x \<in> V \<longrightarrow> ring_isomorphism \<psi>
        P.A.carrier_stalk P.A.add_stalk P.A.mult_stalk (P.A.zero_stalk V) (P.A.one_stalk V)
        P.B.carrier_stalk P.B.add_stalk P.B.mult_stalk (P.B.zero_stalk V) (P.B.one_stalk V))
    \<and> (\<forall>U s. x \<in> U \<longrightarrow> s \<in> (sec U :: ('x \<Rightarrow> 'r) set) \<longrightarrow>
        \<psi> (P.A.class_of U s) = P.B.class_of U (identity (sec U) s))"
proof (intro exI[of _ P.stalk_map] conjI allI impI)
  fix V assume "x \<in> V"
  then show "ring_isomorphism P.stalk_map
        P.A.carrier_stalk P.A.add_stalk P.A.mult_stalk (P.A.zero_stalk V) (P.A.one_stalk V)
        P.B.carrier_stalk P.B.add_stalk P.B.mult_stalk (P.B.zero_stalk V) (P.B.one_stalk V)"
    by (intro P.stalk_map_iso) simp
next
  fix U and s :: "'x \<Rightarrow> 'r" assume U: "x \<in> U" and s: "s \<in> sec U"
  show "P.stalk_map (P.A.class_of U s) = P.B.class_of U (identity (sec U) s)"
  proof (rule P.stalk_map_class)
    show "U \<in> {U. x \<in> U}" using U by simp
    show "s \<in> sec U" by (rule s)
    show "identity (sec U) s \<in> fsec U" using s by (simp add: sec_in_fsec)
    show "frho U {x} (identity (sec U) s) = pcst x c" if "srho U {x} s = pcst x c" for c
      using that s by (simp add: sec_in_fsec)
  qed
qed

interpretation M: ind_mor_btw_stalks "UNIV :: 'x set" "\<lambda>U. True"
  "fsec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r) set" frho "\<lambda>x. undefined" sadd smul szero sone
  "UNIV :: 'x set" "\<lambda>U. True"
  "sec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r) set" srho "\<lambda>x. undefined" sadd smul szero sone
  "identity UNIV" "\<lambda>U. identity (sec U)" x
  by (intro ind_mor_btw_stalks.intro inclusion_morphism_ringed_spaces
      ind_mor_btw_stalks_axioms.intro) simp

text \<open>The AFP's induced map on stalks is the map constructed above.\<close>

lemma induced_morphism_eq_stalk_map: "M.induced_morphism = P.stalk_map"
proof (rule ext)
  fix C
  show "M.induced_morphism C = P.stalk_map C"
  proof (cases "C \<in> P.A.carrier_stalk")
    case True
    obtain c where c: "C = P.A.germ c" using P.A.germ_surj[OF True] by blast
    have mem: "({x}, pcst x c) \<in> C"
      unfolding c P.A.germ_def by (rule P.A.class_self) (simp_all add: sec_constant)
    have "M.induced_morphism C = P.B.class_of {x} (pcst x c)"
      using M.induced_morphism_eval[of C "({x}, pcst x c)"] True mem
      by (simp add: sec_constant identity_UNIV_vimage)
    then show ?thesis by (simp add: c P.B.germ_def)
  next
    case False
    then show ?thesis by (simp add: M.induced_morphism_def P.stalk_map_def)
  qed
qed

lemma induced_morphism_iso:
  assumes "x \<in> V"
  shows "ring_isomorphism M.induced_morphism
        P.A.carrier_stalk P.A.add_stalk P.A.mult_stalk (P.A.zero_stalk V) (P.A.one_stalk V)
        P.B.carrier_stalk P.B.add_stalk P.B.mult_stalk (P.B.zero_stalk V) (P.B.one_stalk V)"
  unfolding induced_morphism_eq_stalk_map using assms by (intro P.stalk_map_iso) simp

end

section \<open>The counterexample to Hartshorne II.1.1 for the AFP predicate\<close>

theorem stalkwise_iso_not_iso:
  "sheaf_of_rings (UNIV :: coeff set) (\<lambda>U. True)
       (sec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set)
       srho (\<lambda>x. undefined) sadd smul szero sone
   \<and> sheaf_of_rings (UNIV :: coeff set) (\<lambda>U. True)
       (fsec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set)
       frho (\<lambda>x. undefined) sadd smul szero sone
   \<and> morphism_sheaves_of_rings (UNIV :: coeff set) (\<lambda>U. True)
       (sec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) srho (\<lambda>x. undefined) sadd smul szero sone
       fsec frho (\<lambda>x. undefined) sadd smul szero sone
       (\<lambda>U. identity (sec U))
   \<and> (\<forall>x::coeff. \<exists>\<psi>.
        (\<forall>V. x \<in> V \<longrightarrow> ring_isomorphism \<psi>
          (stalk.carrier_stalk (\<lambda>U. True) (sec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) srho x)
          (stalk.add_stalk sec srho sadd {U. x \<in> U})
          (stalk.mult_stalk sec srho smul {U. x \<in> U})
          (stalk.zero_stalk sec srho szero {U. x \<in> U} V)
          (stalk.one_stalk sec srho sone {U. x \<in> U} V)
          (stalk.carrier_stalk (\<lambda>U. True) (fsec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) frho x)
          (stalk.add_stalk fsec frho sadd {U. x \<in> U})
          (stalk.mult_stalk fsec frho smul {U. x \<in> U})
          (stalk.zero_stalk fsec frho szero {U. x \<in> U} V)
          (stalk.one_stalk fsec frho sone {U. x \<in> U} V))
        \<and> (\<forall>U s. x \<in> U \<longrightarrow> s \<in> (sec U :: (coeff \<Rightarrow> coeff) set) \<longrightarrow>
            \<psi> (direct_lim.class_of sec srho {U. x \<in> U} U s) =
            direct_lim.class_of fsec frho {U. x \<in> U} U (identity (sec U) s)))
   \<and> \<not> iso_sheaves_of_rings (UNIV :: coeff set) (\<lambda>U. True)
       (sec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) srho (\<lambda>x. undefined) sadd smul szero sone
       fsec frho (\<lambda>x. undefined) sadd smul szero sone
       (\<lambda>U. identity (sec U))"
  using bounded_range_sheaf all_functions_sheaf inclusion_morphism
    inclusion_stalk_iso inclusion_not_iso
  by blast

text \<open>The same counterexample in the entry's own vocabulary for ringed spaces: a morphism of
ringed spaces whose underlying map is a homeomorphism (the identity) and whose induced maps
on stalks, as defined in the entry, are all ring isomorphisms, but whose map of sheaves is not
an isomorphism.\<close>

theorem stalkwise_iso_not_iso_ringed_spaces:
  "morphism_ringed_spaces (UNIV :: coeff set) (\<lambda>U. True)
       (fsec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) frho (\<lambda>x. undefined) sadd smul szero sone
       (UNIV :: coeff set) (\<lambda>U. True)
       (sec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) srho (\<lambda>x. undefined) sadd smul szero sone
       (identity UNIV) (\<lambda>U. identity (sec U))
   \<and> homeomorphism (UNIV :: coeff set) (\<lambda>U. True) (UNIV :: coeff set) (\<lambda>U. True) (identity UNIV)
   \<and> (\<forall>(x::coeff) V. x \<in> V \<longrightarrow> ring_isomorphism
          (ind_mor_btw_stalks.induced_morphism (UNIV :: coeff set) (\<lambda>U. True)
             (fsec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) frho
             (\<lambda>U. True) (sec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) srho
             (identity UNIV) (\<lambda>U. identity (sec U)) x)
          (stalk.carrier_stalk (\<lambda>U. True) (sec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) srho x)
          (stalk.add_stalk sec srho sadd {U. x \<in> U})
          (stalk.mult_stalk sec srho smul {U. x \<in> U})
          (stalk.zero_stalk sec srho szero {U. x \<in> U} V)
          (stalk.one_stalk sec srho sone {U. x \<in> U} V)
          (stalk.carrier_stalk (\<lambda>U. True) (fsec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) frho x)
          (stalk.add_stalk fsec frho sadd {U. x \<in> U})
          (stalk.mult_stalk fsec frho smul {U. x \<in> U})
          (stalk.zero_stalk fsec frho szero {U. x \<in> U} V)
          (stalk.one_stalk fsec frho sone {U. x \<in> U} V))
   \<and> \<not> iso_sheaves_of_rings (UNIV :: coeff set) (\<lambda>U. True)
       (sec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) srho (\<lambda>x. undefined) sadd smul szero sone
       (im_sheaf.im_sheaf UNIV (fsec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) (identity UNIV))
       (im_sheaf.im_sheaf_morphisms UNIV frho (identity UNIV)) (\<lambda>x. undefined)
       (im_sheaf.add_im_sheaf UNIV sadd (identity UNIV))
       (im_sheaf.mult_im_sheaf UNIV smul (identity UNIV))
       (im_sheaf.zero_im_sheaf UNIV szero (identity UNIV))
       (im_sheaf.one_im_sheaf UNIV sone (identity UNIV))
       (\<lambda>U. identity (sec U))"
proof (intro conjI allI impI)
  show "morphism_ringed_spaces (UNIV :: coeff set) (\<lambda>U. True)
       (fsec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) frho (\<lambda>x. undefined) sadd smul szero sone
       (UNIV :: coeff set) (\<lambda>U. True)
       (sec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) srho (\<lambda>x. undefined) sadd smul szero sone
       (identity UNIV) (\<lambda>U. identity (sec U))"
    by (rule inclusion_morphism_ringed_spaces)
  have "topological_space (UNIV :: coeff set) (\<lambda>U. True)"
    by unfold_locales auto
  then show "homeomorphism (UNIV :: coeff set) (\<lambda>U. True) (UNIV :: coeff set) (\<lambda>U. True)
      (identity UNIV)"
    by (rule topological_space.id_is_homeomorphism)
  show "\<not> iso_sheaves_of_rings (UNIV :: coeff set) (\<lambda>U. True)
       (sec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) srho (\<lambda>x. undefined) sadd smul szero sone
       (im_sheaf.im_sheaf UNIV (fsec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) (identity UNIV))
       (im_sheaf.im_sheaf_morphisms UNIV frho (identity UNIV)) (\<lambda>x. undefined)
       (im_sheaf.add_im_sheaf UNIV sadd (identity UNIV))
       (im_sheaf.mult_im_sheaf UNIV smul (identity UNIV))
       (im_sheaf.zero_im_sheaf UNIV szero (identity UNIV))
       (im_sheaf.one_im_sheaf UNIV sone (identity UNIV))
       (\<lambda>U. identity (sec U))"
    unfolding im_identity_eqs by (rule inclusion_not_iso)
qed (rule induced_morphism_iso)

text \<open>A construction-independent existence statement: the witnesses occur only in the
proof. The ambient point and section types remain fixed, as required in HOL. The stalk
maps here are the AFP's own induced morphisms.\<close>

theorem exists_stalkwise_iso_not_iso:
  "\<exists>S is_open (F :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set) rho G sigma b add mult zero one phi.
    morphism_ringed_spaces S is_open
       G sigma b add mult zero one
       S is_open
       F rho b add mult zero one
       (identity S) phi
   \<and> homeomorphism S is_open S is_open (identity S)
   \<and> (\<forall>(x::coeff) V. is_open V \<longrightarrow> x \<in> V \<longrightarrow> ring_isomorphism
          (ind_mor_btw_stalks.induced_morphism S is_open
             G sigma
             is_open F rho
             (identity S) phi x)
          (stalk.carrier_stalk is_open F rho x)
          (stalk.add_stalk F rho add {U. is_open U \<and> x \<in> U})
          (stalk.mult_stalk F rho mult {U. is_open U \<and> x \<in> U})
          (stalk.zero_stalk F rho zero {U. is_open U \<and> x \<in> U} V)
          (stalk.one_stalk F rho one {U. is_open U \<and> x \<in> U} V)
          (stalk.carrier_stalk is_open G sigma x)
          (stalk.add_stalk G sigma add {U. is_open U \<and> x \<in> U})
          (stalk.mult_stalk G sigma mult {U. is_open U \<and> x \<in> U})
          (stalk.zero_stalk G sigma zero {U. is_open U \<and> x \<in> U} V)
          (stalk.one_stalk G sigma one {U. is_open U \<and> x \<in> U} V))
   \<and> \<not> iso_sheaves_of_rings S is_open
       F rho b add mult zero one
       (im_sheaf.im_sheaf S G (identity S))
       (im_sheaf.im_sheaf_morphisms S sigma (identity S)) b
       (im_sheaf.add_im_sheaf S add (identity S))
       (im_sheaf.mult_im_sheaf S mult (identity S))
       (im_sheaf.zero_im_sheaf S zero (identity S))
       (im_sheaf.one_im_sheaf S one (identity S))
       phi"
  apply (rule exI[of _ "UNIV :: coeff set"])
  apply (rule exI[of _ "\<lambda>U. True"])
  apply (rule exI[of _ "sec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set"])
  apply (rule exI[of _ "srho"])
  apply (rule exI[of _ "fsec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set"])
  apply (rule exI[of _ "frho"])
  apply (rule exI[of _ "\<lambda>x. undefined"])
  apply (rule exI[of _ "sadd"])
  apply (rule exI[of _ "smul"])
  apply (rule exI[of _ "szero"])
  apply (rule exI[of _ "sone"])
  apply (rule exI[of _ "\<lambda>U. identity (sec U)"])
  using stalkwise_iso_not_iso_ringed_spaces by simp

end
