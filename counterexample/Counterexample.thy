theory Counterexample
  imports "Grothendieck_Schemes.Scheme" Small_Range
begin

notation plus (infixl "+" 65)
notation minus (infixl "-" 65)
unbundle uminus_syntax
unbundle cardinal_syntax

lemma sections_ring:
  "Ring_Theory.ring (sec U :: ('x \<Rightarrow> 'r::ring_1) set)
    (sadd U) (smul U) (szero U) (sone U)"
proof -
  have am: "Group_Theory.monoid (sec U :: ('x \<Rightarrow> 'r) set) (sadd U) (szero U)"
  proof (unfold_locales)
    show "\<And>a b. a\<in>sec U \<Longrightarrow> b\<in>sec U \<Longrightarrow> sadd U a b\<in>(sec U :: ('x\<Rightarrow>'r)set)"
      by (rule sec_sadd)
    show "szero U\<in>(sec U :: ('x\<Rightarrow>'r)set)" by (rule sec_szero)
    show "\<And>a b c. a\<in>sec U \<Longrightarrow> b\<in>sec U \<Longrightarrow> c\<in>sec U \<Longrightarrow>
      sadd U (sadd U a b) c = (sadd U a (sadd U b c) :: 'x\<Rightarrow>'r)"
      by (auto simp: sadd_def cut_def fun_eq_iff add.assoc)
    show "\<And>a. a\<in>sec U \<Longrightarrow> sadd U (szero U) a = (a :: 'x\<Rightarrow>'r)"
      by (auto simp: sadd_def szero_def cut_def fun_eq_iff dest: sec_outside)
    show "\<And>a. a\<in>sec U \<Longrightarrow> sadd U a (szero U) = (a :: 'x\<Rightarrow>'r)"
      by (auto simp: sadd_def szero_def cut_def fun_eq_iff dest: sec_outside)
  qed
  interpret am: Group_Theory.monoid "sec U :: ('x \<Rightarrow> 'r) set" "sadd U" "szero U"
    by fact
  have inv: "am.invertible f" if "f \<in> sec U" for f
  proof (rule am.invertibleI[where v="sneg U f"])
    show "sadd U f (sneg U f) = szero U"
      by (auto simp: sadd_def sneg_def szero_def cut_def fun_eq_iff)
    show "sadd U (sneg U f) f = szero U"
      by (auto simp: sadd_def sneg_def szero_def cut_def fun_eq_iff)
    show "f\<in>sec U" by fact
    show "sneg U f\<in>sec U" by (rule sec_sneg[OF that])
  qed
  have ag: "Group_Theory.abelian_group (sec U :: ('x \<Rightarrow> 'r) set) (sadd U) (szero U)"
    by (intro Group_Theory.abelian_group.intro Group_Theory.group.intro
        Group_Theory.group_axioms.intro Group_Theory.commutative_monoid.intro
        Group_Theory.commutative_monoid_axioms.intro am)
       (use inv in \<open>auto simp: sadd_def cut_def fun_eq_iff add.commute\<close>)
  have mm: "Group_Theory.monoid (sec U :: ('x \<Rightarrow> 'r) set) (smul U) (sone U)"
  proof (unfold_locales)
    show "\<And>a b. a\<in>sec U \<Longrightarrow> b\<in>sec U \<Longrightarrow> smul U a b\<in>(sec U :: ('x\<Rightarrow>'r)set)"
      by (rule sec_smul)
    show "sone U\<in>(sec U :: ('x\<Rightarrow>'r)set)" by (rule sec_sone)
    show "\<And>a b c. a\<in>sec U \<Longrightarrow> b\<in>sec U \<Longrightarrow> c\<in>sec U \<Longrightarrow>
      smul U (smul U a b) c = (smul U a (smul U b c) :: 'x\<Rightarrow>'r)"
      by (auto simp: smul_def cut_def fun_eq_iff mult.assoc)
    show "\<And>a. a\<in>sec U \<Longrightarrow> smul U (sone U) a = (a :: 'x\<Rightarrow>'r)"
      by (auto simp: smul_def sone_def cut_def fun_eq_iff dest: sec_outside)
    show "\<And>a. a\<in>sec U \<Longrightarrow> smul U a (sone U) = (a :: 'x\<Rightarrow>'r)"
      by (auto simp: smul_def sone_def cut_def fun_eq_iff dest: sec_outside)
  qed
  show ?thesis
    by (intro Ring_Theory.ring.intro Ring_Theory.ring_axioms.intro ag mm)
       (auto simp: sadd_def smul_def cut_def fun_eq_iff algebra_simps)
qed

lemma srho_map:
  assumes "V \<subseteq> U"
  shows "Set_Theory.map (srho U V :: ('x \<Rightarrow> 'r) \<Rightarrow> ('x \<Rightarrow> 'r)) (sec U) (sec V)"
  using assms sec_cut
  by (auto simp: Set_Theory.map_def srho_def PiE_def extensional_def cut_def)

lemma srho_hom:
  assumes "V \<subseteq> U"
  shows "Ring_Theory.ring_homomorphism (srho U V :: ('x \<Rightarrow> 'r::ring_1) \<Rightarrow> ('x \<Rightarrow> 'r))
      (sec U) (sadd U) (smul U) (szero U) (sone U)
      (sec V) (sadd V) (smul V) (szero V) (sone V)"
proof -
  interpret src: Ring_Theory.ring "sec U :: ('x \<Rightarrow> 'r) set" "sadd U" "smul U" "szero U" "sone U"
    by (rule sections_ring)
  interpret tgt: Ring_Theory.ring "sec V :: ('x \<Rightarrow> 'r) set" "sadd V" "smul V" "szero V" "sone V"
    by (rule sections_ring)
  have hm: "Set_Theory.map (srho U V :: ('x\<Rightarrow>'r)\<Rightarrow>('x\<Rightarrow>'r)) (sec U) (sec V)"
    by (rule srho_map[OF assms])
  have ha: "srho U V (sadd U f g) = sadd V (srho U V f) (srho U V g)"
    if "f\<in>sec U" "g\<in>sec U" for f g :: "'x\<Rightarrow>'r"
    using assms that
    by (simp only: srho_apply[OF sec_sadd[OF that]] srho_apply[OF that(1)] srho_apply[OF that(2)])
       (auto simp: sadd_def cut_def fun_eq_iff)
  have hz: "srho U V (szero U) = (szero V :: 'x\<Rightarrow>'r)"
    using assms by (simp only: srho_apply[OF sec_szero])
      (auto simp: szero_def cut_def fun_eq_iff)
  have ht: "srho U V (smul U f g) = smul V (srho U V f) (srho U V g)"
    if "f\<in>sec U" "g\<in>sec U" for f g :: "'x\<Rightarrow>'r"
    using assms that
    by (simp only: srho_apply[OF sec_smul[OF that]] srho_apply[OF that(1)] srho_apply[OF that(2)])
       (auto simp: smul_def cut_def fun_eq_iff)
  have ho: "srho U V (sone U) = (sone V :: 'x\<Rightarrow>'r)"
    using assms by (simp only: srho_apply[OF sec_sone])
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

lemma sec_empty: "sec {} = {\<lambda>x. undefined}"
  by (auto simp: sec_def extensional_def fun_eq_iff)

lemma bounded_range_presheaf:
  "presheaf_of_rings (UNIV :: 'x set) (\<lambda>U. True) (sec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r::ring_1) set)
      srho (\<lambda>x. undefined) sadd smul szero sone"
proof (intro presheaf_of_rings.intro presheaf_of_rings_axioms.intro)
  show "Topological_Space.topological_space (UNIV :: 'x set) (\<lambda>U. True)"
    by unfold_locales auto
  show "\<And>U V. V \<subseteq> U \<Longrightarrow>
       ring_homomorphism (srho U V :: ('x \<Rightarrow> 'r) \<Rightarrow> ('x \<Rightarrow> 'r))
       (sec U) (sadd U) (smul U) (szero U) (sone U)
       (sec V) (sadd V) (smul V) (szero V) (sone V)"
    by (rule srho_hom)
  show "sec {} = {\<lambda>x::'x. undefined::'r}" by (rule sec_empty)
  show "\<And>U f. f \<in> sec U \<Longrightarrow> srho U U f = (f :: 'x \<Rightarrow> 'r)"
    by (simp add: cut_sec)
  show "\<And>U V W f. V \<subseteq> U \<Longrightarrow> W \<subseteq> V \<Longrightarrow> f \<in> sec U \<Longrightarrow>
        srho U W f = (srho V W \<circ> srho U V) (f :: 'x \<Rightarrow> 'r)"
    by (auto simp: sec_cut cut_def fun_eq_iff)
qed

lemma bounded_range_sheaf:
  "sheaf_of_rings (UNIV :: 'x set) (\<lambda>U. True) (sec :: 'x set \<Rightarrow> ('x \<Rightarrow> 'r::ring_1) set)
      srho (\<lambda>x. undefined) sadd smul szero sone"
proof (intro sheaf_of_rings.intro sheaf_of_rings_axioms.intro bounded_range_presheaf)
  fix U I V f
  assume cover: "open_cover_of_open_subset (UNIV :: 'x set) (\<lambda>U. True) U I V"
    and sub: "\<And>i. i\<in>I \<Longrightarrow> V i \<subseteq> U"
    and f: "f \<in> (sec U :: ('x \<Rightarrow> 'r) set)"
    and zero: "\<And>i. i\<in>I \<Longrightarrow> srho U (V i) f = szero (V i)"
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
      have "(srho U (V i) f) x = szero (V i) x" using zero[OF i(1)] by simp
      then show ?thesis using f i True by (simp add: szero_def)
    next
      case False
      then show ?thesis using f sec_outside by (simp add: szero_def cut_def)
    qed
  qed
next
  fix U I V s
  assume cover: "open_cover_of_open_subset (UNIV :: 'x set) (\<lambda>U. True) U I V"
    and sections: "\<forall>i. i\<in>I \<longrightarrow> V i \<subseteq> U \<and> s i \<in> (sec (V i) :: ('x \<Rightarrow> 'r) set)"
    and compat: "\<And>i j. i\<in>I \<Longrightarrow> j\<in>I \<Longrightarrow>
      srho (V i) (V i \<inter> V j) (s i) = srho (V j) (V i \<inter> V j) (s j)"
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
  have small_union: "csmall (\<Union>i\<in>I. s i ` V i)"
    by (intro csmall_UNION) (use sections in \<open>auto intro: sec_small\<close>)
  have small_t: "csmall (t ` U)"
    by (rule csmall_mono[OF _ small_union])
       (use pick_index in \<open>auto simp: t_def\<close>)
  have t: "t \<in> (sec U :: ('x \<Rightarrow> 'r) set)"
    using small_t unfolding t_def sec_def by simp
  have cuts: "srho U (V i) t = s i" if "i\<in>I" for i
  proof (rule ext)
    fix x
    have si: "s i \<in> sec (V i)" and sub: "V i \<subseteq> U" using sections that by auto
    show "srho U (V i) t x = s i x"
    proof (cases "x\<in>V i")
      case True
      then have xu: "x\<in>U" using sub by blast
      have ci: "pick_index x\<in>I" and xc: "x\<in>V (pick_index x)" using pick_index[OF xu] by auto
      have sc: "s (pick_index x)\<in>sec (V (pick_index x))" using sections ci by auto
      have "(srho (V i) (V i \<inter> V (pick_index x)) (s i)) x =
            (srho (V (pick_index x)) (V i \<inter> V (pick_index x)) (s (pick_index x))) x"
        using compat[OF that ci] by simp
      then have "s i x = s (pick_index x) x" using si sc True xc by simp
      then show ?thesis using t True xu by (simp add: t_def)
    next
      case False
      then show ?thesis using sec_outside[OF si False] t by (simp add: cut_def)
    qed
  qed
  show "\<exists>t. t \<in> (sec U :: ('x \<Rightarrow> 'r) set) \<and> (\<forall>i. i\<in>I \<longrightarrow> srho U (V i) t = s i)"
    using t cuts by blast
qed

text \<open>A fully concrete coefficient ring: all integer-valued functions on the reals.
Cantor's diagonal argument shows it has more than continuum many elements.\<close>
type_synonym coeff = "real \<Rightarrow> int"

lemma coeff_not_csmall: "\<not> csmall (UNIV :: coeff set)"
proof
  assume "csmall (UNIV :: coeff set)"
  then obtain g :: "real \<Rightarrow> coeff" where g: "surj g"
    unfolding csmall_def using card_of_ordLeq2[of "UNIV :: coeff set" "UNIV :: real set"] by auto
  define d :: coeff where "d x = g x x + 1" for x
  obtain x where dx: "d = g x" using surjD[OF g, of d] by blast
  have "g x x = g x x + 1" using fun_cong[OF dx, of x] by (simp add: d_def)
  then show False by simp
qed

lemma singleton_section: "cut (\<lambda>_. a) {a} \<in> (sec {a} :: ('a \<Rightarrow> 'a) set)"
  by (rule sec_constant)

lemma singleton_sections_compatible:
  "srho {a} ({a} \<inter> {b}) (cut (\<lambda>_. a) {a}) =
   srho {b} ({a} \<inter> {b}) (cut (\<lambda>_. b) {b})"
  by (auto simp: cut_def fun_eq_iff sec_constant)

lemma singleton_family_has_no_gluing:
  "\<not> (\<exists>t \<in> (sec UNIV :: (coeff \<Rightarrow> coeff) set).
    \<forall>a. srho UNIV {a} t = cut (\<lambda>_. a) {a})"
proof
  assume "\<exists>t \<in> (sec UNIV :: (coeff \<Rightarrow> coeff) set).
    \<forall>a. srho UNIV {a} t = cut (\<lambda>_. a) {a}"
  then obtain t where t: "t \<in> (sec UNIV :: (coeff \<Rightarrow> coeff) set)"
    and cutions: "\<And>a. srho UNIV {a} t = cut (\<lambda>_. a) {a}" by blast
  have tid: "t = id"
  proof (rule ext)
    fix a
    have "(srho UNIV {a} t) a = (cut (\<lambda>_. a) {a}) a" using cutions[of a] by simp
    then show "t a = id a" using t by simp
  qed
  have "csmall (UNIV :: coeff set)" using sec_small[OF t] by (simp add: tid)
  then show False using coeff_not_csmall by blast
qed


lemma singleton_cover:
  "\<Union>(range (\<lambda>a::coeff. {a})) = (UNIV :: coeff set)"
  by auto

lemma sections_comm_ring:
  "Comm_Ring.comm_ring (sec U :: ('x \<Rightarrow> 'r::comm_ring_1) set)
      (sadd U) (smul U) (szero U) (sone U)"
  by (intro Comm_Ring.comm_ring.intro sections_ring Comm_Ring.comm_ring_axioms.intro)
     (auto simp: smul_def fun_eq_iff mult.commute)

text \<open>The following theorem combines the original AFP sheaf predicate with an
explicit open cover and compatible local sections that have no global gluing.
The coefficient ring is concrete and no extra axioms are assumed.
This refutes equivalence of the AFP predicate with the ordinary sheaf condition;
it does not claim the AFP's particular structure sheaf of Spec is incorrect.\<close>

theorem counterexample_to_arbitrary_gluing:
  "sheaf_of_rings (UNIV :: coeff set) (\<lambda>U. True)
       (sec :: coeff set \<Rightarrow> (coeff \<Rightarrow> coeff) set)
       srho (\<lambda>x. undefined) sadd smul szero sone
   \<and> (\<Union>(range (\<lambda>a::coeff. {a})) = (UNIV :: coeff set))
   \<and> (\<forall>a::coeff. cut (\<lambda>_. a) {a} \<in> sec {a})
   \<and> (\<forall>a b::coeff.
       srho {a} ({a} \<inter> {b}) (cut (\<lambda>_. a) {a}) =
       srho {b} ({a} \<inter> {b}) (cut (\<lambda>_. b) {b}))
   \<and> \<not> (\<exists>t \<in> (sec UNIV :: (coeff \<Rightarrow> coeff) set).
       \<forall>a. srho UNIV {a} t = cut (\<lambda>_. a) {a})"
  using bounded_range_sheaf singleton_cover singleton_section
    singleton_sections_compatible singleton_family_has_no_gluing by blast

end
