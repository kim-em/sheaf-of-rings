theory Scheme_Counterexample
  imports Counterexample Point_Schemes BigRing
begin

text \<open>The bounded-range presheaf of the counterexample, with coefficients in the large
local ring \<open>bigring\<close>, satisfies the AFP locale \<open>scheme\<close> although a compatible
family on the cover by singletons has no gluing.\<close>

section \<open>Type-class rings as AFP rings\<close>

lemma class_ring: "Ring_Theory.ring (UNIV :: 'r::ring_1 set) (+) (*) 0 1"
proof -
  have am: "Group_Theory.monoid (UNIV :: 'r set) (+) 0"
    by unfold_locales (auto simp: add.assoc)
  interpret am: Group_Theory.monoid "UNIV :: 'r set" "(+)" 0 by fact
  have inv: "am.invertible f" for f
    by (rule am.invertibleI[where v="- f"]) auto
  have ag: "Group_Theory.abelian_group (UNIV :: 'r set) (+) 0"
    by (intro Group_Theory.abelian_group.intro Group_Theory.group.intro
        Group_Theory.group_axioms.intro Group_Theory.commutative_monoid.intro
        Group_Theory.commutative_monoid_axioms.intro am)
       (use inv in \<open>auto simp: add.commute\<close>)
  have mm: "Group_Theory.monoid (UNIV :: 'r set) (*) 1"
    by unfold_locales (auto simp: mult.assoc)
  show ?thesis
    by (intro Ring_Theory.ring.intro Ring_Theory.ring_axioms.intro ag mm)
       (auto simp: algebra_simps)
qed

lemma class_comm_ring: "Comm_Ring.comm_ring (UNIV :: 'r::comm_ring_1 set) (+) (*) 0 1"
  by (intro Comm_Ring.comm_ring.intro class_ring Comm_Ring.comm_ring_axioms.intro)
     (auto simp: mult.commute)

section \<open>Sections over a singleton\<close>

lemma eval_sec_iso:
  "ring_isomorphism (\<lambda>f\<in>(sec {x} :: ('x \<Rightarrow> 'r::ring_1) set). f x)
     (sec {x}) (sadd {x}) (smul {x}) (szero {x}) (sone {x}) UNIV (+) (*) 0 1"
proof (rule ring_isomorphismI)
  show "Ring_Theory.ring (sec {x} :: ('x \<Rightarrow> 'r) set) (sadd {x}) (smul {x}) (szero {x}) (sone {x})"
    by (rule sections_ring)
  show "Ring_Theory.ring (UNIV :: 'r set) (+) (*) 0 1" by (rule class_ring)
  show "(\<lambda>f\<in>(sec {x} :: ('x \<Rightarrow> 'r) set). f x) \<in> sec {x} \<rightarrow>\<^sub>E UNIV" by auto
  show "(\<lambda>f\<in>(sec {x} :: ('x \<Rightarrow> 'r) set). f x) (sadd {x} f g) =
        (\<lambda>f\<in>(sec {x} :: ('x \<Rightarrow> 'r) set). f x) f + (\<lambda>f\<in>(sec {x} :: ('x \<Rightarrow> 'r) set). f x) g"
    if "f \<in> sec {x}" "g \<in> sec {x}" for f g
    using that sec_sadd[OF that] by (simp add: sadd_def)
  show "(\<lambda>f\<in>(sec {x} :: ('x \<Rightarrow> 'r) set). f x) (smul {x} f g) =
        (\<lambda>f\<in>(sec {x} :: ('x \<Rightarrow> 'r) set). f x) f * (\<lambda>f\<in>(sec {x} :: ('x \<Rightarrow> 'r) set). f x) g"
    if "f \<in> sec {x}" "g \<in> sec {x}" for f g
    using that sec_smul[OF that] by (simp add: smul_def)
  show "(\<lambda>f\<in>(sec {x} :: ('x \<Rightarrow> 'r) set). f x) (szero {x}) = 0"
    by (simp add: szero_def sec_constant)
  show "(\<lambda>f\<in>(sec {x} :: ('x \<Rightarrow> 'r) set). f x) (sone {x}) = 1"
    by (simp add: sone_def sec_constant)
  have inj: "f = g" if "f \<in> sec {x}" "g \<in> sec {x}" "f x = g x" for f g :: "'x \<Rightarrow> 'r"
  proof (rule ext)
    fix y show "f y = g y"
      using that sec_outside[OF that(1), of y] sec_outside[OF that(2), of y] by (cases "y = x") auto
  qed
  have surj: "\<exists>f\<in>(sec {x} :: ('x \<Rightarrow> 'r) set). r = f x" for r
    by (rule bexI[where x="cut (\<lambda>_. r) {x}"]) (auto intro: sec_constant)
  show "bij_betw (\<lambda>f\<in>(sec {x} :: ('x \<Rightarrow> 'r) set). f x) (sec {x}) UNIV"
    unfolding bij_betw_def inj_on_def using inj surj by (auto simp: image_iff)
qed

section \<open>The big ring has a single prime ideal, and everything outside it is a unit\<close>

definition bm :: "bigring set" where "bm = {z. re z = 0}"

lemma bm_subgroup: "Group_Theory.subgroup bm (UNIV :: bigring set) (+) 0"
proof -
  interpret R: Ring_Theory.ring "UNIV :: bigring set" "(+)" "(*)" 0 1 by (rule class_ring)
  have m: "Group_Theory.monoid bm (+) (0 :: bigring)"
    by unfold_locales (auto simp: bm_def add.assoc)
  interpret m: Group_Theory.monoid bm "(+)" "0 :: bigring" by fact
  have "m.invertible u" if "u \<in> bm" for u
    by (rule m.invertibleI[where v="- u"]) (use that in \<open>auto simp: bm_def\<close>)
  then have g: "Group_Theory.group bm (+) (0 :: bigring)"
    by (intro Group_Theory.group.intro Group_Theory.group_axioms.intro m)
  show ?thesis
    by (intro Group_Theory.subgroup.intro Group_Theory.submonoid.intro
        Group_Theory.submonoid_axioms.intro g R.additive.monoid_axioms) (auto simp: bm_def)
qed

lemma bm_lideal: "lideal bm (UNIV :: bigring set) (+) (*) 0 1"
  by (intro lideal.intro subgroup_of_additive_group_of_ring.intro bm_subgroup class_ring
      lideal_axioms.intro) (auto simp: bm_def)

lemma lideal_proper_sub_bm:
  assumes "lideal I (UNIV :: bigring set) (+) (*) 0 1" "I \<noteq> UNIV"
  shows "I \<subseteq> bm"
proof
  fix z assume z: "z \<in> I"
  interpret I: lideal I "UNIV :: bigring set" "(+)" "(*)" 0 1 by fact
  show "z \<in> bm"
  proof (rule ccontr)
    assume "z \<notin> bm"
    then have "re z \<noteq> 0" by (simp add: bm_def)
    then obtain y where "y * z = 1" using bigring_unit by blast
    then have "1 \<in> I" using I.lideal[of y z] z by simp
    then show False using I.has_one_imp_equal assms(2) by blast
  qed
qed

lemma bm_proper: "bm \<noteq> (UNIV :: bigring set)"
proof
  assume "bm = (UNIV :: bigring set)"
  then have "(1 :: bigring) \<in> bm" by simp
  then show False by (simp add: bm_def)
qed

lemma bigring_pr_ideal_iff:
  "pr_ideal (UNIV :: bigring set) I (+) (*) 0 1 \<longleftrightarrow> I = bm"
proof
  assume "pr_ideal (UNIV :: bigring set) I (+) (*) 0 1"
  then interpret P: pr_ideal "UNIV :: bigring set" I "(+)" "(*)" 0 1 .
  have "lideal I (UNIV :: bigring set) (+) (*) 0 1"
    using P.ideal_axioms comm_ring.ideal_iff_lideal[OF class_comm_ring] by blast
  then have sub: "I \<subseteq> bm" using lideal_proper_sub_bm P.carrier_neq by blast
  have "z \<in> I" if "z \<in> bm" for z
  proof -
    have "z * z = 0" using that bigring_square_zero by (simp add: bm_def)
    moreover have "(0 :: bigring) \<in> I" by (rule P.additive.sub_unit_closed)
    ultimately show ?thesis using P.absorbent[of z z] by auto
  qed
  then show "I = bm" using sub by blast
next
  assume I: "I = bm"
  have id: "ideal bm (UNIV :: bigring set) (+) (*) 0 1"
    using bm_lideal comm_ring.ideal_iff_lideal[OF class_comm_ring] by blast
  show "pr_ideal (UNIV :: bigring set) I (+) (*) 0 1"
    unfolding I
  proof (intro pr_ideal.intro class_comm_ring id pr_ideal_axioms.intro)
    show "bm \<noteq> (UNIV :: bigring set)" by (rule bm_proper)
    show "x \<in> bm \<or> y \<in> bm" if "x * y \<in> bm" for x y :: bigring
      using that by (auto simp: bm_def)
  qed
qed

lemma bigring_spec: "comm_ring.spectrum (UNIV :: bigring set) (+) (*) 0 1 = {bm}"
  unfolding comm_ring.spectrum_def[OF class_comm_ring] using bigring_pr_ideal_iff by auto

lemma bigring_units: "s \<notin> bm \<Longrightarrow> \<exists>t. s * t = (1 :: bigring)"
  using bigring_unit[of s] by (auto simp: bm_def)

section \<open>The AFP scheme locale holds\<close>

theorem bounded_bigring_scheme:
  "scheme (UNIV :: bigring set) (\<lambda>U. True)
     (sec :: bigring set \<Rightarrow> (bigring \<Rightarrow> bigring) set)
     srho (\<lambda>x. undefined) sadd smul szero sone (UNIV :: bigring set)"
proof -
  interpret B: sheaf_of_rings "UNIV :: bigring set" "\<lambda>U. True"
      "sec :: bigring set \<Rightarrow> (bigring \<Rightarrow> bigring) set" srho "\<lambda>x. undefined" sadd smul szero sone
    by (rule bounded_range_sheaf)
  show ?thesis
  proof (rule B.open_points_scheme)
    fix x :: bigring
    show "True" by simp
    have H: "comm_ring (UNIV :: bigring set) (+) (*) 0 1
      \<and> comm_ring.spectrum (UNIV :: bigring set) (+) (*) 0 1 = {bm}
      \<and> (\<forall>s\<in>(UNIV :: bigring set). s \<notin> bm \<longrightarrow> (\<exists>t\<in>UNIV. s * t = 1))
      \<and> ring_isomorphism (\<lambda>f\<in>(sec {x} :: (bigring \<Rightarrow> bigring) set). f x)
            (sec {x}) (sadd {x}) (smul {x}) (szero {x}) (sone {x}) UNIV (+) (*) 0 1"
      using class_comm_ring bigring_spec bigring_units eval_sec_iso by auto
    show "\<exists>(R :: bigring set) addR multR zeroR oneR \<mm> g.
        comm_ring R addR multR zeroR oneR
      \<and> comm_ring.spectrum R addR multR zeroR oneR = {\<mm>}
      \<and> (\<forall>s\<in>R. s \<notin> \<mm> \<longrightarrow> (\<exists>t\<in>R. multR s t = oneR))
      \<and> ring_isomorphism g (sec {x} :: (bigring \<Rightarrow> bigring) set)
            (sadd {x}) (smul {x}) (szero {x}) (sone {x}) R addR multR zeroR oneR"
      by (rule exI[where x="UNIV :: bigring set"], rule exI[where x="(+)"],
          rule exI[where x="(*)"], rule exI[where x=0], rule exI[where x=1],
          rule exI[where x=bm],
          rule exI[where x="\<lambda>f\<in>(sec {x} :: (bigring \<Rightarrow> bigring) set). f x"])
         (rule H)
  qed
qed

text \<open>In particular it is a locally ringed space in the AFP sense.\<close>

theorem bounded_bigring_locally_ringed_space:
  "locally_ringed_space (UNIV :: bigring set) (\<lambda>U. True)
     (sec :: bigring set \<Rightarrow> (bigring \<Rightarrow> bigring) set)
     srho (\<lambda>x. undefined) sadd smul szero sone"
  by (rule scheme.axioms(1)[OF bounded_bigring_scheme])

section \<open>Failure of gluing\<close>

lemma bigring_singleton_family_has_no_gluing:
  "\<not> (\<exists>t \<in> (sec UNIV :: (bigring \<Rightarrow> bigring) set).
    \<forall>a. srho UNIV {a} t = cut (\<lambda>_. a) {a})"
proof
  assume "\<exists>t \<in> (sec UNIV :: (bigring \<Rightarrow> bigring) set).
    \<forall>a. srho UNIV {a} t = cut (\<lambda>_. a) {a}"
  then obtain t where t: "t \<in> (sec UNIV :: (bigring \<Rightarrow> bigring) set)"
    and cuts: "\<And>a. srho UNIV {a} t = cut (\<lambda>_. a) {a}" by blast
  have tid: "t = id"
  proof (rule ext)
    fix a
    have "(srho UNIV {a} t) a = (cut (\<lambda>_. a) {a}) a" using cuts[of a] by simp
    then show "t a = id a" using t by simp
  qed
  have "csmall (UNIV :: bigring set)" using sec_small[OF t] by (simp add: tid)
  then show False using bigring_not_csmall by blast
qed

theorem afp_scheme_without_gluing:
  "scheme (UNIV :: bigring set) (\<lambda>U. True)
       (sec :: bigring set \<Rightarrow> (bigring \<Rightarrow> bigring) set)
       srho (\<lambda>x. undefined) sadd smul szero sone (UNIV :: bigring set)
   \<and> \<Union>(range (\<lambda>a::bigring. {a})) = UNIV
   \<and> (\<forall>a::bigring. cut (\<lambda>_. a) {a} \<in> sec {a})
   \<and> (\<forall>a b::bigring.
       srho {a} ({a} \<inter> {b}) (cut (\<lambda>_. a) {a}) =
       srho {b} ({a} \<inter> {b}) (cut (\<lambda>_. b) {b}))
   \<and> \<not> (\<exists>t \<in> (sec UNIV :: (bigring \<Rightarrow> bigring) set).
       \<forall>a. srho UNIV {a} t = cut (\<lambda>_. a) {a})"
proof (intro conjI allI)
  show "scheme (UNIV :: bigring set) (\<lambda>U. True)
       (sec :: bigring set \<Rightarrow> (bigring \<Rightarrow> bigring) set)
       srho (\<lambda>x. undefined) sadd smul szero sone (UNIV :: bigring set)"
    by (rule bounded_bigring_scheme)
  show "\<Union>(range (\<lambda>a::bigring. {a})) = UNIV" by auto
  show "cut (\<lambda>_. a) {a} \<in> sec {a}" for a :: bigring by (rule singleton_section)
  show "srho {a} ({a} \<inter> {b}) (cut (\<lambda>_. a) {a}) =
       srho {b} ({a} \<inter> {b}) (cut (\<lambda>_. b) {b})" for a b :: bigring
    by (rule singleton_sections_compatible)
  show "\<not> (\<exists>t \<in> (sec UNIV :: (bigring \<Rightarrow> bigring) set).
       \<forall>a. srho UNIV {a} t = cut (\<lambda>_. a) {a})"
    by (rule bigring_singleton_family_has_no_gluing)
qed

end
