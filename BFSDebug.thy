theory BFSDebug

imports Simpl.Vcg Simpl.HeapList

begin

type_synonym path = "ref list"

abbreviation inn (infixl "\<in>:" 45) where
  "inn x xs \<equiv> x \<in> set xs"

record globals_heap =
  value_' :: "ref \<Rightarrow> int"
  nexts_' :: "ref \<Rightarrow> ref list"

type_synonym graph = "globals_heap \<times> ref set \<times> ref"

fun valid_path :: "graph \<Rightarrow> path \<Rightarrow> ref \<Rightarrow> ref \<Rightarrow> bool" where
  "valid_path _ [] _ _ = False"
| "valid_path (heap, nodes, root) [a] from to = (from = a \<and> to = a)"
| "valid_path (heap, nodes, root) (u#v#subpath) from to = 
    (from = u \<and> v \<in> set (nexts_' heap u) \<and> valid_path (heap, nodes, root) (v#subpath) v to)"

fun reachable :: "graph \<Rightarrow> ref \<Rightarrow> ref \<Rightarrow> bool" where
"reachable (heap, nodes, root) from to = (\<exists>p. valid_path (heap, nodes, root) p from to)"

lemma bfs_debug:
  fixes t21_10 :: globals_heap
  fixes t6_10 :: globals_heap
  fixes nodes3_10 :: "ref set"
  fixes root4_10 :: ref
  fixes visited20_10 :: "ref set"
  fixes q16_10 :: "ref list"
  fixes p014_10 :: path
  fixes a15_10 :: ref
  fixes i19_10 :: nat
  fixes neighbors17_10 :: "ref list"
  fixes neighbors_len18_10 :: nat
  fixes visited12_10 :: "ref set"
  fixes q13_10 :: "ref list"
  assumes 1704: "\<not>(length q16_10 > 0)"
  assumes 315: "\<forall>n22_10::ref. \<not>(n22_10 \<in> visited20_10) \<or> (n22_10 \<in> visited20_10)"
  assumes 316: "\<forall>n22_10::ref. n22_10 \<in> visited20_10 \<longrightarrow> n22_10 \<in> nodes3_10"
  assumes 326: "\<forall>k23_10::nat. (k23_10 \<ge> 0) \<or> \<not> (k23_10 \<ge> 0)"
  assumes 333: "\<forall>k23_10::nat. \<not> (k23_10 \<ge> 0 \<and> k23_10 < length q16_10) \<or>  (k23_10 \<ge> 0 \<and> k23_10 < length q16_10)"
  assumes 338: "\<forall>k23_10::nat. k23_10 \<ge> 0 \<and> k23_10 < length q16_10 \<longrightarrow> q16_10 ! k23_10 \<in> visited20_10"
  assumes 360: "\<forall>n24_10::ref. \<not>(n24_10 \<in> visited20_10) \<or> (n24_10 \<in> visited20_10)"
  assumes 366: "\<forall>n24_10::ref. n24_10 \<in> visited20_10 \<longrightarrow> reachable (t21_10,nodes3_10,root4_10) root4_10 n24_10"
  assumes 385: "\<forall>n25_10::ref. \<not>(n25_10 \<in> visited20_10) \<or> (n25_10 \<in> visited20_10)"
  assumes 429: "\<forall>n25_10::ref. \<forall>c26_10::ref. (n25_10 \<in> visited20_10 \<and> reachable (t21_10,nodes3_10,root4_10) n25_10 c26_10)\<longrightarrow> (c26_10 \<in> visited20_10 \<or>
      (\<exists>j27_10::nat. j27_10 < length q16_10 \<and> q16_10 ! j27_10 = n25_10))"
  assumes 431: "root4_10 \<in> visited20_10"
  assumes 442: "\<forall>n28_10::ref. \<not>(n28_10 \<in> visited12_10) \<or> (n28_10 \<in> visited12_10)"
  assumes 446: "\<forall>n28_10::ref. n28_10 \<in> visited12_10 \<longrightarrow> n28_10 \<in> nodes3_10"
  assumes 467: "\<forall>k29_10::nat. k29_10 < length q13_10 \<longrightarrow> q13_10 ! k29_10 \<in> visited12_10"
  assumes 487: "\<forall>n30_10::ref. \<not>(n30_10 \<in> visited12_10) \<or> (n30_10 \<in> visited12_10)"
  assumes 494: "\<forall>n30_10::ref. n30_10 \<in> visited12_10 \<longrightarrow> reachable (t6_10,nodes3_10,root4_10) root4_10 n30_10"
  assumes 556:  "\<forall>n31_10::ref. \<forall>c32_10::ref. (n31_10 \<in> visited12_10 \<and> reachable (t6_10,nodes3_10,root4_10) n31_10 c32_10)\<longrightarrow> (c32_10 \<in> visited12_10 \<or>
      (\<exists>j33_10::nat. j33_10 < length q13_10 \<and> q13_10 ! j33_10 = n31_10))"
  assumes 557: "root4_10 \<in> visited12_10"
  assumes 267: "visited12_10 = {root4_10}"
  assumes 268: "length [root4_10] = 1"
  assumes 269: "q13_10 = [root4_10]"
  assumes 270: "p014_10 = []"
  assumes 297: "reachable (t6_10,nodes3_10,root4_10) root4_10 root4_10"
  shows "\<forall>n130::ref. (n130 \<in> visited20_10 \<longleftrightarrow> reachable (t21_10,nodes3_10,root4_10) root4_10 n130)"
  apply (rule allI)
  apply (rule iffI)
  using "366" apply blast
  using "1704" "429" "431" gr_implies_not0 by blast

(*proof
    fix n130 :: ref
    have len0: "length q16_10 = 0"
      using "1704" by blast
    have "\<not> (\<exists>j::nat. j < length q16_10 \<and> q16_10 ! j = root4_10)"
      by (simp add: len0)
    show "n130 \<in> visited20_10 \<longleftrightarrow> reachable (t21_10,nodes3_10,root4_10) root4_10 n130"
    proof
      assume "n130 \<in> visited20_10"
      thus "reachable (t21_10,nodes3_10,root4_10) root4_10 n130"
        using 366 by blast
    next
      assume R: "reachable (t21_10,nodes3_10,root4_10) root4_10 n130"
      have "n130 \<in> visited20_10 \<or> (\<exists>j::nat. j < length q16_10 \<and> q16_10 ! j = root4_10)"
        using "429" "431" R by blast
      thus "n130 \<in> visited20_10"
        sledgehammer
        using \<open>\<not> (\<exists>j<length q16_10. q16_10 ! j = root4_10)\<close> by blast
    qed
  qed*)


