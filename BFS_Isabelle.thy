theory BFS_Isabelle

imports Simpl.Vcg Simpl.HeapList

begin

type_synonym path = "ref list"

abbreviation inn (infixl "\<in>:" 45) where
  "inn x xs \<equiv> x \<in> set xs"

subsection \<open>Defining BFS\<close>

record globals_heap =
  value_' :: "ref \<Rightarrow> int"
  nexts_' :: "ref \<Rightarrow> ref list"

record 'g vars = "'g state" +
  nodes_' :: "ref set"
  root_' :: ref
  r_' :: "ref set"
  visited_' :: "ref set"
  q_' :: "ref list"
  p0_' :: path
  a_' :: ref
  i_' :: nat
  neighbors_' :: "ref list"
  neighbors_len_' :: nat

value "length []"

procedures
  bfs(nodes,root|r) = 
"
\<acute>visited :== {\<acute>root};;
\<acute>q :== [\<acute>root];;
WHILE \<acute>q \<noteq> [] DO
  \<acute>a :== hd \<acute>q;;
  \<acute>q :== tl \<acute>q;;
  \<acute>neighbors :== \<acute>nexts (\<acute>a);;
  \<acute>neighbors_len :== length \<acute>neighbors;;
  \<acute>i :== 0;;
  WHILE \<acute>i < \<acute>neighbors_len DO
    IF \<not>(\<acute>neighbors!\<acute>i \<in> \<acute>visited) THEN
      \<acute>visited :== \<acute>visited \<union> {\<acute>neighbors!\<acute>i};;
      \<acute>q :== \<acute>q @ [\<acute>neighbors!\<acute>i]
    FI;;
    \<acute>i :== \<acute>i + 1
  OD
OD;;
\<acute>r :== \<acute>visited
"

procedures
  bfss(nodes) = 
"SKIP"

type_synonym graph = "globals_heap \<times> ref set \<times> ref" (* hea map, nodes, root *)

fun valid_path :: "graph \<Rightarrow> path \<Rightarrow> ref \<Rightarrow> ref \<Rightarrow> bool" where
  "valid_path (heap, nodes, root) [] from to = (from = to)"
| "valid_path (heap, nodes, root) (r#subpath) from to = 
    (from = r
    \<and> (subpath = [] \<longrightarrow> to \<in> set (nexts_' heap r)) 
    \<and> (subpath \<noteq> [] \<longrightarrow> (\<exists>x. x \<in> set (nexts_' heap r) 
        \<and> valid_path (heap, nodes, root) subpath x to)))"

fun valid_path2 :: "graph \<Rightarrow> path \<Rightarrow> ref \<Rightarrow> ref \<Rightarrow> bool" where
  "valid_path2 _ [] _ _ = False"
| "valid_path2 (heap, nodes, root) [a] from to = (from = a \<and> to = a)"
| "valid_path2 (heap, nodes, root) (u#v#subpath) from to = 
    (from = u \<and> v \<in> set (nexts_' heap u) \<and> valid_path2 (heap, nodes, root) (v#subpath) v to)"

fun reachable :: "graph \<Rightarrow> ref \<Rightarrow> ref \<Rightarrow> bool" where
"reachable (heap, nodes, root) from to = (\<exists>p. valid_path2 (heap, nodes, root) p from to)"

fun bfs_pre :: "graph \<Rightarrow> bool" where
"bfs_pre (heap, nodes, root) = (root \<in> nodes \<and> 
  (\<forall>(n::ref) (x::ref). n \<in> nodes \<and> x \<in>: (nexts_' heap) n \<longrightarrow> x \<in> nodes))"

(* Define postcondition *)
                               
fun visited_is_reachable :: "graph \<Rightarrow> ref set \<Rightarrow> bool" where
"visited_is_reachable (heap, nodes, root) visited = (\<forall>n. n \<in> visited 
  \<longrightarrow> reachable (heap, nodes, root) root n)"

fun reach_closed :: "graph \<Rightarrow> ref set \<Rightarrow> bool" where
"reach_closed (heap,nodes,root) visited =
   (\<forall>n\<in>nodes. reachable (heap,nodes,root) root n \<longrightarrow> n \<in> visited)"

definition bfs_post :: "graph \<Rightarrow> ref set \<Rightarrow> bool" where
  "bfs_post g visited \<equiv> visited_is_reachable g visited \<and> reach_closed g visited"

lemma valid_path_step:
  assumes "x \<in> set (nexts_' heap u)"
  shows   "valid_path2 (heap,nodes,root) [u, x] u x"
  using assms by auto

lemma valid_path_append_last:
  assumes "valid_path2 (heap,nodes,root) p s u"
      and "valid_path2 (heap,nodes,root) [u, x] u x"
  shows   "valid_path2 (heap,nodes,root) (p @ [x]) s x"
  using assms
proof (induction p arbitrary: s)
  case Nil
  then show ?case by auto
next
  case (Cons a p)
  then show ?case
    using valid_path2.elims(2) by force
qed

lemma reachable_step:
  assumes "x \<in> set (nexts_' heap u)"
      and "reachable (heap,nodes,root) root u"
  shows   "reachable (heap,nodes,root) root x"
proof -
  obtain p where "valid_path2 (heap,nodes,root) p root u"
    using assms(2) by auto
  hence "valid_path2 (heap,nodes,root) (p @ [x]) root x"
    using valid_path_step[OF assms(1)] valid_path_append_last by blast
  thus ?thesis by auto
qed

lemma set_nexts_subset:
  assumes CLOSE: "\<forall>n x. n \<in> nodes \<and> x \<in> set (nexts_' heap n) \<longrightarrow> x \<in> nodes"
      and A: "a \<in> nodes"
  shows "set (nexts_' heap a) \<subseteq> nodes"
  using CLOSE A by auto


lemma bfs_invariant_step:
  fixes nexts nodes root visited q
  assumes "visited \<subseteq> nodes" and "set q \<subseteq> visited" and "\<forall>x\<in>nodes. set (nexts x) \<subseteq> nodes" and
  "Ball visited (reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) root)" and 
"\<forall>n\<in>nodes.
           reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) root n \<longrightarrow>
           n \<in> visited \<or>
           (\<exists>u\<in>set q.
               reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) root u \<and> reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) u n)" and
"q \<noteq> []"
shows "\<forall>n\<in>nodes.
              reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) root n \<longrightarrow>
              n \<in> visited \<or>
              (\<exists>u\<in>set (tl q) \<union> set (drop 0 (nexts (hd q))).
                  reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) root u \<and> reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) u n)"
proof -
  {fix n
  assume NOES: "n \<in> nodes"
  assume REACH: "reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) root n"
  assume VISITED: "n \<notin> visited"
  obtain u where "u\<in>set q \<and>
               reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) root u \<and> reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) u n"
    using NOES REACH VISITED assms(5) by blast
  then obtain p where "valid_path2 (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) p u n"
    by fastforce
  have "(\<exists>u\<in>set (tl q) \<union> set (drop 0 (nexts (hd q))).
                 reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) root u \<and> reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) u n)"
  proof -
    from \<open>u\<in>set q \<and>
       reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) root u \<and>
       reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) u n\<close>
    have  UinQ: "u \<in> set q" 
      and Uroot: "reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) root u"
      and Uun:   "reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) u n"
      by auto
    obtain a qs where Q: "q = a # qs"
      using assms(6) list.exhaust_sel by blast
    have Cases: "u = a \<or> u \<in> set qs"
      using Q UinQ by auto
    show ?thesis
    proof (cases "u = a")
      case False
      then have "u \<in> set qs"
        using Cases by blast
      hence "u \<in> set (tl q)"
        using Q by auto
      thus ?thesis
        using Uroot Uun by blast
    next
      case True
      hence UA: "u = a"
        by simp
      have AinVisited: "a \<in> visited"
        using UA UinQ assms(2) by blast
      have Aroot: "reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) root a"
        using UA Uroot by auto
      from \<open>valid_path2 (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) p u n\<close> UA
      have P: "valid_path2 (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) p a n"
        by auto
      have "p \<noteq> [a]"
      proof
        assume "p = [a]"
        with P have "n = a"
          by simp
        then show False
          using AinVisited VISITED by auto
      qed
      then obtain v sub where Pv:"p = a # v # sub"
        using UA \<open>valid_path2 (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) p u n\<close>
          valid_path2.elims(2) by blast
      from P Pv 
      have V_in:"v \<in> set (nexts a)"
           and V_path: "valid_path2 (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) (v # sub) v n"
        by auto
      have Vroot: "reachable (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) root v"
        using Aroot V_in reachable_step by auto
      have "v \<in> set (drop 0 (nexts (hd q)))"
        using Q V_in by auto
      thus ?thesis
        using V_path Vroot by auto
    qed
  qed
}
  thus ?thesis by blast
qed

lemma visited_closed:
  assumes "\<forall>n c. n \<in> visited \<and> c \<in>: nexts n \<longrightarrow> c \<in> visited"
      and "s \<in> visited"
      and "valid_path2 (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) p s n"
    shows "n \<in> visited"
  using assms(2-3)
proof (induction p arbitrary: s n)
  case Nil
  then show ?case
    by simp
next
  case (Cons a p)
  then show ?case
  proof (cases p)
    case Nil
    then show ?thesis 
      using Cons.prems(1,2) by auto
  next
    case (Cons b ps)
    from Cons.prems Cons have "s = a"
      and "b \<in>: nexts s"
      and "valid_path2 (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) (b # ps) b n"
      using Cons by auto
    have "b \<in> visited" 
      using Cons.prems(1) \<open>b \<in>: nexts s\<close> assms(1) by blast
    have "n \<in> visited"
      using Cons.IH \<open>b \<in> visited\<close>
        \<open>valid_path2 (\<lparr>value_' = value, nexts_' = nexts\<rparr>, nodes, root) (b # ps) b n\<close> local.Cons
      by blast
    then show ?thesis 
      by auto
  qed
qed


context bfs_impl
begin

lemma bfs_reachability:
(*  assumes  "bfs_pre (heap,nodes,root)" *)
  shows "\<Gamma>\<turnstile> \<lbrace> bfs_pre (\<lparr>value_' = \<acute>value, nexts_' = \<acute>nexts\<rparr>, \<acute>nodes, \<acute>root) \<rbrace>
        \<acute>r :== PROC bfs(\<acute>nodes,\<acute>root)
         \<lbrace>bfs_post (\<lparr>value_' = \<acute>value, nexts_' = \<acute>nexts\<rparr>,\<acute>nodes,\<acute>root) \<acute>r\<rbrace>"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (hoare_rule anno =
"
\<acute>visited :== {\<acute>root};;
\<acute>q :== [\<acute>root];;
WHILE \<acute>q \<noteq> []
  INV \<lbrace> \<acute>visited \<subseteq> \<acute>nodes \<and> set \<acute>q  \<subseteq> \<acute>visited \<and> (\<forall>x\<in>\<acute>nodes. set (\<acute>nexts (x)) \<subseteq> \<acute>nodes) \<and> 
       (\<forall>v \<in> \<acute>visited. reachable (\<lparr>value_' = \<acute>value, nexts_' = \<acute>nexts\<rparr>,\<acute>nodes,\<acute>root) \<acute>root v) \<and> 
       (\<forall>n c. ( n\<in>\<acute>visited \<and> c\<in>:(\<acute>nexts n)) \<longrightarrow>(c\<in>\<acute>visited \<or> n\<in>:\<acute>q)) \<and> \<acute>root \<in> \<acute>visited
       \<rbrace>
DO
  \<acute>a :== hd \<acute>q;;
  \<acute>q :== tl \<acute>q;;
  \<acute>neighbors :== \<acute>nexts (\<acute>a);;
  \<acute>neighbors_len :== length \<acute>neighbors;;
  \<acute>i :== 0;;
  WHILE \<acute>i < \<acute>neighbors_len
    INV \<lbrace> \<acute>visited \<subseteq> \<acute>nodes \<and> set \<acute>q  \<subseteq> \<acute>visited \<and> (\<forall>x\<in>\<acute>nodes. set (\<acute>nexts (x)) \<subseteq> \<acute>nodes) \<and> 
       (\<forall>v \<in> \<acute>visited. reachable (\<lparr>value_' = \<acute>value, nexts_' = \<acute>nexts\<rparr>,\<acute>nodes,\<acute>root) \<acute>root v) \<and> 
     \<acute>neighbors = \<acute>nexts (\<acute>a) \<and>
     \<acute>a \<in> \<acute>visited \<and>
     \<acute>neighbors_len = length (\<acute>neighbors) \<and>
     set (\<acute>neighbors) \<subseteq> \<acute>nodes \<and>
     0 \<le> \<acute>i \<and> \<acute>i \<le> \<acute>neighbors_len \<and>
     (\<forall>n c. (n\<in>\<acute>visited \<and> n\<noteq>\<acute>a \<and> c\<in>:(\<acute>nexts n)) \<longrightarrow> (c\<in>\<acute>visited \<or> n\<in>:\<acute>q))
     \<and> (\<forall>n. n \<in>: take \<acute>i \<acute>neighbors \<longrightarrow> n \<in> \<acute>visited) \<and> \<acute>root \<in> \<acute>visited
 \<rbrace>
  DO
    IF \<not>(\<acute>neighbors!\<acute>i \<in> \<acute>visited) THEN
      \<acute>visited :== \<acute>visited \<union> {\<acute>neighbors!\<acute>i};;
      \<acute>q :== \<acute>q @ [\<acute>neighbors!\<acute>i]
    FI;;
    \<acute>i :== \<acute>i + 1
  OD
OD;;
\<acute>r :== \<acute>visited
" in HoarePartial.annotateI
)
  apply vcg
      apply clarsimp
      apply (metis subset_code(1) valid_path2.simps(2))
  apply(intro conjI)
  apply fastforce
  apply (meson list.set_sel(2) subset_code(1))
  apply fastforce
  apply force
  apply fastforce
  apply auto[1]
  apply blast
  apply (metis in_mono list.set_sel(1))
  apply blast
        apply force
       apply (metis list.exhaust_sel set_ConsD)
  apply (metis empty_iff list.set(1) take0)
  apply meson
    apply safe[1]
            apply blast
  using nth_mem apply blast
  apply (metis Un_iff list.set(1) list.simps(15) set_append singletonD subset_code(1))
         apply blast
  apply (metis globals_heap.select_convs(2) nth_mem reachable_step)
       apply linarith
  apply (metis Un_iff set_append)
       apply (meson in_set_conv_decomp)
  apply (metis Cons_nth_drop_Suc One_nat_def Un_iff add.right_neutral add_Suc_right drop_eq_Nil emptyE hd_conv_nth le_antisym list.set(1) nat_less_le
      nth_Cons_0 set_ConsD set_append take_hd_drop)
     apply linarith
  apply clarsimp
  apply (metis Cons_nth_drop_Suc Un_iff append.right_neutral list.discI list.exhaust_sel nth_Cons_0 set_ConsD set_append take_hd_drop)
   apply clarsimp  
  apply metis
  unfolding bfs_post_def
  apply(intro conjI)
  unfolding visited_is_reachable.simps
  apply clarsimp
  unfolding reach_closed.simps
  apply clarsimp
  using visited_closed by blast

end

end

