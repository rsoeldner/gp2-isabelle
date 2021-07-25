theory Varnames
  imports Main Common 
begin

fun fresh :: "nat set \<Rightarrow> nat \<times> nat set" where
"fresh X = (if X = {} then (0, {0}) else (let n = Suc (Max X) in (n, insert n X)))"

(*  lemma a : "\<lbrakk>\<exists>x. P x\<rbrakk> \<Longrightarrow> (LEAST x:: nat. x \<noteq> v \<and> P x) = min v (LEAST x. P x)"
   apply (rule Least_equality)
    apply (simp add: min_def)

   sorry
 *)

(* ma "fresh {0,1,2::nat} = x"
  apply (simp add: fresh_def)
  s *)


(* fun fresh :: "'a :: linorder set \<Rightarrow> 'a \<times> 'a set" where
"fresh V = (let 
  e = (LEAST x. x \<in> V);
  r = V - {e} in (e,r))"
 *)

(* lemma "fresh (UNIV-{0,1,2::nat}) = x"
  apply (simp) *)
(* 

lemma l: "\<lbrakk>\<exists>x. P x\<rbrakk> \<Longrightarrow> (LEAST x:: 'a :: wellorder. x = v \<or> P x) = min v (LEAST x. P x)"
   using [[show_types, show_sorts]]
   apply (rule Least_equality)
    apply (metis LeastI min_def)
   by (meson Least_le min_le_iff_disj order_refl)

lemma l2[simp]: "(LEAST x ::'a :: order. x = v) = v"
  by (simp add: Least_equality)
 *)
(*
lemma "fresh {1::nat,2} = x"
  apply (simp add: Let_def l l2 min_def)
 *)

fun zipFresh :: "'a list \<Rightarrow> nat set \<Rightarrow> ('a \<times> nat) list \<times> nat set" where
"zipFresh ts V = 
  foldr (\<lambda>t (l, u). (let (n, u') = fresh u in ((t, n) # l, u'))) ts ([], V)"

end