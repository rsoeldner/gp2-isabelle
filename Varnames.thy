theory Varnames
  imports Main Common
begin



fun fresh :: "string set \<Rightarrow> string \<times> string set" where
"fresh v = (let 
  e = (SOME x. x \<in> v);
  r = v - {e} in (e,r))"

fun zipFresh :: "'a list \<Rightarrow> string set \<Rightarrow> ('a \<times> string) list \<times> string set" where
"zipFresh ts v = 
  foldr (\<lambda>t (l, u). (let (n, u') = fresh u in ((t, n) # l, u'))) ts ([], v)"
(* 
fun splitWith :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<times> 'a list" where
"splitWith t p = foldr (\<lambda>e (l,r). if p e then (e#l,r) else (l, e#r)) t ([],[])"

lemma "splitWith [1,2,3,4,5,6,7,8,9,10] even = ([2,4,6,8,10],[1,3,5,7,9])"
  by simp
 *)
end