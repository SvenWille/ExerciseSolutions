theory Ex1_2 
imports Main 
begin 



primrec replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
"replace _  _ [] = []"|
"replace x  y (z # zs) = (if z = y then x else z) # replace x y zs"

theorem helper : "replace x y (ls @ xs) = replace x y ls @ replace x y xs"
proof (induct ls)
  case Nil 
  show ?case by simp
 next 
  fix a ls 
  assume "replace x y (ls @ xs) = replace x y ls @ replace x y xs"
  thus "replace x y ((a # ls) @ xs) = replace x y (a # ls) @ replace x y xs " by simp
qed

theorem "rev(replace x y zs) = replace x y (rev zs)"
proof (induct zs)
  case Nil 
  show ?case by simp
 next 
  fix a zs 
  assume "rev (replace x y zs) = replace x y (rev zs)"
  thus " rev (replace x y (a # zs)) = replace x y (rev (a # zs)) " by (simp add : helper)
qed


  
  

